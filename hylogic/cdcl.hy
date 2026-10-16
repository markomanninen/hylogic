"A conflict-driven clause learning (CDCL) SAT solver.

DPLL in hylogic.sat guesses, propagates and backtracks one step at a time, and
scans every clause on every step. Modern SAT solvers add four things, all here:

- two watched literals: a clause is looked at only when one of the two
  literals it watches becomes false, so propagation touches few clauses
- clause learning: a conflict is traced back to the decision that caused it,
  and the reason becomes a new clause, so the same dead end is never entered
  twice (the first unique implication point, as in MiniSat)
- backjumping: after a conflict the search jumps back as many levels as the
  learned clause allows, not just one
- VSIDS and restarts: variables involved in recent conflicts are decided
  first, and the search restarts now and then, keeping what it learned

Clauses are lists of nonzero integers in DIMACS style, as in hylogic.sat."

(import heapq
        time)

(defclass _Timeout [Exception])

(defclass Solver []
  (defn __init__ [self clauses [deadline None]]
    (setv self.deadline deadline
          self.nvars (max (gfor c clauses l c (abs l)) :default 0)
          self.assign (* [0] (+ self.nvars 1))
          self.level (* [0] (+ self.nvars 1))
          self.reason (* [None] (+ self.nvars 1))
          self.phase (* [-1] (+ self.nvars 1))
          self.activity (* [0.0] (+ self.nvars 1))
          self.bump 1.0
          self.heap (lfor v (range 1 (+ self.nvars 1)) #(0.0 v))
          self.trail []
          self.limits []
          self.qhead 0
          self.clauses []
          self.watches {}
          self.unsat False)
    (heapq.heapify self.heap)
    (for [c clauses]
      (setv c (list (dict.fromkeys c)))
      (cond
        (any (gfor l c (in (- l) c))) None
        (not c) (setv self.unsat True)
        (= (len c) 1)
          (do
            (setv v (.value self (get c 0)))
            (cond (= v -1) (setv self.unsat True)
                  (= v 0) (.enqueue self (get c 0) None)))
        True (.attach self c))))

  (defn value [self lit]
    (setv v (get self.assign (abs lit)))
    (if (> lit 0) v (- v)))

  (defn attach [self c]
    (.append self.clauses c)
    (setv ci (- (len self.clauses) 1))
    (for [l (cut c 0 2)]
      (.append (.setdefault self.watches l []) ci))
    ci)

  (defn enqueue [self lit reason]
    (setv v (abs lit)
          (get self.assign v) (if (> lit 0) 1 -1)
          (get self.level v) (len self.limits)
          (get self.reason v) reason)
    (.append self.trail lit))

  (defn propagate [self]
    "Unit propagation over the watched literals; the index of a conflicting clause, or None."
    (while (< self.qhead (len self.trail))
      (setv p (get self.trail self.qhead)
            false-lit (- p)
            ws (.get self.watches false-lit [])
            kept []
            i 0)
      (+= self.qhead 1)
      (while (< i (len ws))
        (setv ci (get ws i) c (get self.clauses ci))
        (+= i 1)
        (when (= (get c 0) false-lit)
          (setv (get c 0) (get c 1) (get c 1) false-lit))
        (when (= (.value self (get c 0)) 1)
          (.append kept ci)
          (continue))
        (setv moved False)
        (for [k (range 2 (len c))]
          (when (!= (.value self (get c k)) -1)
            (setv (get c 1) (get c k) (get c k) false-lit)
            (.append (.setdefault self.watches (get c 1) []) ci)
            (setv moved True)
            (break)))
        (when moved (continue))
        (.append kept ci)
        (if (= (.value self (get c 0)) -1)
            (do
              (setv (get self.watches false-lit) (+ kept (cut ws i None))
                    self.qhead (len self.trail))
              (return ci))
            (.enqueue self (get c 0) ci)))
      (setv (get self.watches false-lit) kept))
    None)

  (defn bump-var [self v]
    (+= (get self.activity v) self.bump)
    (when (> (get self.activity v) 1e100)
      (for [u (range 1 (+ self.nvars 1))] (*= (get self.activity u) 1e-100))
      (*= self.bump 1e-100))
    (heapq.heappush self.heap #((- (get self.activity v)) v)))

  (defn analyze [self confl]
    "The first-UIP learned clause and the level to jump back to."
    (setv seen #{} learnt [None] counter 0 p None idx (- (len self.trail) 1)
          clause (get self.clauses confl) current (len self.limits))
    (while True
      (for [q clause]
        (when (and (is-not p None) (= q p)) (continue))
        (setv v (abs q))
        (when (and (not-in v seen) (> (get self.level v) 0))
          (.add seen v)
          (.bump-var self v)
          (if (= (get self.level v) current)
              (+= counter 1)
              (.append learnt q))))
      (while (not-in (abs (get self.trail idx)) seen) (-= idx 1))
      (setv p (get self.trail idx))
      (-= idx 1)
      (.discard seen (abs p))
      (-= counter 1)
      (when (<= counter 0) (break))
      (setv clause (get self.clauses (get self.reason (abs p)))))
    (setv (get learnt 0) (- p))
    (setv back 0)
    (when (> (len learnt) 1)
      ;; the literal from the highest remaining level goes second, as the other watch
      (setv best 1)
      (for [k (range 2 (len learnt))]
        (when (> (get self.level (abs (get learnt k))) (get self.level (abs (get learnt best))))
          (setv best k)))
      (setv [(get learnt 1) (get learnt best)] [(get learnt best) (get learnt 1)]
            back (get self.level (abs (get learnt 1)))))
    (*= self.bump 1.05)
    #(learnt back))

  (defn backtrack [self lvl]
    (when (> (len self.limits) lvl)
      (for [lit (cut self.trail (get self.limits lvl) None)]
        (setv v (abs lit)
              (get self.phase v) (if (> lit 0) 1 -1)
              (get self.assign v) 0
              (get self.reason v) None)
        (heapq.heappush self.heap #((- (get self.activity v)) v)))
      (setv self.trail (cut self.trail 0 (get self.limits lvl))
            self.limits (cut self.limits 0 lvl)
            self.qhead (len self.trail))))

  (defn decide [self]
    "The next decision literal, or None when every variable has a value."
    (while self.heap
      (setv [_ v] (heapq.heappop self.heap))
      (when (= (get self.assign v) 0)
        (return (* v (get self.phase v)))))
    (for [v (range 1 (+ self.nvars 1))]
      (when (= (get self.assign v) 0) (return (* v (get self.phase v)))))
    None)

  (defn add [self c]
    "Add a clause between calls to solve, keeping everything learned so far."
    (.backtrack self 0)
    (setv c (list (dict.fromkeys c)))
    (for [v (range (+ self.nvars 1) (+ (max (gfor l c (abs l)) :default 0) 1))]
      (.append self.assign 0) (.append self.level 0) (.append self.reason None)
      (.append self.phase -1) (.append self.activity 0.0)
      (heapq.heappush self.heap #(0.0 v))
      (setv self.nvars v))
    (when (or (any (gfor l c (in (- l) c))) (any (gfor l c (= (.value self l) 1))))
      (return))
    (setv c (lfor l c :if (= (.value self l) 0) l))
    (cond
      (not c) (setv self.unsat True)
      (= (len c) 1) (.enqueue self (get c 0) None)
      True (.attach self c)))

  (defn solve [self]
    "A model {variable: bool}, or None if the clauses are unsatisfiable."
    (when self.unsat (return None))
    (.backtrack self 0)
    (setv conflicts 0 restart-at 100)
    (while True
      (setv confl (.propagate self))
      (if (is-not confl None)
          (do
            (+= conflicts 1)
            (when (and self.deadline (= (% conflicts 64) 0) (> (time.monotonic) self.deadline))
              (raise (_Timeout)))
            (when (= (len self.limits) 0) (return None))
            (setv [learnt back] (.analyze self confl))
            (.backtrack self back)
            (if (= (len learnt) 1)
                (.enqueue self (get learnt 0) None)
                (.enqueue self (get learnt 0) (.attach self learnt))))
          (do
            (when (>= conflicts restart-at)
              (setv restart-at (int (* restart-at 1.5)))
              (.backtrack self 0))
            (setv lit (.decide self))
            (when (is lit None)
              (return (dfor v (range 1 (+ self.nvars 1)) v (= (get self.assign v) 1))))
            (.append self.limits (len self.trail))
            (.enqueue self lit None))))))

(defn cdcl [clauses [deadline None]]
  "A satisfying assignment {variable: bool}, None if there is none, or the string
  timeout if the deadline (a time.monotonic value) passes first."
  (try
    (.solve (Solver (lfor c clauses (list c)) deadline))
    (except [_Timeout] "timeout")))
