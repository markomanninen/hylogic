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

Clauses are lists of nonzero integers in DIMACS style, as in hylogic.sat.

Every learned clause is the result of resolution steps: the conflict clause
resolved with the reasons of the literals analyze walks back over. The solver
records those steps, so when it finds the clauses unsatisfiable, `refutation`
can replay them into a resolution proof of the empty clause."

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
          self.origin []
          self.pos (* [0] (+ self.nvars 1))
          self.final None
          self.unsat False)
    (heapq.heapify self.heap)
    (for [[k c] (enumerate clauses)]
      (setv c (list (dict.fromkeys c)))
      (cond
        (any (gfor l c (in (- l) c))) None
        (not c) (do (setv self.unsat True)
                    (when (is self.final None) (setv self.final (.store self c #("input" k)))))
        (= (len c) 1)
          (do
            (setv ci (.store self c #("input" k)) v (.value self (get c 0)))
            (cond (= v -1) (do (setv self.unsat True)
                               (when (is self.final None) (setv self.final ci)))
                  (= v 0) (.enqueue self (get c 0) ci)))
        True (.attach self c #("input" k)))))

  (defn store [self c origin]
    "Keep a clause without watching it (a unit, or an empty clause)."
    (.append self.clauses c)
    (.append self.origin origin)
    (- (len self.clauses) 1))

  (defn value [self lit]
    (setv v (get self.assign (abs lit)))
    (if (> lit 0) v (- v)))

  (defn attach [self c [origin None]]
    (setv ci (.store self c origin))
    (for [l (cut c 0 2)]
      (.append (.setdefault self.watches l []) ci))
    ci)

  (defn enqueue [self lit reason]
    (setv v (abs lit)
          (get self.assign v) (if (> lit 0) 1 -1)
          (get self.level v) (len self.limits)
          (get self.reason v) reason
          (get self.pos v) (len self.trail))
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
          clause (get self.clauses confl) current (len self.limits) chain [])
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
      (.append chain #((get self.reason (abs p)) (abs p)))
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
    #(learnt back #("learned" confl chain)))

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
      (.append self.phase -1) (.append self.activity 0.0) (.append self.pos 0)
      (heapq.heappush self.heap #(0.0 v))
      (setv self.nvars v))
    (when (or (any (gfor l c (in (- l) c))) (any (gfor l c (= (.value self l) 1))))
      (return))
    (setv c (lfor l c :if (= (.value self l) 0) l))
    (cond
      (not c) (setv self.unsat True)
      (= (len c) 1) (.enqueue self (get c 0) (.store self c #("added" None)))
      True (.attach self c #("added" None))))

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
            (when (= (len self.limits) 0)
              (setv self.final confl)
              (return None))
            (setv [learnt back origin] (.analyze self confl))
            (.backtrack self back)
            (if (= (len learnt) 1)
                (.enqueue self (get learnt 0) (.store self learnt origin))
                (.enqueue self (get learnt 0) (.attach self learnt origin))))
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

(defn refutation [solver]
  "After solve found the clauses unsatisfiable: the resolution proof it made, as
  #(steps root). steps maps a node to #(literals parents), where parents is
  #(k) for input clause k, or the two nodes resolved; root is the empty clause.
  A learned clause is replayed from the steps analyze recorded, and the
  literals it dropped because they were false at level 0 are resolved away
  with their (permanent) level-0 reasons, latest first."
  (setv steps {} done {} fresh (iter (range (len solver.clauses) 10000000000)))
  (defn resolve [a b v]
    "The resolvent of nodes a and b on variable v, as a new node."
    (setv lits (frozenset (gfor l (| (get (get steps a) 0) (get (get steps b) 0)) :if (!= (abs l) v) l))
          node (next fresh))
    (setv (get steps node) #(lits #(a b)))
    node)
  (defn eliminate [node target]
    "Resolve away the literals of node outside target with level-0 reasons."
    (while True
      (setv extra (lfor l (get (get steps node) 0) :if (not-in l target) l))
      (when (not extra) (return node))
      (setv v (max (gfor l extra (abs l)) :key (fn [v] (get solver.pos v)))
            node (resolve node (build (get solver.reason v)) v))))
  (defn build [ci]
    (when (in ci done) (return (get done ci)))
    (setv origin (get solver.origin ci))
    (if (= (get origin 0) "learned")
        (do
          (setv [_ confl chain] origin node (build confl))
          (for [[r v] chain] (setv node (resolve node (build r) v)))
          (setv node (eliminate node (frozenset (get solver.clauses ci)))))
        (do
          (setv node ci)
          (setv (get steps ci) #((frozenset (get solver.clauses ci)) #((get origin 1))))))
    (setv (get done ci) node)
    node)
  (setv root (eliminate (build solver.final) (frozenset)))
  #(steps root))
