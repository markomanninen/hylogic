"Reading TPTP problems, and a command line that answers like the provers do.

TPTP (Thousands of Problems for Theorem Provers) is the standard problem
library and input language for first-order provers. This module reads its
first-order form (FOF) into HyLogic formulas:

  fof(name, role, formula).   include('Axioms/SET001+0.ax').

Variables start with a capital letter and stay as they are; HyLogic's
quantifiers bind them. Equality is the predicate =. A name that HyLogic
would read as a connective (or, not, ...) gets a trailing underscore.

  python -m hylogic.tptp PROBLEM.p [--time-limit 10]

prints an SZS status line, the TPTP standard for prover results:
Theorem, CounterSatisfiable, Unsatisfiable, Satisfiable, GaveUp or Timeout."

(import re
        os
        sys
        time
        pathlib [Path]
        hylogic.formulas [OPERATORS CONSTANTS])

(setv TOKEN (re.compile #[[(?x)
  (?P<skip> \s+ | %[^\n]* | /\*.*?\*/ )
  | (?P<op> <=> | <~> | => | <= | ~\| | ~& | != | [&|~!?:,()\[\].=] )
  | (?P<single> '(?:[^'\\]|\\.)*' )
  | (?P<distinct> "(?:[^"\\]|\\.)*" )
  | (?P<word> \$\$?\w+ | [A-Za-z_][A-Za-z0-9_]* )
  | (?P<number> [+-]?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?(?:/\d+)? )
  ]] re.S))

(defclass TPTPError [Exception])

(defn tokens [text]
  "The TPTP tokens of a text, as (kind, value) pairs, without comments."
  (setv out [] pos 0)
  (while (< pos (len text))
    (setv m (.match TOKEN text pos))
    (when (not m)
      (raise (TPTPError (+ "cannot read TPTP text at: " (repr (cut text pos (+ pos 40)))))))
    (setv pos (.end m) kind m.lastgroup)
    (when (!= kind "skip")
      (.append out #(kind (.group m kind)))))
  out)

(defn _name [word]
  "A TPTP name as a HyLogic name, kept clear of connective and constant names."
  (when (.startswith word "'") (setv word (.replace (cut word 1 -1) "\\'" "'")))
  (if (or (in word OPERATORS) (in word CONSTANTS)) (+ word "_") word))

(defclass Parser []
  (defn __init__ [self toks]
    (setv self.toks toks self.i 0))

  (defn peek [self [ahead 0]]
    (if (< (+ self.i ahead) (len self.toks)) (get self.toks (+ self.i ahead)) #(None None)))

  (defn take [self [value None]]
    (setv tok (.peek self))
    (when (and value (!= (get tok 1) value))
      (raise (TPTPError (+ "expected " (repr value) ", found " (repr (get tok 1))))))
    (+= self.i 1)
    tok)

  (defn at [self #* values] (in (get (.peek self) 1) values))

  (defn term [self]
    (setv [kind value] (.take self))
    (cond
      (= kind "distinct") value
      (= kind "number") value
      (and (= kind "word") (get value 0) (.isupper (get value 0))) value      ; variable
      (in kind #{"word" "single"})
        (do
          (setv name (_name value))
          (if (.at self "(")
              (do
                (.take self "(")
                (setv args [(.term self)])
                (while (.at self ",") (.take self ",") (.append args (.term self)))
                (.take self ")")
                #(name #* args))
              name))
      True (raise (TPTPError (+ "expected a term, found " (repr value))))))

  (defn atomic [self]
    (setv [kind value] (.peek self))
    (cond
      (= value "$true") (do (.take self) "true")
      (= value "$false") (do (.take self) "false")
      True
        (do
          (setv left (.term self))
          (cond
            (.at self "=") (do (.take self) #("=" left (.term self)))
            (.at self "!=") (do (.take self) #("not" #("=" left (.term self))))
            True left))))

  (defn unitary [self]
    (cond
      (.at self "(") (do (.take self "(") (setv f (.logic self)) (.take self ")") f)
      (.at self "~") (do (.take self) #("not" (.unitary self)))
      (.at self "!" "?")
        (do
          (setv q (if (= (get (.take self) 1) "!") "forall" "exists"))
          (.take self "[")
          (setv names [(get (.take self) 1)])
          (while (.at self ",") (.take self ",") (.append names (get (.take self) 1)))
          (.take self "]")
          (.take self ":")
          #(q (tuple names) (.unitary self)))
      True (.atomic self)))

  (defn logic [self]
    (setv first (.unitary self))
    (setv op (get (.peek self) 1))
    (cond
      (in op #{"&" "|"})
        (do
          (setv parts [first])
          (while (.at self op) (.take self) (.append parts (.unitary self)))
          #((if (= op "&") "and" "or") #* parts))
      (in op #{"<=>" "=>" "<=" "<~>" "~|" "~&"})
        (do
          (.take self)
          (setv second (.unitary self))
          (get {"<=>" #("<=>" first second) "=>" #("=>" first second) "<=" #("=>" second first)
                "<~>" #("not" #("<=>" first second)) "~|" #("not" #("or" first second))
                "~&" #("not" #("and" first second))} op))
      True first)))

(defclass Problem []
  "Premises, the conjecture (None when the problem has none) and the header facts."
  (defn __init__ [self name premises conjecture status]
    (setv self.name name self.premises premises self.conjecture conjecture self.status status))
  (defn [property] goal [self]
    (if (is self.conjecture None) "false" self.conjecture))
  (defn [property] has-equality [self]
    (_mentions-equality [#* self.premises self.goal])))

(defn _mentions-equality [x]
  (cond
    (isinstance x tuple) (or (and x (= (get x 0) "=")) (any (gfor y x (_mentions-equality y))))
    (isinstance x list) (any (gfor y x (_mentions-equality y)))
    True False))

(defn _tptp-root [path]
  (setv env (os.environ.get "TPTP"))
  (if env (Path env) (. (Path path) parent parent parent)))

(defn _read-formulas [path root selection premises conjectures]
  (setv p (Parser (tokens (.read-text (Path path) :encoding "utf-8" :errors "replace"))))
  (while (is-not (get (.peek p) 0) None)
    (setv [_ kind] (.take p))
    (.take p "(")
    (cond
      (= kind "include")
        (do
          (setv file (cut (get (.take p) 1) 1 -1)
                names None)
          (when (.at p ",")
            (.take p ",") (.take p "[")
            (setv names #{})
            (while (not (.at p "]"))
              (.add names (get (.take p) 1))
              (when (.at p ",") (.take p ",")))
            (.take p "]"))
          (.take p ")") (.take p ".")
          (_read-formulas (/ root file) root names premises conjectures))
      (in kind #{"fof" "cnf"})
        (do
          (setv name (get (.take p) 1))
          (.take p ",")
          (setv role (get (.take p) 1))
          (.take p ",")
          (setv f (.logic p))
          ;; skip annotations
          (setv depth 0)
          (while (or (> depth 0) (not (.at p ")")))
            (setv v (get (.take p) 1))
            (cond (in v #{"(" "["}) (+= depth 1) (in v #{")" "]"}) (-= depth 1)))
          (.take p ")") (.take p ".")
          (when (= kind "cnf") (setv f (_close f)))
          (when (or (is selection None) (in name selection))
            (cond
              (= role "conjecture") (.append conjectures f)
              (= role "type") None
              True (.append premises f))))
      True (raise (TPTPError f"{kind} formulas are not supported, only fof and cnf")))))

(defn _variables [x found]
  (cond
    (and (isinstance x str) x (.isupper (get x 0))) (when (not-in x found) (.append found x))
    (isinstance x tuple) (for [y (cut x (if (and x (isinstance (get x 0) str)) 1 0) None)] (_variables y found)))
  found)

(defn _close [f]
  "A cnf clause with its free variables bound by forall."
  (setv vs (_variables f []))
  (if vs #("forall" (tuple vs) f) f))

(defn _status [path]
  (setv m (re.search r"% Status\s*:\s*(\w+)" (.read-text (Path path) :encoding "utf-8" :errors "replace")))
  (if m (.group m 1) None))

(defn _distinct-objects [x [found None]]
  "The distinct objects (double-quoted names) occurring in formulas."
  (when (is found None) (setv found #{}))
  (cond
    (and (isinstance x str) (.startswith x "\"")) (.add found x)
    (isinstance x #(tuple list)) (for [y x] (_distinct-objects y found)))
  found)

(defn read-problem [path]
  "A TPTP problem file as a Problem, with its includes read from the TPTP root."
  (setv premises [] conjectures [])
  (_read-formulas path (_tptp-root path) None premises conjectures)
  (when (> (len conjectures) 1)
    (raise (TPTPError "more than one conjecture")))
  ;; distinct objects such as "Apple" denote pairwise different elements in
  ;; TPTP; saying so as premises lets every method below know it
  (setv objects (sorted (_distinct-objects [#* premises #* conjectures])))
  (for [[i a] (enumerate objects)  b (cut objects (+ i 1) None)]
    (.append premises #("not" #("=" a b))))
  (Problem (. (Path path) stem) premises (if conjectures (get conjectures 0) None) (_status path)))

(defn szs-status [problem result-status countermodel [equality-built-in False]]
  "The SZS status for a prover result. equality-built-in says whether the search knew
  what = means (equality axioms or superposition), so that saturation is meaningful."
  (setv conj (is-not problem.conjecture None))
  (cond
    (= result-status "proved") (if conj "Theorem" "Unsatisfiable")
    countermodel (if conj "CounterSatisfiable" "Satisfiable")
    ;; saturation shows satisfiability only when = means nothing special
    (and (= result-status "saturated") (or equality-built-in (not problem.has-equality)))
      (if conj "CounterSatisfiable" "Satisfiable")
    (= result-status "timeout") "Timeout"
    True "GaveUp"))

(setv SCHEDULE
  ;; strategies a portfolio can run after the main search, as option changes
  {"plain" {}
   "unordered" {"ordered" 0}
   "no_goal_bias" {"goal_bias" 2 "age_ratio" 3}
   "fifo" {"age_ratio" 1}})

(defn solve [path [time-limit 10.0] [limit 1000000] [equality 0] [epr 0] #** options]
  "Read and attempt a TPTP problem. Returns the SZS status and the result.
  equality 1 adds the equality axioms when the problem uses =, and equality 2
  builds equality into the search with superposition. Superposition here may
  be incomplete, so its saturation is not taken as a CounterSatisfiable answer."
  (import hylogic.resolution [prove clausify]
          hylogic.models [find-model]
          hylogic.equality [equality-axioms])
  (setv started (time.monotonic)
        problem (read-problem path))
  ;; effectively propositional problems are decided exactly by grounding and SAT
  (when epr
    (import hylogic.resolution [clausify Result]
            hylogic.grounding [decide-epr epr-refutation])
    (import hylogic.ground [decide-ground]
            hylogic.euf [decide-euf-with-proof])
    (setv definitional (.get options "definitional" False)
          goal-clauses (clausify #("not" problem.goal) definitional)
          clauses [#* (gfor f problem.premises  c (clausify f definitional) c) #* goal-clauses]
          epr-verdict (decide-epr clauses :deadline (+ started (* 0.25 time-limit)))
          ;; ground problems with functions: exactly by congruence closure,
          ;; then by a bounded search for finite models
          [euf-verdict euf-proof] (if epr-verdict
                                      #(None None)
                                      (decide-euf-with-proof clauses (set goal-clauses)
                                                             :deadline (+ started (* 0.75 time-limit))))
          verdict (or epr-verdict euf-verdict
                      (decide-ground clauses :deadline (+ started (* 0.8 time-limit)))))
    (when verdict
      ;; a SAT answer comes with a readable proof: the solver's resolution steps
      ;; over ground instances (EPR) or over equality lemmas (congruence closure)
      (setv result (cond
                     (= epr-verdict "proved")
                       (epr-refutation clauses (set goal-clauses) :deadline (+ started (* 0.95 time-limit)))
                     euf-proof euf-proof))
      (return #((szs-status problem verdict None True)
                (or result (Result verdict None {"kept" 0 "generated" 0})) problem))))
  ;; a short model search first: small countermodels are cheap, and the search
  ;; at the end gets only what resolution leaves
  (when (.get options "finder_first" 0)
    (import hylogic.resolution [clausify Result]
            hylogic.finite [find-finite-model distinct-constants])
    (setv clauses (lfor f [#* problem.premises #("not" problem.goal)]
                        c (clausify f (.get options "definitional" False)) c)
          found (find-finite-model clauses :max-size 4 :fixed-constants (distinct-constants clauses)
                                   :deadline (+ (time.monotonic) (* (/ (get options "finder_first") 100) time-limit))))
    (when (isinstance found tuple)
      (return #((szs-status problem "saturated" True (= equality 1))
                (Result "saturated" None {"kept" 0 "generated" 0}) problem))))
  (setv problem problem
        axioms (if (and (= equality 1) problem.has-equality)
                   [#* problem.premises #* (equality-axioms [#* problem.premises problem.goal])]
                   problem.premises)
        search-options (dfor [k v] (.items options) :if (not-in k #{"superposition" "portfolio" "finder_first" "schedule"}) k v)
        budget (- (* 0.8 time-limit) (- (time.monotonic) started))
        main-share (if (.get options "portfolio" 0) (/ (get options "portfolio") 100) 1)
        result (prove problem.goal axioms :limit limit
                      :timeout (max 0.5 (* main-share budget))
                      :superposition (if (= equality 2) 1 (.get options "superposition" 0))
                      #** search-options)
        model None)
  ;; portfolio: if the main search fails, the strategies in "schedule" share the
  ;; rest of the search time; each finds proofs the others prune away
  ;; (benchmarks/tptp/strategies.py measured which)
  (when (and (.get options "portfolio" 0) (not result.proved) (!= result.status "saturated"))
    (setv names (.split (.get options "schedule" "plain") "+"))
    (for [[i name] (enumerate names)]
      (setv rest (- (* 0.8 time-limit) (- (time.monotonic) started)))
      (when (< rest 0.5) (break))
      (setv share (/ rest (- (len names) i))
            strategy (get SCHEDULE name)
            second (if (= name "plain")
                       (prove problem.goal axioms :limit limit :timeout share
                              :age-ratio (.get options "age_ratio" 10)
                              :definitional (.get options "definitional" False))
                       (prove problem.goal axioms :limit limit :timeout share
                              :superposition (if (= equality 2) 1 0)
                              #** (| search-options strategy))))
      (when (or second.proved (and (= second.status "saturated") (not problem.has-equality)))
        (setv result second)
        (break))))
  ;; the two model finders find different countermodels (benchmarks/tptp):
  ;; enumerating function tables, then flattening into SAT; they share the rest
  (when (not result.proved)
    (import hylogic.finite [find-finite-model distinct-constants])
    (setv remaining (- time-limit (- (time.monotonic) started) 0.3))
    (when (> remaining 0.4)
      (setv model (find-model [#* problem.premises #("not" problem.goal)] :max-size 3
                              :deadline (+ (time.monotonic) (/ remaining 2))))
      (when (not model)
        (setv clauses (lfor f [#* problem.premises #("not" problem.goal)]
                            c (clausify f (.get options "definitional" False)) c)
              found (find-finite-model clauses :max-size 6 :fixed-constants (distinct-constants clauses)
                                       :deadline (- (+ started time-limit) 0.3))
              model (isinstance found tuple)))))
  #((szs-status problem result.status model (= equality 1)) result problem))

(defn main [[argv None]]
  ;; the best combination measured in benchmarks/tptp; --set overrides each
  (setv args (list (or argv (cut sys.argv 1 None)))
        time-limit 10.0
        options {"age_ratio" 10 "equality" 2 "ordered" 1 "index" 1 "definitional" 8 "epr" 1
                 "goal_bias" 6 "portfolio" 40 "schedule" "unordered"
                 "finder_first" 30})
  ;; --set name=value passes a search option to prove, for experiments
  (while (in "--set" args)
    (setv i (.index args "--set")
          [k v] (.split (get args (+ i 1)) "=" 1)
          ;; numbers for most options, names for schedule (such as unordered+fifo)
          (get options (hy.mangle k)) (if (.isdigit v) (int v) v))
    (del (cut args i (+ i 2))))
  (when (in "--time-limit" args)
    (setv i (.index args "--time-limit")
          time-limit (float (get args (+ i 1))))
    (del (cut args i (+ i 2))))
  (for [path args]
    (setv name (. (Path path) stem))
    (try
      (setv [status result _] (solve path :time-limit time-limit #** options))
      (except [e TPTPError]
        (print f"% SZS status Inappropriate for {name}: {e}")
        (continue)))
    (print f"% SZS status {status} for {name}")
    (when result.proved
      (print f"% SZS output start Proof for {name}")
      (for [line (.proof result)] (print line))
      (print f"% SZS output end Proof for {name}"))
    (sys.stdout.flush)))

(when (= __name__ "__main__")
  (main))
