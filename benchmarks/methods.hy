"Compare the four ways hylogic can decide a propositional question.

Random 3-SAT formulas at the hard ratio of 4.26 clauses per variable, and
pigeonhole problems (n+1 pigeons in n holes, always unsatisfiable, a classic
hard case for resolution). Each method gets a time budget per problem.

  hy benchmarks/methods.hy        (needs z3-solver for the Z3 column)"

(import random time sys signal
        hylogic.truth [satisfiable? :as tt-satisfiable?]
        hylogic.sat [satisfiable]
        hylogic.resolution [saturate Clause clausify]
        hylogic.export [check-with-z3])

(defn random-3sat [rng n]
  (setv names (lfor i (range n) f"x{i}"))
  #("and" #* (gfor _ (range (round (* 4.26 n)))
                   #("or" #* (gfor v (.sample rng names 3)
                                   (if (< (.random rng) 0.5) v #("not" v)))))))

(defn pigeonhole [holes]
  (setv pigeons (+ holes 1) p (fn [i j] f"p{i}h{j}"))
  #("and"
    #* (gfor i (range pigeons) #("or" #* (gfor j (range holes) (p i j))))
    #* (gfor j (range holes) a (range pigeons) b (range (+ a 1) pigeons)
             #("not" #("and" (p a j) (p b j))))))

(setv BUDGET 20)   ; seconds per method and problem

(defn on-alarm [#* _] (raise (TimeoutError)))
(signal.signal signal.SIGALRM on-alarm)

(defn timed [f]
  "Result and milliseconds, or #(\"timeout\" None) after BUDGET seconds."
  (signal.setitimer signal.ITIMER_REAL BUDGET)
  (setv t0 (time.perf-counter))
  (try
    (setv r (f))
    (except [TimeoutError] (return #("timeout" None)))
    (finally (signal.setitimer signal.ITIMER_REAL 0)))
  #(r (* 1000 (- (time.perf-counter) t0))))

(defn by-resolution [formula]
  (setv r (saturate (lfor c (clausify formula) (Clause c)) :limit 20000))
  (cond (= r.status "proved") False (= r.status "saturated") True True None))

(defn by-z3 [formula]
  ;; satisfiable when "formula entails false" is invalid
  (setv v (check-with-z3 [formula] "false"))
  (cond (= v "valid") False (= v "invalid") True True None))

(setv METHODS [#("truth table" (fn [f] (tt-satisfiable? f)) 14)
               #("resolution" by-resolution 40)
               #("DPLL" (fn [f] (is-not (satisfiable f) None)) 200)
               #("Z3" by-z3 1000)])

(defn row [label formula nvars]
  (setv cells [] answers #{})
  (for [[name method max-vars] METHODS]
    (if (> nvars max-vars)
        (.append cells "-")
        (do
          (setv [r ms] (timed (fn [] (method formula))))
          (cond
            (= r "timeout") (.append cells f">{BUDGET} s")
            (is r None) (.append cells "gave up")
            True (do (.add answers r) (.append cells (+ (format ms ".1f") " ms")))))))
  (assert (<= (len answers) 1) f"methods disagree on {label}")
  (print (.ljust label 22) (.join "  " (gfor c cells (.rjust c 10)))
         " " (if answers (if (get (list answers) 0) "sat" "unsat") "?") :flush True))

(print (.ljust "problem" 22) (.join "  " (gfor m METHODS (.rjust (get m 0) 10))))
(setv rng (random.Random 1))
(for [n [6 10 14 20 40 80 160]]
  (for [k (range 3)]
    (row f"3-SAT n={n} #{k}" (random-3sat rng n) n)))
(for [h [3 4 5 6 7]]
  (row f"pigeonhole {(+ h 1)}->{h}" (pigeonhole h) (* h (+ h 1))))
