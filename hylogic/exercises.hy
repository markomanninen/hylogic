"Checking logic exercises, with feedback a student can act on.

Two kinds of exercise are checked:

- formalize: translate an English sentence into a formula. The answer is
  correct when it is logically equivalent to the reference, however it is
  written. When it is not, the feedback shows a situation where the two
  differ, in the words of the sentence.
- validity: decide whether an argument is valid. A claim that it is invalid
  can come with a counterexample, which is checked too.

  (check-formalization '(→ Q P) '(→ P Q) {\"P\" \"it rains\" \"Q\" \"the street is wet\"})"

(import hylogic.formulas [formula basic pretty]
        hylogic.evaluate [evaluate]
        hylogic.truth [propositions]
        hylogic.sat [satisfiable]
        hylogic.resolution [prove]
        hylogic.models [countermodel]
        hylogic.argument [Argument propositional?])

(defclass Feedback []
  (defn __init__ [self correct message [situation None]]
    (setv self.correct correct
          self.message message
          self.situation situation))
  (defn __bool__ [self] (bool self.correct))
  (defn __str__ [self] self.message))

(defn _truth [v] (if v "true" "false"))

(defn describe [assignment [meanings None]]
  "An assignment in words: \"it rains\" is true, \"the street is wet\" is false."
  (setv meanings (or meanings {})
        parts (lfor [name value] (.items assignment)
                    (+ (if (in name meanings) f"“{(get meanings name)}”" name)
                       " is " (_truth value))))
  (if (> (len parts) 1)
      (+ (.join ", " (cut parts 0 -1)) " and " (get parts -1))
      (.join "" parts)))

(defn check-formalization [answer reference [meanings None] [limit 2000]]
  "Is the answer equivalent to the reference formula? Feedback explains a difference."
  (setv a (formula answer) r (formula reference))
  (if (and (propositional? a) (propositional? r))
      (do
        (setv names (propositions #("and" a r))
              situation (satisfiable #("not" #("<=>" (basic a) (basic r)))))
        (when (is situation None)
          (return (Feedback True f"Correct. {(pretty a)} says the same as the sentence.")))
        ;; fill in atoms the solver left out, so the description is complete
        (setv situation (dfor n names n (.get situation n False)))
        (Feedback False
                  (+ f"Not quite. Suppose {(describe situation meanings)}. Then your formula is "
                     f"{(_truth (evaluate a situation))}, but the sentence is {(_truth (evaluate r situation))}.")
                  situation))
      (do
        (when (. (prove #("<=>" a r) :limit limit) proved)
          (return (Feedback True f"Correct. {(pretty a)} says the same as the sentence.")))
        (setv world (countermodel [] #("<=>" a r)))
        (if world
            (Feedback False
                      (+ "Not quite. In this world your formula is "
                         f"{(_truth (evaluate a (.as-model world) world.domain))}, but the sentence is "
                         f"{(_truth (evaluate r (.as-model world) world.domain))}:\n{world}")
                      world)
            (Feedback None "Could not decide within the search limits; ask a teacher.")))))

(defn check-validity-claim [premises conclusion claim [counterexample None] [meanings None]]
  "Check a claim that an argument is valid (True) or invalid (False), and a counterexample if given."
  (setv argument (Argument premises conclusion :meanings meanings))
  (cond
    (is argument.valid None)
      (Feedback None "Could not decide this argument within the search limits.")
    (!= claim argument.valid)
      (Feedback False
                (if argument.valid
                    "Not quite. The argument is valid: whenever the premises are true, so is the conclusion."
                    (+ "Not quite. The argument is invalid. "
                       (cond
                         argument.counterexample
                           f"Suppose {(describe argument.counterexample meanings)}. Then the premises are true and the conclusion is false."
                         argument.countermodel
                           f"In this world the premises are true and the conclusion is false:\n{argument.countermodel}"
                         True
                           "There is a world where the premises are true and the conclusion is false."))))
    (and (not claim) counterexample)
      (do
        (setv premises-true (all (gfor p argument.premises (evaluate p counterexample)))
              conclusion-false (not (evaluate argument.conclusion counterexample)))
        (if (and premises-true conclusion-false)
            (Feedback True "Correct, and your counterexample works.")
            (Feedback False
                      (+ "The argument is invalid, but your counterexample does not show it: "
                         (if premises-true "the conclusion is true there." "not all premises are true there.")))))
    True (Feedback True (if claim "Correct, the argument is valid." "Correct, the argument is invalid."))))
