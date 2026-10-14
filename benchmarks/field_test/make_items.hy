"Generate the field test's arguments, with validity decided by hylogic.

32 propositional arguments in English, half valid, and 8 first-order
syllogisms. A valid item needs every premise: without any one of them the
conclusion no longer follows. An invalid item is tempting: the conclusion is
true in at least two thirds of the situations the premises allow.

  hy benchmarks/field_test/make_items.hy > benchmarks/field_test/items.json"

(import json random sys
        hylogic.argument [Argument]
        hylogic.formulas [pretty]
        hylogic.truth [propositions assignments]
        hylogic.evaluate [evaluate])

(setv SENTENCES ["the alarm is set" "the door is locked" "the lights are on" "Anna is at home"
                 "the heating is on" "the window is open" "the dog is outside" "the car is in the garage"
                 "the printer is working" "the meeting is cancelled" "the report is finished"
                 "the server is down"])

(defn cap [s] (+ (.upper (cut s 0 1)) (cut s 1 None)))

;; premise patterns: number of sentences used, formula, English
(setv PREMISES [
  #(2 (fn [a b] #("=>" a b)) (fn [a b] f"If {a}, then {b}."))
  #(2 (fn [a b] #("=>" a b)) (fn [a b] f"{(cap b)} if {a}."))
  #(2 (fn [a b] #("=>" a b)) (fn [a b] f"{(cap a)} only if {b}."))
  #(2 (fn [a b] #("or" a b)) (fn [a b] f"{(cap a)} or {b}, or both."))
  #(2 (fn [a b] #("or" a b)) (fn [a b] f"Unless {a}, {b}."))
  #(1 (fn [a] #("not" a)) (fn [a] f"It is not the case that {a}."))
  #(1 (fn [a] a) (fn [a] f"{(cap a)}."))
  #(2 (fn [a b] #("<=>" a b)) (fn [a b] f"{(cap a)} if and only if {b}."))
  #(3 (fn [a b c] #("=>" #("and" a b) c)) (fn [a b c] f"If {a} and {b}, then {c}."))
  #(2 (fn [a b] #("not" #("and" a b))) (fn [a b] f"It is not the case that both {a} and {b}."))
  #(3 (fn [a b c] #("=>" a #("or" b c))) (fn [a b c] f"If {a}, then {b} or {c}."))])

(setv CONCLUSIONS [
  #(1 (fn [a] a) (fn [a] f"{(cap a)}."))
  #(1 (fn [a] #("not" a)) (fn [a] f"It is not the case that {a}."))
  #(2 (fn [a b] #("=>" a b)) (fn [a b] f"If {a}, then {b}."))
  #(2 (fn [a b] #("or" a b)) (fn [a b] f"{(cap a)} or {b}, or both."))])

(defn instance [rng patterns sentences]
  (setv [n f text] (.choice rng patterns)
        chosen (.sample rng sentences n))
  #((f #* chosen) (text #* chosen)))

(defn valid? [premises conclusion]
  (. (Argument premises conclusion) valid))

(defn temptation [premises conclusion]
  "Share of the situations allowed by the premises in which the conclusion is true."
  (setv names (propositions #("and" #* premises conclusion))
        allowed (lfor env (assignments names) :if (all (gfor p premises (evaluate p env))) env))
  (if allowed (/ (sum (gfor env allowed (evaluate conclusion env))) (len allowed)) 0))

(defn propositional-items [rng want]
  (setv items [] counts {True 0 False 0} tries 0)
  (while (< (len items) want)
    (+= tries 1)
    (setv sentences (.sample rng SENTENCES 4)
          k (.randint rng 3 4)
          ps (lfor _ (range k) (instance rng PREMISES sentences))
          [cf ct] (instance rng CONCLUSIONS sentences)
          pfs (lfor p ps (get p 0))
          valid (valid? pfs cf))
    (when (>= (get counts valid) (// want 2)) (continue))
    (when (and valid (not (all (gfor i (range k) (not (valid? (+ (cut pfs 0 i) (cut pfs (+ i 1) None)) cf))))))
      (continue))
    (when (and (not valid) (< (temptation pfs cf) (/ 2 3))) (continue))
    ;; no argument may be decided by the premises being contradictory
    (when (is (. (Argument pfs "false") valid) True) (continue))
    (+= (get counts valid) 1)
    (.append items {"id" f"P{(+ (len items) 1)}" "kind" "propositional"
                    "text" (+ (.join " " (gfor p ps (get p 1))) " Therefore, " (+ (.lower (cut ct 0 1)) (cut ct 1 None)))
                    "premises" (lfor p pfs (pretty p)) "conclusion" (pretty cf)
                    "premise_terms" pfs "conclusion_term" cf "valid" valid}))
  items)

(defn all-are [a b] #("forall" #("x") #("=>" #(a "x") #(b "x"))))
(defn some-are [a b] #("exists" #("x") #("and" #(a "x") #(b "x"))))
(defn no-are [a b] #("not" (some-are a b)))
(defn some-are-not [a b] #("exists" #("x") #("and" #(a "x") #("not" #(b "x")))))

;; believable but invalid, or absurd but valid, to test belief bias
(setv SYLLOGISMS [
  #("All roses are flowers. Some flowers fade quickly. Therefore, some roses fade quickly."
    [(all-are "Rose" "Flower") (some-are "Flower" "FadesQuickly")] (some-are "Rose" "FadesQuickly"))
  #("All mammals can fly. All whales are mammals. Therefore, all whales can fly."
    [(all-are "Mammal" "Flies") (all-are "Whale" "Mammal")] (all-are "Whale" "Flies"))
  #("All doctors went to university. No nurses are doctors. Therefore, no nurses went to university."
    [(all-are "Doctor" "University") (no-are "Nurse" "Doctor")] (no-are "Nurse" "University"))
  #("No birds are mammals. Some pets are birds. Therefore, some pets are not mammals."
    [(no-are "Bird" "Mammal") (some-are "Pet" "Bird")] (some-are-not "Pet" "Mammal"))
  #("Some athletes are students. Some students are musicians. Therefore, some athletes are musicians."
    [(some-are "Athlete" "Student") (some-are "Student" "Musician")] (some-are "Athlete" "Musician"))
  #("All fish live in trees. Some salmon are fish. Therefore, some salmon live in trees."
    [(all-are "Fish" "LivesInTrees") (some-are "Salmon" "Fish")] (some-are "Salmon" "LivesInTrees"))
  #("All squares are rectangles. Therefore, all rectangles are squares."
    [(all-are "Square" "Rectangle")] (all-are "Rectangle" "Square"))
  #("No reptiles have fur. All snakes are reptiles. Therefore, no snakes have fur."
    [(no-are "Reptile" "HasFur") (all-are "Snake" "Reptile")] (no-are "Snake" "HasFur"))])

(defn syllogism-items []
  (lfor [i [text ps c]] (enumerate SYLLOGISMS)
        {"id" f"S{(+ i 1)}" "kind" "syllogism" "text" text
         "premises" (lfor p ps (pretty p)) "conclusion" (pretty c)
         "premise_terms" ps "conclusion_term" c "valid" (valid? ps c)}))

(setv items [#* (propositional-items (random.Random 2026) 32) #* (syllogism-items)])
(print (json.dumps items :indent 1 :ensure-ascii False))
