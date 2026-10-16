"Exercises for an introduction to logic.

Each exercise is a dict. A formalize exercise has the sentence, the meanings
of its letters or predicates, and a reference answer. A validity exercise has
premises, a conclusion and whether the argument is valid.

  (import hylogic.exercise-sets [EXERCISES check-answer])
  (print (check-answer (get EXERCISES 1) '(→ P Q)))"

(import hylogic.exercises [check-formalization check-validity-claim])

(defn formalize [id text meanings answer]
  {"id" id "kind" "formalize" "text" text "meanings" meanings "answer" answer})

(defn validity [id text meanings premises conclusion valid]
  {"id" id "kind" "validity" "text" text "meanings" meanings
   "premises" premises "conclusion" conclusion "valid" valid})

(setv RAIN {"P" "it rains" "Q" "the street is wet"})
(setv TRAVEL {"B" "the bus is late" "T" "the train is late"})

(setv EXERCISES [
  ;; Propositional formalization
  (formalize "F1" "If it rains, the street is wet." RAIN '(→ P Q))
  (formalize "F2" "The street is wet only if it rains." RAIN '(→ Q P))
  (formalize "F3" "It rains unless the sun shines."
             {"P" "it rains" "S" "the sun shines"} '(∨ P S))
  (formalize "F4" "Neither the bus nor the train is late." TRAVEL '(∧ (¬ B) (¬ T)))
  (formalize "F5" "The bus and the train are not both late." TRAVEL '(¬ (∧ B T)))
  (formalize "F6" "The alarm sounds if and only if the door opens."
             {"A" "the alarm sounds" "D" "the door opens"} '(↔ A D))
  (formalize "F7" "If the door opens and the code is wrong, the alarm sounds."
             {"A" "the alarm sounds" "D" "the door opens" "C" "the code is wrong"} '(→ (∧ D C) A))
  (formalize "F8" "The meeting is on Monday or on Tuesday, but not on both."
             {"M" "the meeting is on Monday" "T" "the meeting is on Tuesday"} '(⊕ M T))
  (formalize "F9" "You get a refund only if you have the receipt and return the item within 30 days."
             {"F" "you get a refund" "R" "you have the receipt" "W" "you return the item within 30 days"}
             '(→ F (∧ R W)))
  (formalize "F10" "The program stops whenever its input is finite."
             {"S" "the program stops" "I" "its input is finite"} '(→ I S))

  ;; First-order formalization
  (formalize "F11" "Every student reads some book."
             {"Student" "is a student" "Book" "is a book" "Reads" "reads"}
             '(∀ [x] (→ (Student x) (∃ [y] (∧ (Book y) (Reads x y))))))
  (formalize "F12" "Some book is read by every student."
             {"Student" "is a student" "Book" "is a book" "Reads" "reads"}
             '(∃ [y] (∧ (Book y) (∀ [x] (→ (Student x) (Reads x y))))))
  (formalize "F13" "No cat likes water."
             {"Cat" "is a cat" "LikesWater" "likes water"}
             '(¬ (∃ [x] (∧ (Cat x) (LikesWater x)))))
  (formalize "F14" "Only members can vote."
             {"Member" "is a member" "Votes" "can vote"}
             '(∀ [x] (→ (Votes x) (Member x))))
  (formalize "F15" "Everybody loves somebody."
             {"Loves" "loves"} '(∀ [x] (∃ [y] (Loves x y))))
  (formalize "F16" "There is somebody whom everybody loves."
             {"Loves" "loves"} '(∃ [y] (∀ [x] (Loves x y))))

  ;; Validity
  (validity "V1" "If it rains, the street is wet. It rains. So the street is wet."
            RAIN ['(→ P Q) 'P] 'Q True)
  (validity "V2" "If it rains, the street is wet. The street is wet. So it rains."
            RAIN ['(→ P Q) 'Q] 'P False)
  (validity "V3" "If it rains, the street is wet. It does not rain. So the street is not wet."
            RAIN ['(→ P Q) '(¬ P)] '(¬ Q) False)
  (validity "V4" "If it rains, the street is wet. The street is not wet. So it does not rain."
            RAIN ['(→ P Q) '(¬ Q)] '(¬ P) True)
  (validity "V5" "The bus or the train is late. The bus is not late. So the train is late."
            TRAVEL ['(∨ B T) '(¬ B)] 'T True)
  (validity "V6" "If the bus is late, the train is late. If the train is late, I miss the meeting. So if the bus is late, I miss the meeting."
            {"B" "the bus is late" "T" "the train is late" "M" "I miss the meeting"}
            ['(→ B T) '(→ T M)] '(→ B M) True)
  (validity "V7" "All cats are animals. Tom is a cat. So Tom is an animal."
            {"Cat" "is a cat" "Animal" "is an animal"}
            ['(∀ [x] (→ (Cat x) (Animal x))) '(Cat tom)] '(Animal tom) True)
  (validity "V8" "All cats are animals. Tom is an animal. So Tom is a cat."
            {"Cat" "is a cat" "Animal" "is an animal"}
            ['(∀ [x] (→ (Cat x) (Animal x))) '(Animal tom)] '(Cat tom) False)
  (validity "V9" "Everybody loves somebody. So there is somebody whom everybody loves."
            {"Loves" "loves"}
            ['(∀ [x] (∃ [y] (Loves x y)))] '(∃ [y] (∀ [x] (Loves x y))) False)
  (validity "V10" "There is somebody whom everybody loves. So everybody loves somebody."
            {"Loves" "loves"}
            ['(∃ [y] (∀ [x] (Loves x y)))] '(∀ [x] (∃ [y] (Loves x y))) True)])

(setv BY-ID (dfor e EXERCISES (get e "id") e))

(defn check-answer [exercise answer [counterexample None]]
  "Check an answer to an exercise: a formula for formalize, True or False for validity."
  (when (isinstance exercise str) (setv exercise (get BY-ID exercise)))
  (if (= (get exercise "kind") "formalize")
      (check-formalization answer (get exercise "answer") (get exercise "meanings"))
      (check-validity-claim (get exercise "premises") (get exercise "conclusion") answer
                            :counterexample counterexample :meanings (get exercise "meanings"))))
