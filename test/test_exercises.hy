(import pytest
        hylogic.exercise-sets [EXERCISES BY-ID check-answer]
        hylogic.exercises [check-formalization check-validity-claim describe]
        hylogic.argument [Argument])

(setv FORMALIZE (lfor e EXERCISES :if (= (get e "kind") "formalize") e))
(setv VALIDITY (lfor e EXERCISES :if (= (get e "kind") "validity") e))

(defn [(pytest.mark.parametrize "exercise" FORMALIZE :ids (lfor e FORMALIZE (get e "id")))]
  test-reference-answers-are-accepted [exercise]
  (assert (. (check-answer exercise (get exercise "answer")) correct)))

(defn [(pytest.mark.parametrize "exercise" VALIDITY :ids (lfor e VALIDITY (get e "id")))]
  test-validity-answers-match-the-library [exercise]
  ;; the stated answer must be what the library decides, or the exercise is wrong
  (assert (= (. (Argument (get exercise "premises") (get exercise "conclusion")) valid)
             (get exercise "valid")))
  (assert (. (check-answer exercise (get exercise "valid")) correct)))

(defn test-equivalent-answers-count-as-correct []
  (assert (. (check-answer "F1" '(∨ (¬ P) Q)) correct))
  (assert (. (check-answer "F4" '(¬ (∨ B T))) correct))              ; De Morgan
  (assert (. (check-answer "F13" '(∀ [x] (→ (Cat x) (¬ (LikesWater x))))) correct)))

(defn test-wrong-propositional-answer-is-explained []
  (setv fb (check-answer "F2" '(→ P Q)))                           ; the converse
  (assert (is fb.correct False))
  (assert (in "“it rains” is" (str fb)))
  (assert (in "your formula is" (str fb))))

(defn test-wrong-first-order-answer-shows-a-world []
  (setv fb (check-answer "F11" '(∃ [y] (∧ (Book y) (∀ [x] (→ (Student x) (Reads x y)))))))
  (assert (is fb.correct False))
  (assert (in "Domain:" (str fb))))

(defn test-validity-claims []
  (assert (not (. (check-answer "V2" True) correct)))
  (assert (in "invalid" (str (check-answer "V2" True))))
  (assert (in "Domain:" (str (check-answer "V9" True))))
  (assert (. (check-answer "V2" False :counterexample {"P" False "Q" True}) correct))
  (setv fb (check-answer "V2" False :counterexample {"P" True "Q" True}))
  (assert (not fb.correct))
  (assert (in "does not show it" (str fb))))

(defn test-describe-uses-meanings []
  (assert (= (describe {"P" True "Q" False} {"P" "it rains"})
             "“it rains” is true and Q is false")))
