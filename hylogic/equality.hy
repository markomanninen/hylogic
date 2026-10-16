"Equality as axioms.

Resolution treats = as just another predicate, so it cannot know that equal
things can replace each other. The simplest remedy is to add the axioms that
say so, for the symbols of the problem at hand:

  reflexivity    ∀x x = x
  symmetry       ∀x y (x = y → y = x)
  transitivity   ∀x y z (x = y ∧ y = z → x = z)
  congruence     for each function f and argument i:
                   ∀x y (x = y → f(... x ...) = f(... y ...))
                 for each predicate p and argument i:
                   ∀x y (x = y ∧ p(... x ...) → p(... y ...))

This is complete but slow, because the axioms resolve with almost anything.
Superposition, which builds equality into the inference rules, is the method
real provers use."

(import hylogic.formulas [basic]
        hylogic.export [signature])

(defn _vars [n] (lfor i (range 1 (+ n 1)) f"EqX{i}"))

(defn equality-axioms [formulas]
  "The equality axioms for the functions and predicates used in the formulas."
  (setv sig (signature (lfor f formulas (basic f)))
        axioms [#("forall" #("EqX") #("=" "EqX" "EqX"))
                #("forall" #("EqX" "EqY") #("=>" #("=" "EqX" "EqY") #("=" "EqY" "EqX")))
                #("forall" #("EqX" "EqY" "EqZ")
                  #("=>" #("and" #("=" "EqX" "EqY") #("=" "EqY" "EqZ")) #("=" "EqX" "EqZ")))])
  (for [[name n] (sorted (.items (get sig "functions")))  i (range n)]
    (setv xs (_vars n)
          ys (+ (cut xs 0 i) ["EqY"] (cut xs (+ i 1) None)))
    (.append axioms #("forall" #(#* xs "EqY")
                      #("=>" #("=" (get xs i) "EqY") #("=" #(name #* xs) #(name #* ys))))))
  (for [[name n] (sorted (.items (get sig "predicates")))  i (range n)]
    (when (!= name "=")
      (setv xs (_vars n)
            ys (+ (cut xs 0 i) ["EqY"] (cut xs (+ i 1) None)))
      (.append axioms #("forall" #(#* xs "EqY")
                        #("=>" #("and" #("=" (get xs i) "EqY") #(name #* xs)) #(name #* ys))))))
  axioms)
