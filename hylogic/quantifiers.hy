"Quantifiers over Python data.

  (require hylogic.quantifiers [∀ ∃])
  (∀ [x (range 1 10)] (> x 0))              ; every x in 1..9 is positive
  (∃ [x (range 10)] (< x 1))                ; some x is below 1
  (∀ [x [1 2] y [-1 -2]] (!= (+ x y) 5))    ; nested: every pair

Several bindings nest, so the body is checked for every combination. The
check stops at the first counterexample (∀) or witness (∃). The ASCII names
forall and exists work the same."

(defmacro ∀ [bindings body]
  `(all (gfor ~@bindings ~body)))

(defmacro ∃ [bindings body]
  `(any (gfor ~@bindings ~body)))

(defmacro forall [bindings body]
  `(all (gfor ~@bindings ~body)))

(defmacro exists [bindings body]
  `(any (gfor ~@bindings ~body)))
