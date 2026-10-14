"A walk through hylogic. Run from the repository root:

  hy examples/tour.hy"

(import sys pathlib [Path])
(.insert sys.path 0 (str (. (Path __file__) parent parent)))

(import hylogic.truth [truth-table]
        hylogic.argument [Argument]
        hylogic.evaluate [evaluate]
        hylogic.terms [term show]
        hylogic.unify [unify substitute]
        hylogic.rewrite [normalize rule-text]
        hylogic.resolution [prove clausify-steps]
        hylogic.problems [PEANO DERIVATIVE FIRST-ORDER HARD])

(defn heading [text]
  (print (+ "\n" text "\n" (* "=" (len text)))))

(heading "1. Truth tables")
(print (truth-table '(→ (∧ P (→ P Q)) Q) '(⊕ P Q)))

(heading "2. Arguments")
(print (.explain (Argument ['(→ P Q) '(¬ Q)] '(¬ P) :meanings {"P" "It rains" "Q" "The street is wet"})))
(print)
(print (.explain (Argument ['(→ P Q) 'Q] 'P)))

(heading "3. A formula in a finite model")
(setv model {"Man" #{"socrates" "plato"} "Mortal" #{"socrates" "plato" "fido"}})
(print "∀x (Man x → Mortal x):" (evaluate '(∀ [x] (→ (Man x) (Mortal x))) model ["socrates" "plato" "fido"]))
(print "∀x (Mortal x → Man x):" (evaluate '(∀ [x] (→ (Mortal x) (Man x))) model ["socrates" "plato" "fido"]))

(heading "4. Unification")
(setv a (term '(Knows john ?x))
      b (term '(Knows ?y (mother ?y)))
      s (unify a b))
(print "unify" (show a) "and" (show b))
(print "  substitution:" (.join ", " (gfor [k v] (.items s) f"{k} = {(show v)}")))
(print "  both become: " (show (substitute a s)))

(heading "5. Rewriting: 2 × 2 in Peano arithmetic")
(setv [nf steps] (normalize '(* (s (s 0)) (s (s 0))) PEANO))
(print "  " (show (term '(* (s (s 0)) (s (s 0))))))
(for [[rule t] steps]
  (print "=>" (.ljust (show t) 42) "by" (rule-text rule)))

(heading "6. Rewriting: d/dx (x · x)")
(setv [nf steps] (normalize '(d x (* x x)) DERIVATIVE))
(for [[rule t] steps]
  (print "=>" (show t)))

(heading "7. Clausal form of P20")
(for [[stage text] (clausify-steps (get (get FIRST-ORDER 4) 2))]
  (print f"{stage}:")
  (if (isinstance text list)
      (for [c text] (print "   " c))
      (print "   " text)))

(heading "8. Proof: did Curiosity kill the cat?")
(setv [name axioms goal] (get FIRST-ORDER 1))
(for [a axioms] (print "  axiom:" (show (term a))))
(print "  goal: " (show (term goal)))
(print)
(setv result (prove goal axioms))
(for [line (.proof result)] (print line))
(setv kept (get result.stats "kept") generated (get result.stats "generated"))
(print f"\n{kept} clauses kept, {generated} generated")

(heading "9. Where the method strains: Andrews' challenge (P34)")
(setv [name axioms goal] (get HARD 0))
(for [limit [2000 10000]]
  (setv r (prove goal axioms :limit limit))
  (setv kept (get r.stats "kept") generated (get r.stats "generated"))
  (print f"  limit {limit}: {r.status}, {kept} kept, {generated} generated, proof {(len (.proof r))} lines"))
