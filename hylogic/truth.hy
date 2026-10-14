"Truth tables and the questions they answer.

For propositional formulas, a truth table settles everything: whether a
formula is a tautology, satisfiable or a contradiction, whether two formulas
are equivalent, and whether premises entail a conclusion, with a
counterexample when they do not.

  (print (truth-table '(→ (∧ P (→ P Q)) Q)))"

(import itertools [product]
        html
        hylogic.formulas [formula operator-of args-of pretty QUANTIFIERS]
        hylogic.evaluate [evaluate]
        hylogic.terms [compound? show]
        hylogic.connectives [CONNECTIVES])

(defn propositions [form]
  "The proposition names in a formula, in order of first appearance."
  (setv found [])
  (defn walk [f]
    (setv op (operator-of f))
    (cond
      (in op QUANTIFIERS)
        (raise (ValueError "truth tables are for propositional formulas; use evaluate with a domain, or prove"))
      op (for [a (args-of f)] (walk a))
      (compound? f)
        (raise (ValueError f"truth tables are for propositional formulas, but {(show f)} is a predicate"))
      (and (not-in f #{"true" "false"}) (not-in f found)) (.append found f)))
  (walk (formula form))
  found)

(defn assignments [names]
  "Every assignment of truth values to names, as dicts, in truth-table order."
  (gfor values (product [True False] :repeat (len names))
        (dict (zip names values))))

(defn _mark [v] (if v "⊤" "⊥"))

(defclass TruthTable []
  "Rows of a truth table. Prints as text and shows as HTML in a notebook."
  (defn __init__ [self forms]
    (setv self.formulas (lfor f forms (formula f))
          self.names [])
    (for [f self.formulas  p (propositions f)]
      (when (not-in p self.names) (.append self.names p)))
    (setv self.rows
      (lfor env (assignments self.names)
            #((tuple (.values env)) (tuple (gfor f self.formulas (evaluate f env)))))))
  (defn headers [self]
    [#* self.names #* (map pretty self.formulas)])
  (defn __str__ [self]
    (setv headers (.headers self)
          widths (lfor h headers (max 1 (len h)))
          lines [(.join " │ " (gfor [h w] (zip headers widths) (.center h w)))
                 (.join "─┼─" (gfor w widths (* "─" w)))])
    (for [[values results] self.rows]
      (.append lines (.join " │ " (gfor [v w] (zip [#* values #* results] widths) (.center (_mark v) w)))))
    (.join "\n" lines))
  (defn __repr__ [self] (str self))
  (defn _repr_html_ [self]
    (setv head (.join "" (gfor h (.headers self) f"<th>{(html.escape h)}</th>"))
          body (.join "" (gfor [values results] self.rows
                               (+ "<tr>"
                                  (.join "" (gfor v values f"<td>{(_mark v)}</td>"))
                                  (.join "" (gfor v results f"<td><b>{(_mark v)}</b></td>"))
                                  "</tr>"))))
    f"<table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>"))

(defn truth-table [#* forms]
  "The truth table of one or more propositional formulas over their shared propositions."
  (TruthTable forms))

(defn tautology? [form]
  (all (gfor [_ [r]] (. (TruthTable [form]) rows) r)))

(defn satisfiable? [form]
  (any (gfor [_ [r]] (. (TruthTable [form]) rows) r)))

(defn contradiction? [form]
  (not (satisfiable? form)))

(defn equivalent? [a b]
  (all (gfor [_ [x y]] (. (TruthTable [a b]) rows) (= x y))))

(defn counterexample [premises conclusion]
  "An assignment that makes every premise true and the conclusion false, or None."
  (setv table (TruthTable [#* premises conclusion]))
  (for [[values results] table.rows]
    (when (and (all (cut results 0 -1)) (not (get results -1)))
      (return (dict (zip table.names values)))))
  None)

(defn entails? [premises conclusion]
  "Do the premises entail the conclusion? Checked by truth table."
  (is (counterexample premises conclusion) None))

(defn connective-table [connective [arity 2]]
  "The truth table of one connective from CONNECTIVES, with arity arguments."
  (setv n (or connective.arity arity)
        names (cut ["P" "Q" "R" "S" "T"] 0 n))
  (TruthTable [#(connective.operator #* names)]))

(defn connective-tables [[arity 2]]
  "Truth tables for all connectives, as text."
  (.join "\n\n" (gfor c CONNECTIVES
                      (+ f"{c.symbol}  {c.name}\n" (str (connective-table c arity))))))
