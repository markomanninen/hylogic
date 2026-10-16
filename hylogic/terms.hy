"Terms: quoted Hy forms turned into plain Python data.

You write terms and formulas as quoted Hy code, for example
'(Loves ?x (mother-of ?x)). The function `term` turns that into tuples and
strings, which are simpler to compare and hash than Hy's own models:

  a variable          a string starting with ?          \"?x\"
  a constant          any other string, or a number     \"socrates\", 0
  a compound term     a tuple, the name first           (\"mother-of\", \"?x\")"

(defn term [form]
  "Turn a quoted Hy form into a term."
  (cond
    (isinstance form hy.models.Symbol) (str form)
    ;; plain tuples too, since they may hold quoted forms: #("not" '(P x))
    (isinstance form #(hy.models.Expression hy.models.List tuple)) (tuple (gfor x form (term x)))
    (isinstance form hy.models.String) (str form)
    (isinstance form hy.models.Integer) (int form)
    (isinstance form hy.models.Float) (float form)
    True form))

(defn variable? [t]
  (and (isinstance t str) (.startswith t "?")))

(defn compound? [t]
  (isinstance t tuple))

(defn show [t]
  "A term as Lisp text."
  (if (compound? t)
      (+ "(" (.join " " (map show t)) ")")
      (str t)))

(defn size [t]
  "Number of symbols in a term."
  (if (compound? t) (sum (map size t)) 1))

(defn variables-of [t [found None]]
  "The variables of a term, in order of first occurrence."
  (when (is found None) (setv found []))
  (cond
    (and (variable? t) (not-in t found)) (.append found t)
    (compound? t) (for [x t] (variables-of x found)))
  found)
