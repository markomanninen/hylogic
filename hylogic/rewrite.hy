"Term rewriting.

A rule `lhs -> rhs` says that any instance of lhs may be replaced by the same
instance of rhs. Rewriting applies rules until none applies; the result is
the term's normal form. This module rewrites innermost first: arguments are
normalized before the term around them.

Rules are written with the `defrules` macro:

  (require hylogic.rewrite [defrules])
  (defrules peano
    (+ 0 ?y)      -> ?y
    (+ (s ?x) ?y) -> (s (+ ?x ?y)))

A rule may have a condition after :if, an ordinary Hy expression in which the
rule's variables stand for their values:

  (d ?x ?c) -> 0  :if (free-of? ?c ?x)

`defrules` has to be a macro: its arguments are rule text, not code to run,
and the condition has to become a function of the rule's bindings."

(import collections [namedtuple]
        hylogic.terms [term compound? show]
        hylogic.unify [match-term instantiate])

(setv Rule (namedtuple "Rule" ["lhs" "rhs" "condition"]))

(defn make-rule [lhs rhs [condition None]]
  (Rule (term lhs) (term rhs) condition))

(defn rule-text [rule]
  (+ (show rule.lhs) " -> " (show rule.rhs) (if rule.condition "  (conditional)" "")))

(eval-and-compile
  (defn _pattern-vars-to-lookups [form]
    "Replace each ?var symbol in a condition with (get _s \"?var\")."
    (cond
      (and (isinstance form hy.models.Symbol) (.startswith form "?"))
        `(get _s ~(str form))
      (isinstance form hy.models.Expression)
        (hy.models.Expression (lfor x form (_pattern-vars-to-lookups x)))
      (isinstance form hy.models.List)
        (hy.models.List (lfor x form (_pattern-vars-to-lookups x)))
      True form)))

(defmacro defrules [name #* body]
  "Define a list of rewrite rules: lhs -> rhs [:if condition] ..."
  (setv items (list body)
        rules []
        i 0)
  (while (< i (len items))
    (when (or (> (+ i 3) (len items)) (!= (get items (+ i 1)) (hy.models.Symbol "->")))
      (raise (SyntaxError f"defrules: expected `lhs -> rhs` at rule {(+ (// i 3) 1)}")))
    (setv lhs (get items i)
          rhs (get items (+ i 2))
          condition None
          i (+ i 3))
    (when (and (< i (len items)) (= (get items i) (hy.models.Keyword "if")))
      (setv condition `(fn [_s] ~(_pattern-vars-to-lookups (get items (+ i 1))))
            i (+ i 2)))
    (.append rules `(_make-rule '~lhs '~rhs ~condition)))
  `(do
     (import hylogic.rewrite [make-rule :as _make-rule])
     (setv ~name [~@rules])))

(defn rewrite-step [t rules]
  "One innermost rewrite step: #(new-term rule), or None if t is in normal form."
  (when (compound? t)
    ;; the arguments first; position 0 is the function name
    (for [i (range 1 (len t))]
      (setv r (rewrite-step (get t i) rules))
      (when r
        (setv [new rule] r)
        (return #((+ (cut t 0 i) #(new) (cut t (+ i 1) None)) rule)))))
  (for [rule rules]
    (setv s (match-term rule.lhs t))
    (when (and (is-not s None) (or (is rule.condition None) (rule.condition s)))
      (return #((instantiate rule.rhs s) rule))))
  None)

(defn normalize [t rules [limit 10000]]
  "The normal form of t, and the steps that led there as #(rule term-after) pairs."
  (setv t (term t)
        steps [])
  (for [_ (range limit)]
    (setv r (rewrite-step t rules))
    (when (is r None)
      (return #(t steps)))
    (setv [t rule] r)
    (.append steps #(rule t)))
  (raise (RuntimeError f"no normal form within {limit} steps; do the rules loop?")))
