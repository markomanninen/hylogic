"Evaluating formulas in a model.

A model gives meaning to the names in a formula:

  propositions   name -> truth value                 {\"P\" True}
  predicates     name -> function, or a collection   {\"Man\" #{\"socrates\"}}
                 of the argument tuples it holds for  {\"Loves\" #{#(\"a\" \"b\")}}
  functions      name -> function                    {\"mother\" (fn [x] ...)}
  constants      name -> value; a name the model does not mention stands for itself

Quantifiers range over a finite domain:

  (evaluate '(∀ [x] (→ (Man x) (Mortal x)))
            {\"Man\" #{\"socrates\"} \"Mortal\" #{\"socrates\" \"zeus\"}}
            :domain [\"socrates\" \"zeus\"])"

(import itertools
        hylogic.formulas [formula operator-of args-of QUANTIFIERS]
        hylogic.connectives [BY-OPERATOR]
        hylogic.terms [compound?])

(defn _value [t model bound]
  "The value of a term."
  (cond
    (compound? t) ((get model (get t 0)) #* (gfor a (cut t 1 None) (_value a model bound)))
    (in t bound) (get bound t)
    (in t model) (get model t)
    True t))

(defn _holds [relation args]
  (if (callable relation)
      (bool (relation #* args))
      (or (in (tuple args) relation)
          (and (= (len args) 1) (in (get args 0) relation)))))

(defn _eval [f model domain bound]
  (setv op (operator-of f))
  (cond
    (= f "true") True
    (= f "false") False
    (is op None)
      (if (compound? f)
          (do
            (setv name (get f 0))
            (when (not-in name model)
              (raise (KeyError f"the model does not interpret the predicate {name}")))
            (_holds (get model name) (lfor a (cut f 1 None) (_value a model bound))))
          (do
            (when (not-in f model)
              (raise (KeyError f"the model gives no truth value for {f}")))
            (bool (get model f))))
    (in op QUANTIFIERS)
      (do
        (when (is domain None)
          (raise (ValueError "quantifiers need a domain: evaluate it with :domain [...]")))
        (setv names (get f 1)
              body (get f 2)
              test (fn [values] (_eval body model domain (| bound (dict (zip names values)))))
              combos (_product domain (len names)))
        (if (= op "forall")
            (all (map test combos))
            (any (map test combos))))
    True
      ((. (get BY-OPERATOR op) function) #* (gfor a (args-of f) (_eval a model domain bound)))))

(defn _product [domain n]
  (itertools.product (list domain) :repeat n))

(defn evaluate [form [model None] [domain None]]
  "The truth value of a formula in a model, with quantifiers over domain."
  (_eval (formula form) (or model {}) domain {}))
