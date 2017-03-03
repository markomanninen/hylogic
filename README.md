# hylogic

Propositional logic evaluator for Hy

## Atoms and Axioms

### Symbols

### Connectives

## Propositions

```
(defproposition P True "It is raining")
(defproposition Q True "It is cold outside")
(defproposition R False "I'm indoors")
```

## Arguments

```
(setv a (defargument 
  (defpremise (P ∧ Q) → R)
  (defpremise (P ∧ Q))
  (defconclusion R)))
```

Show argumentation inference rules:

```
(print (str a))
```

Is argument valid?

```
(print a.valid)
```
