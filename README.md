# Hylogic

Propositional logic evaluator for [Hy](https://github.com/hylang/hy)

```
; require macros and import functions and variables
(require (hylogic.macros(*)))
(import [hylogic.macros[*]])
; NL for newlines
(setv NL "\r\n")
```

## Atoms and Axioms

### Symbols

### Connectives

## Propositions

```
(defproposition P True "It is raining")
(defproposition Q True "It is cold outside")
(defproposition R True "I'm indoors")
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
(print a)
```

Is argument valid?

```
(print a.valid)
```

## Truth tables

```
(truth-tables-html 2 cimp?)
```
