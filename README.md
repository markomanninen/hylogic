# Hylogic

Propositional logic evaluator for [Hy](https://github.com/hylang/hy)

## Requirements and installation

### Jupyter and Hy

A little bit work is required to get everything running on your local computer. First you need Jupyter Notebook and Calysto Hy kernel to interact with this document. Easy way to get Jupyter Notebook running is to use Anaconda package from Continuum: https://www.continuum.io/downloads. It will install Python language interpreter to your computer, which is also required.

[Hy](http://docs.hylang.org/en/latest/index.html) language, which by the way is a cool Lisp syntax and feature set upon Python, you can get from: https://github.com/hylang/hy. Then follow Calysto Hy kernel installation instructions from their GitHub project page: https://github.com/Calysto/calysto_hy.

After installation you should be ready to print environment information running this Hy code:

```
(import hy sys)
(print "Hy version: " hy.__version__)
(print "Python" sys.version)
```

Hy version should be 0.12.1 and above. Python 3.5 or above. Code is not tested versions below those.

Of course you can just set up Python and Hy without Jupyter notebook and Calysto Hy Kernel, but then you need to interact from console. I just recommend to use Jupyter because it makes prototyping, testing, and documentation so much easier, even fun to do!

```
; require macros and import functions and variables
(require (hylogic.macros(*)))
(import [hylogic.macros[*]])
```

## Atoms and Axioms

### Symbols

Propositional constants:

- ⊤ (True / 1)
- ⊥ (False / 0)

### Connectives

¬ 	 not     	 Negation
∧ 	 and     	 Conjunction
↑ 	 nand     	 Nonconjunction
∨ 	 or     	 Disjunction
↓ 	 nor     	 Nondisjunction
↮ 	 xor     	 Exclusive or
↔ 	 xnor     	 Nonexclusive or
≡ 	 eqv     	 Equivalence
≢ 	 neqv     	 Nonequivalence
← 	 cimp     	 Converse implication
↛ 	 cnimp     	 Converse nonimplication
↚ 	 mimp     	 Material implication
→ 	 mnimp     	 Material nonimplication

## Propositions

Propositional variables are created with `defproposition` and `defproposition*` macros. Latter macro also creates a negation variable to reduce some repetitive work.

```
(defproposition* P False "Today is Tuesday")
(defproposition* Q True "John will go to work")
(println P ¬P)
```

P<Today is Tuesday>=False
¬P<Today is Tuesday>=True

## Argumentation

Introducting `defargument`, `defpremise`, and `defconclusion` macros.

```
(setv a 
  (defargument 
    ; If today is Tuesday, then John will go to work.
    (defpremise P → Q)
    ; Today is Tuesday.
    (defpremise P)
    ; Therefore, John will go to work.
    (defconclusion Q)))
(print a)
```

  P → Q
  P
--------------
∴ Q

## First order logic

### Quantifiers, predicates, variables, sets

#### Universal quantifier (∀)

```
(∀ (x) (x > 0) (range 1 10)) ; all items [1 ... 9] are greater than 0?
```

#### Existential  quantifier (∃)

```
(∃ (x) (x < 1) (range 0 10)) ; is at least one item of [0 ... 9] smaller than 1?
```

#### Nested quantifiers

```
(setv DX [1 1]
      DY [-1 -2])
; all[any[1-1=0 1-2=-1] any[1-1=0 1-2=-1]]
(∀ (x) (∃ (y) (x + y = 0) DY) DX)
```

=> True

## Truth tables

```
(truth-tables-html 2 cimp?)
```
