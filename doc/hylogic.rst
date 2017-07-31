
HyLogic
=======

.. raw:: html

   <hr/>

Propositional, predicate, and first-order logic evaluator for
`Hy <https://github.com/hylang/hy>`__ authored by `Marko
Manninen <https://github.com/markomanninen/>`__, 2017.

.. math::


   P → Q\\
   ¬Q\\
   ----\\
   \therefore \space ¬P

Current status
~~~~~~~~~~~~~~

Draft.

The `Python Package Index <https://pypi.python.org/pypi>`__ installation
is not provided yet, but planned in future.

Contents
~~~~~~~~

-  Requirements and installation
-  Propositional logic
-  Semantical notes
-  Truth-bearer in action
-  Resolution of the famous paradox
-  Formulas
-  Argumentation
-  First-order logic
-  Truth tables
-  Venn diagrams
-  License

Requirements and installation
-----------------------------

.. raw:: html

   <hr/>

Jupyter and Hy
~~~~~~~~~~~~~~

Some work is required to get this interactive document running on your
local computer (Mac, PC, Linux). First you need `Jupyter
Notebook <http://jupyter.org/>`__ and `Calysto
tools <http://calysto.github.io/>`__. Easy way to get Jupyter Notebook
running is to use Anaconda package from Continuum:
https://www.continuum.io/downloads. It will also install Python language
interpreter to your computer.

`Hy <http://docs.hylang.org/en/latest/index.html>`__ language, which by
the way is a cool Lisp syntax and feature set upon Python, you can get
from: https://github.com/hylang/hy. Install it and then follow Calysto
Hy kernel installation instructions from their GitHub project page:
https://github.com/Calysto/calysto\_hy. Note, that Calysto tools does
not contain Calysto Hy kernel. That's why Hy kernel for Jupyter Notebook
needs to be installed also.

Hy is selected for a core Logic implementation language because its
syntax resembles mathematical and logic notation in many ways, mostly
the use of parentheses in the native syntax and no separate parser is
needed for that purpose. Not that the parser implementation was not
tried for three different languages before the selection:
http://plcparser.herokuapp.com/

With macro support Hy can be extended pretty easily to satisfy
notational needs for this project.

After installations you should be ready to print environment information
running the following Hy code:

.. code:: python

    (import hy sys)
    (print "Hy version: " hy.__version__)
    (print "Python" sys.version)


.. parsed-literal::

    Hy version:  0.12.1
    Python 3.5.2 |Anaconda custom (64-bit)| (default, Jul  5 2016, 11:41:13) [MSC v.1900 64 bit (AMD64)]
    

HyLogic module
~~~~~~~~~~~~~~

Finally you need to retrieve HyLogic module from GitHub:
https://github.com/markomanninen/hylogic. If you run current Notebook
document from the module directory, then you should be fine to import
necessary macros.

Import main macros
^^^^^^^^^^^^^^^^^^

.. code:: python

    ; require macros and import functions and variables
    (require (hylogic.macros (*)))
    (import [hylogic.macros [*]])
    ; NL for newlines
    (setv NL "\r\n")

Note: If all you need is a command line (console) interface, then you
don't actually need Jupyter Notebook and Calysto. Python, Hy, and
``HyLogic`` module are basic prerequisites. By
`downloading <https://github.com/markomanninen/hylogic>`__ and placing
provided ``Hyffix`` and ``HyLogic`` directories to your script root, you
can get ``HyLogic`` running even on Andoid with
`Termux <https://termux.com/>`__!

`Hyffix <https://github.com/markomanninen/hyffix>`__ is used to support
infix, prefix and affix notation plus provide operator precedence
functionality.

Propositional logic
-------------------

.. raw:: html

   <hr/>

This documentation will provide a lot of introductionary material for
understanding `concepts of
logic <https://www.ics.uci.edu/~alspaugh/cls/shr/logicConcepts.html>`__,
not just how to use ``HyLogic`` module. Main motivation is to provide a
computational playground for studying logic, testing logical clauses and
automated deduction. See:
https://en.wikipedia.org/wiki/Automated\_theorem\_proving and
https://en.wikipedia.org/wiki/Automated\_proof\_checking.

Symbols
~~~~~~~

Propositional constants:

-  ⊤ (True / 1)
-  ⊥ (False / 0)

Basic axioms and theorems
~~~~~~~~~~~~~~~~~~~~~~~~~

-  Identity :math:`P` = :math:`P`
-  Negation ¬⊤ = ⊥ and ¬⊥ = ⊤
-  Double negation ¬¬⊤ = ⊤
-  All well defined statements are true (explicit metalogical axiom)

The last axiom may look odd at the moment, but is clarified later on the
`Semantical notes <#Semantical-notes>`__ section.

Propositions
------------

Propositional variables are created with ``defproposition``,
``defpropositions``, ``defproposition*``, and ``defpropositions*``
macros. The last two macros also creates a negated propositional
variable to reduce some repetitive work. In ``HyLogic`` a proposition
consists of one mandatory and two optional parameters:

Mandatory:

1) A propositional variable that is usually denoted by a capital letter
   like :math:`P`, :math:`Q`, and :math:`R`. Often small letters are
   used too but we have reserved small letters for predicate variable
   names. But it is really up to you, what letters to use. You can use
   multi-character symbols too. For example :math:`VaR!` is a proper
   symbol name as well. Using commonly used variable names and
   conventions improves readability and understandability of the logic
   expressions however. A propositional variable is also called a
   `sentential
   variable <http://mathworld.wolfram.com/SententialVariable.html>`__.

Optional (statement):

2) A truth value that is either :math:`True` or :math:`False`. Default
   is :math:`True`. A truth value can also be defined by using the
   number :math:`1` for :math:`True` and the number :math:`0` for
   :math:`False` or by using constant symbols :math:`⊤` and :math:`⊥`
   respectively. Note that in some `logic
   systems <https://en.wikipedia.org/wiki/Three-valued_logic>`__
   :math:`⊥` may be used for "unknown" rather than :math:`False`.

3) A sentence that is a literal representation of the proposition such
   as the phrase "Today is Tuesday". Default is an empty string ("").
   Althought in ``HyLogic`` it doesn't really matter what is the content
   of the sentence, in practice we urge to find out
   `complementizer <https://en.wikipedia.org/wiki/Complementizer>`__
   from the written natural text. It means that in the sentence there
   should be a clear situational condition mentioned. If there is a
   `state of
   affair <https://en.wikipedia.org/wiki/State_of_affairs_(philosophy)>`__
   in the sentence like "A is B" then it becomes a truth-maker and
   consequently we are able to transfer it to a proposition, which then
   is a truth-bearer.

So the format of the macro (``defproposition``, ``defpropositions``,
``defproposition*``, ``defpropositions*``) to initialize a proposition
in ``HyLogic`` is the following:

``(macro symbol &optional [truth-value True] [sentence ""])``

Example 1.1
^^^^^^^^^^^

Let us first define a proposition variable :math:`P` by using
``defproposition`` macro and output it:

.. code:: python

    (defproposition P)
    (print P)


.. parsed-literal::

    P=True
    

Note, how truth value is set to :math:`True` by default. It is
recommended that the truth value is set to :math:`True` for statements
because interpretation of the arguments may get trickier if
:math:`False` is used as we can see from the Example 1.3.

Example 1.2
^^^^^^^^^^^

With ``defpropositions`` marco you can create multiple proposition
variables at once:

.. code:: python

    (defpropositions P Q R)
    (print P Q R)


.. parsed-literal::

    P=True Q=True R=True
    

It is possible to define only simple proposition variables with the mass
creation ``defpropositions`` and ``defpropositions*`` macros. That is,
you cannot give the truth value and the sentence on them. But on the
other hand, it is possible to change the truth value and the sentence
via object properties afterwards.

Next we will change the truth value of the created proposition :math:`P`
to :math:`False`, plus give the literal meaning (sentence) for the
proposition :math:`Q`:

.. code:: python

    ; alter the truth value of the proposition
    (setv P.truth-value False)
    ; set the literal sentence of the proposition
    (setv Q.sentence "This proposition is true")
    ; output modified propositions
    (print P)
    (print Q)


.. parsed-literal::

    P=False
    Q<This proposition is true>=True
    

Example 1.3
^^^^^^^^^^^

Let us then redefine two propositional variables :math:`P` and :math:`Q`
and their negations :math:`¬P` and :math:`¬Q` by using a special
``defproposition*`` macro. Now we will utilize the full parameter set by
also giving the specific truth value and the literal sentence:

.. code:: python

    (defproposition* P False "Today is Tuesday")
    (defproposition* Q True "John will go to work")

Output propositions:

.. code:: python

    (print P NL ¬P)
    (print Q NL ¬Q)


.. parsed-literal::

    P<Today is Tuesday>=False 
     ¬P<Today is Tuesday>=True
    Q<John will go to work>=True 
     ¬Q<John will go to work>=False
    

From the output we find each proposition and their negation represented
in a string format that distinguishes all three aspects of the
proposition, namely the symbol, the literal representation, and the
truth value of the proposition.

Semantical notes
~~~~~~~~~~~~~~~~

Maybe a small explanation here is in place because understanding the
basic components of the propositional logic requires the understanding
of the common convention on how propositional logic works and how it is
represented in a written or a spoken format.

When we define the proposition :math:`P` to mean "Today is Tuesday" and
to be :math:`False`, the following happens. We define that the symbol
:math:`P` denotes the sentence "Today is Tuesday" in natural human
language. We also define that the truth value of the statement is
:math:`False`. Thus we *could* understand the proposition :math:`P` to
say something like "Today is not Tuesday" or maybe even something like:
"Today is Tuesday", but that the statement is not true!

There is a possible pitfall in these expressions. Strictly speaking, the
proposition :math:`P`, as an object in ``HyLogic``, is just stating that
it has the sentencial property which value is "Today is Tuesday" and it
has the truth value which is :math:`False`. And **that statement is
metalogically true** because the proposition object has been stored in
the computer memory in that state.

The last part is important. We have to rely on the top-most metalogical
axiom that all statements, as they are expressed, are invariantly true.
Also, we are not trying to determine if it is really Tuesday today. In
some sense, logic is not meant to find out truth from the world, but to
help to follow logical steps to determine the consequence of the
predefined true statements. Given the assumptions are true, and logical
rules are followed, then we can count on that the consequence is true
too. In our example we defined :math:`P` to be :math:`False` and then we
will deduce the rest of the argumentation according to that definition.

However, the negation of the proposition :math:`P`, which is automaticly
generated by the ``defproposition*`` macro, is :math:`¬P` (read: not
:math:`P`). By literal representation it could be written: "It is not
the case that Today is Tuesday". ``HyLogic`` module doesn't try to
formulate literal representations of the negated sentences. Module just
formulates negations by prepending :math:`¬` symbol to the propositional
variable and switching the truth value to its opposite. Sentence is left
intact.

The truth value of the negation of :math:`P` in our example is
:math:`True` because the original :math:`P` was defined to be
:math:`False` and because we defined negation to work such way in the
basic axioms and theorems.

Truth-bearer in action
~~~~~~~~~~~~~~~~~~~~~~

Because initialized proposition P is a truth-bearer, thus it has the
truth value, either :math:`True` or :math:`False`, we can ask for it.
There are several ways of doing it, because Hy language (backed up with
Python) and HyLogic (including Hyffix) provides a large core of
functions.

Example 1.4.1
^^^^^^^^^^^^^

Let us use equality comparison function to compare if :math:`P` is
:math:`True` by Hy way:

.. code:: python

    (= P True)




.. parsed-literal::

    False



Because a proposition object contains a truth-value property, we could
achieve and compare it directly too in Hy code:

.. code:: python

    ; is the truth-value of P True?
    (if (= P.truth-value True) 
        ; if it is, then
        (print "Yes, it is!") 
        ; else
        (print "No, it is not!"))


.. parsed-literal::

    No, it is not!
    

Above notation is so called prefix or Polish notation which is common in
Lisp languages. ``Hyffix`` module, that is included in ``HyLogic``,
provides infix as well as more exotic affix notation support. ``Hyffix``
module provides ``deffix`` macro that you can use for infixed logical
expressions. Alternatively same can be achieved by ``#$`` macro
shorthand.

In the following example equivalence operator :math:`≡` is used to find
out if proposition :math:`P` is either :math:`True` or :math:`False`.
Other operators, or connectives as they are called in logic, are fully
listed in the `Formulas <#Connectives>`__ section.

Example 1.5
^^^^^^^^^^^

Using ``deffix`` macro:

.. code:: python

    ; P is equivalent to ⊤ (True)?
    (deffix P ≡ ⊤)




.. parsed-literal::

    False



Note, that we are kind of "asking" if :math:`P` is :math:`True`, but in
reality we are passing :math:`P` and :math:`⊤` to the equality function,
which determines that :math:`P`, that is :math:`False`, is not same as
:math:`True`. Thus result is :math:`False`.

Example 1.6
^^^^^^^^^^^

Using ``deffix`` macro shorthand to achieve similar comparison, but this
time we are comparing :math:`P` to :math:`False`:

.. code:: python

    ; P is equivalent to ⊥ (False)?
    #$(P ≡ ⊥)




.. parsed-literal::

    True



.. raw:: html

   <blockquote>

Note, that in ``deffix`` macro, ``=`` is a variable assignment function
and it will change the value of propositions instead of comparison. This
behaviour may change in the future...

.. raw:: html

   </blockquote>

Example 1.7
^^^^^^^^^^^

In this example we will test, if double negation of the proposition
:math:`P` is equivalent to :math:`P`:

.. code:: python

    ; P is equivalent to not not P (double negation)?
    #$(P ≡ (¬(¬P)))




.. parsed-literal::

    True



Double negation version of the proposition symbols are not generated by
``defproposition*`` macro. Just single negation variables are generated.
Thus we can't use ``¬¬P``, but should use either ``(¬ ¬P)`` or
``(¬(¬P))``. One could also utilize ``defproposition`` macro and
generate double negated propositions in the following manner:

.. code:: python

    (defproposition ¬¬P False "Today is Tuesday")
    (print ¬¬P)
    #$(P ≡ ¬¬P)


.. parsed-literal::

    ¬¬P<Today is Tuesday>=False
    



.. parsed-literal::

    True



As said before, the proposition variable symbol can be anything, not
only single letters. In the above example negation symbol has no
independent meaning or functionality. But, if negation symbol is used by
alone, it actually refers to the unary boolean operation, contra to
other connectives, which are n-ary binary operators.

Resolution of the famous paradox
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At first glance, the separate mutable truth value may feel unnecessary
and confucing. Why should we reassert, that "Today is Tuesday" is
:math:`True`, because the truthness is already stated in the sentence?
Separation is really the key to prevent "real" paradoxes occur in the
classical logic. Take for example the famous variation of the `Liar's
Paradox <http://mathworld.wolfram.com/LiarsParadox.html>`__:

.. raw:: html

   <blockquote>

"This sentence is false"

.. raw:: html

   </blockquote>

`Eubulides <http://mathworld.wolfram.com/EubulidesParadox.html>`__, who
formulated it in the fourth century BC, said that if *that* sentence, or
proposition, is true, then *it* can't be true, because *it* says *it* is
false, hence the paradox. Paradox means that the given clause is both
true and false at the same time, or neither one, or that the truthness
of the statement changes mutually. So we can't decide which one it is,
true or false. In reality, the paradox comes from the confusion of the
references of the properties of the proposition. That's why *it* was
written in italics. References are often ambiguous in a written
language.

Model theory
^^^^^^^^^^^^

In HyLogic, the sentence itself doesn't define or hold the truth value
of the proposition. The truth value and the sentence are properties of
the proposition, as is the selected symbol too, for example :math:`P`.
For the practical purposes we have modelled that the proposition is an
object with three properties. We can describe the set of proposition
objects :math:`x` having :math:`Symbol`, :math:`TruthValue`, and
:math:`Sentence`, latter two having no mutable :math:`Relation` with
this notation:

.. math::


   \mathbb{S} = \{x \space | \space Symbol(x) ∧ ¬Relation(TruthValue(x), \space Sentence(x))\

Thus we can do two clarifying things:

a) to say that the proposition symbolized with :math:`P` with a sentence
   "This sentence is false" has the truth value :math:`True`

b) to use only the alternative symbol, instead of the sentence, and say
   that the proposition :math:`P` has the truth value :math:`True`

Now, it becomes apparent that what we try to define in the Liar's
Paradox is that :math:`P` is :math:`True`. There is no contradiction or
paradox in this representation. Whatever is stated in the sentence of
proposition :math:`P`, it does not affect to the truth value of the
statement. The truth value is a separate and an independent property
(attribute) from the sentence. Moreover, the truth value doesn't have a
mutable relation to the sentence, just to the overall state of the
proposition. This can be properly presented by a `model
theory <https://plato.stanford.edu/entries/model-theory/>`__ and is
clearly emphasized in the `semantic theory of
truth <https://en.wikipedia.org/wiki/Semantic_theory_of_truth>`__.

No self-references, please
^^^^^^^^^^^^^^^^^^^^^^^^^^

It is also easy to see that as a logical statement, the sentence "This
proposition is false" is not well defined because it does not really
contain a clear state of affair for the proposition. To formulate it to
logic language it would become "This proposition" is :math:`True`. But
then "This proposition" does not have a truth claim as we would expect.
Compare to similar "Today is tuesday" is :math:`True`, which makes clear
claim on the sentence. "Today is Tuesday" tries to make the truth. "This
proposition" phrase is not a truth-maker and doesn't really fit for
propositional statement. Again, not that it would have any effect in
``HyLogic``, where the sentence could very well be just an empty string!

Finally, according to basic axioms, all statements are true. This
requirement prevents the possibility of the infinite truth value
assigment, that is, the self-referencial mutability of the truth value.
Together these axioms prevents paradoxes to occur in HyLogic, or
classical logic more generally. Solution has familiar identities,
because we designed three properties on a proposition model
categorically similar to Kleene's strong three-valued logic. And we
designed the lowest level of hierachy with metalogical "All statements
are true" that is also similar to Russell's and Tarski's solutions of
paradoxes. Plus there is a reference to Gödel's first incompleteness
theory, because the unique metalogical axiom, really just a model in a
computer memory, is the necessary axiomatic system outside of the logic
system itself.

Althought, this may sound promising, there is still "the million dollar"
problem open:

.. raw:: html

   <blockquote>

The idea is that whatever semantic status the purported solution claims
the liar sentence to have, if we are allowed freely to refer to this
semantic status in the object language, we can generate a new paradox.

.. raw:: html

   </blockquote>

https://plato.stanford.edu/entries/self-reference/

Self-references, yes!
^^^^^^^^^^^^^^^^^^^^^

Proposed logic system does not invoke self-references in theory. But the
language platform, Hy in this question, does not prevent of using
self-references and mutate the truth-value. It is easy to make an
infinite loop and demonstrate that situation.

Let us first initialize the ostensible paradoxical proposition:

.. code:: python

    (defproposition P True "This proposition is False")

In the language level we can find a contradiction already. Sentence says
that *this* proposition is :math:`False`, but we have defined the
proposition :math:`P` to be :math:`True`. Sentence does not know the
truth value nor it can change the truth value. Furthermore, it has no
functionality to refer to itself. Or if it would have, then where would
it refer? If to the sentence itself, then what part of it? Would it say
"False" is "False"? Or would the sentence refer to the proposition, or
to the truth value of the proposition? The sentence is really dummy
about that since it is just a description for the proposition, nothing
more.

But let us assume that the sentence could change the value of the
proposition and then the proposition would change the value of sentence.
Following code should illustrate it:

.. code:: python

    (if (= P.truth-value False)
        (do
          (setv P.sentence (% "This proposition is %s" (str P.truth-value)))
          (print P)))
    
    (if (= P.truth-value True)
        (do
          (setv P.sentence (% "This proposition is %s" (str P.truth-value)))
          (print P)))


.. parsed-literal::

    P<This proposition is True>=True
    



.. parsed-literal::

    'This proposition is True'



After demonstrating this, we will highly recommend to use the default
truth value :math:`True` in propositions to simplify things. And not to
change the value after initialization.

But due to automated factorization of the arguments and proofs, and
demonstration purposes, we will diverge from that rule in the following
examples anyway.

Formulas
--------

.. raw:: html

   <hr/>

Connectives
~~~~~~~~~~~

The list all connectives to operate with the propositional and the
first-order logic:

.. code:: python

    (for [[f data] connectives]
      (print (last data) "\t" (first data) "    \t" (second data)))


.. parsed-literal::

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
    

Argumentation
-------------

.. raw:: html

   <hr/>

Introducing ``defargument``, ``defpremise``, and ``defconclusion``
macros.

In a propositional logic, an argument is a set of premises following
each other where the final premise is distinguished and called the
conclusion. This is also called deductive reasoning where the more
specific conclusion is reasoned from the more general premises or
assumptions. In ``HyLogic``, an argument is created by ``defargument``
macro which returns an object that can be assigned to a variable for
further interaction. ``Defargument`` takes a serie of premises defined
by ``defpremise`` macro plus the final conclusion defined by
``defconclusion`` macro. Each
`premise <https://en.wikipedia.org/wiki/Premise>`__ is a set of
`formulated
propositions <https://en.wikipedia.org/wiki/Propositional_formula>`__
and `axioms <https://en.wikipedia.org/wiki/Axiom>`__ constructed by
known `inference
rules <https://en.wikipedia.org/wiki/Rule_of_inference>`__.

Example 2.1
^^^^^^^^^^^

The next example is meant to demonstrate argumentation process in
``HyLogic``. It is the famous `modus
ponens <https://en.wikipedia.org/wiki/Modus_ponens>`__ implication
elimination rule. But there is a small twist that should stress the need
of accuracy on small details in logical reasoning.

For the Modus Ponens argument, we will first define the implication
premise "if P is True, then Q is True". Then we will define the second
premise "P is True" and finally the conclusion "Q is True". Symbolically
and shortly this is denoted with the expression: :math:`P → Q, P ⊦ Q`.

.. code:: python

    (setv a 
      (defargument 
        ; if the proposition "Today is Tuesday" (P) is True
        ; then the proposition "John will go to work" (Q) must be True as well
        ; note that this does not set Q True, but just gives a rule
        (defpremise P → Q)
        ; but we stated earlier on example 1.3 that the proposition "Today is Tuesday" (P) is False.
        ; so how should we deal with it now?
        (defpremise P)
        ; well therefore, both <John will go to work>=True 
        ; and <John will go to work>=False should be concluded as a valid argument
        (defconclusion Q)))
    ;(print a)

It means that if Today is Tuesday is False OR "John will go to work" is
True, then premise is True

Thus if "Today is not Tuesday" then "John will go to work" or "John will
not go to work"

Moreover, because P is False, it tells nothing about Q so we can accept
both True and False statements of Q

Validation of the argument form
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code:: python

    (defproposition* P False "Today is Tuesday")
    (defproposition* Q True "John will go to work")
    
    (print
      (deffix P) (deffix Q) NL
      "If P, then Q =" (deffix (P → Q)))


.. parsed-literal::

    P<Today is Tuesday>=False Q<John will go to work>=True 
     If P, then Q = True
    

.. code:: python

    (defn gs [s] (if (= s True) s.symbol (+ "¬" s.symbol)))
    
    (print (gs P) " → " (gs Q) "\t\t\t" (deffix P → Q))
    (print (gs P) "\t\t\t\t" (deffix P = True))
    ;(print "(" (gs P) " → " (gs Q) ") ∧ " (gs P) "\t\t" (deffix (P → Q) ∧ P))
    (print (gs Q) "\t\t\t\t" (deffix Q = True))
    (print "(((" (gs P) " → " (gs Q) ") ∧ " (gs P) ") ↔ " (gs Q) ")\t" (deffix (((P → Q) ∧ P) → Q)))


.. parsed-literal::

    ¬P  →  Q 			 True
    ¬P 				 False
    Q 				 True
    ((( ¬P  →  Q ) ∧  ¬P ) ↔  Q )	 True
    

.. code:: python

    (defproposition* P)
    (defproposition* Q)
    
    (print (deffix (¬P ∨ Q) ∧ (¬P → Q)))
    (print (deffix P = True))
    (print (deffix ¬Q = False))
    (print (deffix ((((¬P ∨ Q) ∧ (¬P → Q)) ∧ P) → ¬Q)))


.. parsed-literal::

    True
    True
    True
    False
    

.. code:: python

    (print P)
    (print Q)


.. parsed-literal::

    P=True
    Q=True
    

Example 2.2
^^^^^^^^^^^

Slightly more complicated argument is shown next.

.. code:: python

    (defproposition P True "It is raining")
    (defproposition Q True "It is cold outside")
    (defproposition R False "I'm indoors")
    
    (print P NL Q NL R)


.. parsed-literal::

    P<It is raining>=True 
     Q<It is cold outside>=True 
     R<I'm indoors>=False
    

.. code:: python

    ; set up argument inference rules
    (setv a 
      (defargument 
        ; If "it is raining and it is cold outside" then "I'm indoors"
        (defpremise (P ∧ Q) → R)
        ; It is raining and it is cold outside
        (defpremise (P ∧ Q))
        ; Therefore, I'm indoors
        (defconclusion R)))

.. code:: python

    (print a)


.. parsed-literal::

    
      (P ∧ Q) → R
      (P ∧ Q)
    --------------
    ∴ R
    
    

.. code:: python

    (print
      (deffix P) (deffix Q) (deffix R) NL
      "If P and Q, then R =" (deffix (P ∧ Q) → R))


.. parsed-literal::

    P<It is raining>=True Q<It is cold outside>=True R<I'm indoors>=False 
     If P and Q, then R = False
    

De Morgan's laws
~~~~~~~~~~~~~~~~

https://en.wikipedia.org/wiki/De\_Morgan%27s\_laws

.. code:: python

    (defpropositions P Q)

The negation of conjunction:

.. code:: python

    (deffix (¬ (P ∧ Q)) → (¬P ∨ ¬Q))




.. parsed-literal::

    True



The negation of disjunction:

.. code:: python

    (deffix (¬ (P ∨ Q)) → (¬P ∧ ¬Q))




.. parsed-literal::

    True



First-order logic
-----------------

.. raw:: html

   <hr/>

Quantifiers, predicates, variables, sets
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Universal quantifier (∀)
^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: python

    (tuple (range -9 0))




.. parsed-literal::

    (-9, -8, -7, -6, -5, -4, -3, -2, -1)



.. code:: python

    ;(∀x∈ℕ>0∧<10)(x>0)
    ; (all (map (fn (x) (x > 0)) (range 1 10)))
    (∀ (x) (x > 0) (range 1 10)) ; all items [1 ... 9] are greater than 0?




.. parsed-literal::

    True



.. code:: python

    ;all(map(lambda x: x > 0, range(1 10)))
    (all (map (fn (x) (> x 0)) (range 1 10)))




.. parsed-literal::

    True



Example 3.1
^^^^^^^^^^^

.. code:: python

    (∀ (x y) ((x > 0) ∧ (y < 0)) (range 1 10) (range -9 1)) ; test this case




.. parsed-literal::

    True



Example 3.2
^^^^^^^^^^^

.. code:: python

    (∀ (x) (∀ (y) ((x > 0) ∧ (y < 0)) (range -9 0)) (range 1 10))




.. parsed-literal::

    True



Example 3.3
^^^^^^^^^^^

.. code:: python

    (∀ (x) ((x > 0) ∧ (∀ (y) (y < 0) (range -9 0))) (range 1 10))
    ;(macroexpand `(∀ (x) ((x > 0) ∧ (∀ (y) (y < 0) (range -10 -1))) (range 1 10)))




.. parsed-literal::

    True



.. code:: python

    ; Every whole number is divisible by 1 and itself.
    ;(∀x)(Div(x,x)∧(Div(1,x))
    
    ;(defoperator mod [x y] (% x y))
    (defoperator mod0? [x y] (zero? (% x y)))
    (defoperator Div [x y] (mod0? x y))
    
    (setv domain-set [1 2 3])
    
    (∀ (x) ((Div x 1) ∧ (Div x x)) domain-set)




.. parsed-literal::

    True



.. code:: python

    (setv DX [1 1]
          DY [-1 -2])
    ; all[any[1-1=0 1-2=-1] any[1-1=0 1-2=-1]]
    (∀ (x) (∃ (y) (x + y = 0) DY) DX)




.. parsed-literal::

    True



.. code:: python

    ; all[1-1=0 1-2=-1 1-1=0 1-2=-1]
    (∀ (x y) (x + y = 0) DX DY)




.. parsed-literal::

    False



Existential quantifier (∃)
^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: python

    (∃ (x) (x < 1) (range 0 10)) ; is at least one item of [0 ... 9] smaller than 1?




.. parsed-literal::

    True



.. code:: python

    ; (∃x)((¬Div(x,x))∨(¬Div(1,x))
    (∃ (x) ( (¬ (x mod0? 1) ) ∨ (¬ (x mod0? x) ) ) domain-set)




.. parsed-literal::

    False



.. code:: python

    ; any[1-1=0 1-2=-1 1-1=0 1-2=-1]
    (∃ (x y) ((x > 0) ∧ (y < 0)) DX DY)




.. parsed-literal::

    True



.. code:: python

    ; any[all[1-1=0 1-2=-1] all[1-1=0 1-2=-1]]
    (∃ (x) (∀ (y) (x + y = 0) DY) DX)




.. parsed-literal::

    False



Truth tables
------------

.. raw:: html

   <hr/>

.. code:: python

    (truth-tables-html 2 cimp?)




.. raw:: html

    <table><thead style='background-color:#dcdccc'><tr><th colspan=3>Converse implication (cimp?)</th></tr></thead><tbody><tr><td style='text-align:center'>0</td><td style='text-align:center'>0</td><td style='background-color:#7f9f7f'>True</td></tr><tr><td style='text-align:center'>0</td><td style='text-align:center'>1</td><td style='background-color:#cc9393'>False</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>0</td><td style='background-color:#7f9f7f'>True</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>1</td><td style='background-color:#7f9f7f'>True</td></tr></tbody></table>



.. code:: python

    (truth-tables-html 2 eqv?)




.. raw:: html

    <table><thead style='background-color:#dcdccc'><tr><th colspan=3>Equivalence (eqv?)</th></tr></thead><tbody><tr><td style='text-align:center'>0</td><td style='text-align:center'>0</td><td style='background-color:#7f9f7f'>True</td></tr><tr><td style='text-align:center'>0</td><td style='text-align:center'>1</td><td style='background-color:#cc9393'>False</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>0</td><td style='background-color:#cc9393'>False</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>1</td><td style='background-color:#7f9f7f'>True</td></tr></tbody></table>



.. code:: python

    (truth-tables-html 2 xnor?)




.. raw:: html

    <table><thead style='background-color:#dcdccc'><tr><th colspan=3>Nonexclusive or (xnor?)</th></tr></thead><tbody><tr><td style='text-align:center'>0</td><td style='text-align:center'>0</td><td style='background-color:#7f9f7f'>True</td></tr><tr><td style='text-align:center'>0</td><td style='text-align:center'>1</td><td style='background-color:#cc9393'>False</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>0</td><td style='background-color:#cc9393'>False</td></tr><tr><td style='text-align:center'>1</td><td style='text-align:center'>1</td><td style='background-color:#7f9f7f'>True</td></tr></tbody></table>



Venn diagrams
-------------

.. raw:: html

   <hr/>

.. code:: python

    ;(venn-diagram)

.. code:: python

    (defn odd? [x &rest y]
      (= 1 (% (+ x (sum y)) 2)))
    
    (deffix (odd? 1 1 1))




.. parsed-literal::

    True



The `MIT <https://choosealicense.com/licenses/mit/>`__ License
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Copyright © 2017 Marko Manninen
