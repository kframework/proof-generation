---
geometry: margin=2cm
---

\newcommand{\limplies}{\to}
\renewcommand{\phi}{\varphi}


Matching logic proof format
===========================

This is a proposed matching logic proof format.

## Relation to Metamath

Note that this language heavily based on the metamath format for compressed proofs.
Besides being a binary rather than ASCII encoding, there are two major changes.

1.  We use the same mechanism for constructing terms and proofs, allowing better
    compression.
2.  We allow emmitting multiple proofs from the same representation. This allows
    us to represent lemmas and compression uniformly.
    That is, we can store the entire contents of a single metamath file in this format,
    rather than just the proof of a single lemma.

## Relation to postfix notation/RPN

The format may be viewed as a generalization
of postfix notation (incidentally also called Lukaseiwicz notation),
for an expression computing the conclusion of a proof.

We also allow marking subexpressions (i.e. either proofs or patterns) for reuse. This
allows us to represent lemmas, and compactly representing configurations and notation.

(This needs input from ZK folk.) Finally, we allow marking constructed proofs
as public. This serves two purposes. First, it allows us to publish lemmas
that may be reused in other proofs. Second, it allows us to publish the main
result proved by the proof.


## As a stack machine

It may also be viewed language interpreted using a stack machine.
This stack machines constructs terms---either patterns or proofs. We treat
patterns and proofs uniformly---at an abstract level, they are both terms we
must construct, with particular well-formedness criteria. It is intended for the
most part, that **the verifier only needs to keep proved conclusions in
memory**.


## Goals:

-   No upfront parsing cost.
-   Easily verifiable using ZK.
-   Low memory usage.
-   Composability.


## Non-goals:

-   Parallization: I have not been thinking explicitly about parallel verification of this format,
    because I expect parallization to happen by composing units of this format into larger proofs.
    Even so I think with some additional metadata, we could make
    this format parallizable.

-   Human readability: We aim to be a simple binary format. To become human
    readable, we expect the user to run a secondary program to pretty-print the
    proof. Note that symbols, lemmas, and notation do not have names.


Terms
=====

As mentioned previously, we may view this format as a language for constructing
terms that meet particular well-formedness criteria. Let us first enumerate
those terms, in a python-esque pseudocode.

`Term`s are of two types, `Pattern`, and `Proof`.
Every `Term` has a well-formedness check.
Every `Proof` has a conclusion.

```python
abstract class Term:
    abstract def well_formed:
        ...

abstract class Pattern(Term):
    def well_formed():
        # Fails if any two MetaVars with the same id has
        # different meta-requirements
        # MetaVars are introduced later.
    ...

abstract class Proof(Term):
    abstract def conclusion:
        ...
```

`Pattern`s
----------

There are two classes of `Pattern`,
the expected concrete constructors for matching logic patterns,
and a representation for various "meta" patterns.

### Standard patterns

```python
class Symbol(Pattern):
    name: uint32

class SVar(Pattern):
    name: uint32

class EVar(Pattern):
    name: uint32

class Implication(Pattern):
    left: Pattern
    right: Pattern

class Application(Pattern):
    left: Pattern
    right: Pattern

class Exists(Pattern):
    var: EVar
    subpattern : Pattern

class Mu(Pattern):
    var: SVar
    subpattern : Pattern

    def well_formed():
        return super.well_formed()
           and subpattern.var_occurs_positively(var)
```

### Meta-patterns

Meta-patterns allow us to represent axiom- and theorem-schemas through the use
of metavariables:

```python
class MetaVar(Pattern):
    name: uint32

    # Meta-requirements that must be satisfied by any instantiation.
    fresh: list[EVar | SVar]        # variables that must not occur in an instatiation
    positive: list[SVar]            # variables that must only occur positively in an instatiation
    negative: list[SVar]            # variables that must only occur negatively in an instatiation
    application_context: list[EVar] # Variables that must only occur as a hole variable in an application context.
```

Each `MetaVar` has a list of requirements that must be met by any instantiation.
These may also be used by the well-formedness checks for `Proof`s.

We also need to represent substitutions applied to `MetaVar`s.

```python
class ESubst(Pattern):
    pattern: MetaVar
    var: EVar
    plug: Pattern

class SSubst(Pattern):
    pattern: MetaVar
    var: SVar
    plug: Pattern
```


`Proof`s
--------

### Axiom Schemas

Axiom schemas are `Proof`s that do not need any input arguments.
They may use `MetaVar`s to represent their schematic nature.

```python
class Lukaseiwicz(Proof):
    def conclusion():
        phi1 = MetaVar('phi1')
        return Implication(Implication(Implication(MetaVar(phi1) , ...)...)...)

class Quantifier(Proof):
    def conclusion():
        x = EVar('#x')
        y = EVar('#y')
        phi = MetaVar('phi', fresh=[y])
        return Implication(ESubst(phi, x, y), Exists(x, phi))

class PropagationOr(Proof):
    def conclusion():
        hole = EVar('#hole')
        C = MetaVar(application_context=(EVar('#hole'),))
        phi1 = MetaVar('#phi1')
        phi2 = MetaVar('#phi2')
        return Implication(ESubst(C, or(phi1, phi2), hole), or(ESubst(C, phi1, hole), ESubst(C, phi2, hole)))

...
```


### Meta Variable Instantiation

Using a single rule of meta inference, we may instantiate metatheorems.
This allows us to prove theorem schemas, such as $\phi \limplies \phi$.

```python
class InstantiateSchema(Proof):
    subproof : Proof
    metavar_id: uint32
    instantiation: Pattern

    def well_formed():
        # Fails if the instantiation does not meet the
        # disjoint/positive/freshness/application ctx
        # criterea of the metavar.

    def conclusion():
        return subproof.meta_substitute(metavar, instantiation)
```

We may also use metavariables to represent notation.

```python
class InstantiateNotation(Pattern):
    notation: Pattern
    metavar_id: uint32
    instantiation: Pattern

    def well_formed():
        # Fails if the instantiation does not meet the
        # disjoint/positive/freshness/application ctx
        # criterea of the metavar.

    def conclusion():
        return notation.meta_substitute(metavar, instantiation)
```


### Ordinary inference

```python
class ModusPonens(Proof):
    premise_left: Implication
    premise_right: Pattern

    def conclusion():
        return premise_left.right

    def well_formed():
        assert premise_right == premise_left.left

class Generalization(Proof):
    premise: Implication

    def phi1():
        premise.left
    def phi2():
        premise.right

    def conclusion():
        return Implication(ESubst(MetaVar(phi), EVar(x), EVar(y)), Exists(EVar(x), MetaVar(phi)))

    def well_formed():
        assert EVar(x) is fresh in phi1()
...
```

Instructions and semantics
==========================

Each of these instructions checks that the constructed `Term` is well-formed before pushing onto the stack.
Otherwise, execution aborts, and verification fails.

*   Supporting:

    `List n:uint32`
    : Consume $n$ items from the stack, and push a list containing those items to the stack.

* Variables and Symbols:

    `EVar <uint32>`
    : Push an `EVar` onto the stack.

    `SVar <uint32>`
    : `Push an `SVar` onto the stack.

    `Symbol <uint32>`
    : `Push an `Symbol` onto the stack.

    `MetaVar <uint32>`
    : Consume the first four entries from the stack (corresponding to the meta-requirements),
      and push an `MetaVar` onto the stack.

* Connectives:

    `Implication`/`Application`/`Exists`/`Mu`
    : Consume the first two patterns from the stack, and push an implication/application/exists/mu onto the stack with appropriate argumetns.

* Axiom Schemas

    `Lukaseiwicz`/`Quantifier`/`PropagationOr`/`PropagationExists`/`PreFixpoint`/`Existance`/`Singleton`
    : Push Proof term corresponding to axiom schema onto the stack.

* Meta inference

    `InstantiateSchema <metavar_id:uint32>`
    : Consume a `Proof` and `Pattern` off the stack, and push the instantiated proof term to the stack.

    `InstantiateNotation <metavar_id:uint32>`
    : Consume two `Pattern`s off the stack, and push the instantiated proof term to the stack.

*   Inference rules

    `ModusPonens`/`Generalization`/`Frame`/`Substitution`/`KnasterTarski`
    : Consume one or two `Proof` terms off the stack and push the new proof term.

*   Memory manipulation:

    `Save`
    : Store the top of the stack to the lowest unused index in memory.

    `Load i:uint32`
    : Push the `Term` at index $i$ to the top of the stack.

    `Delete i:uint32`
    : Remove the `Term` at index $i$ from memory. This is not strictly needed,
      but will allow the verifier to use less memory. The memory slot is not considered free.

*   Journal manipulation.

    `Publish`
    : publish the entry at the top of the stack to the journal.

*   Stack manipulation.

    `Pop`
    : Consume the top of the stack. (Do we need this? Probably not.)

Verification
============

The verifier takes two inputs[^1]:

1.  `theory` A file with instructions to construct patterns
    and place them on the stack to represent the theory $\Gamma$.
    This is public.

    All patterns on the stack after running this file are considered axioms.
    Before verification of the proof, these are moved to the first free memory locations (That is, after the notation).

    All patterns placed in memory using the `Save` instruction may be used as notation.
    Note that these patterns are not considered proved, and can only be used to buildother patterns.

    TODO: We should review this. Do we want a specific instruction for publishing notation?

2.  `lemmas`: A file with instructions to construct patterns corresponding the
    lemmas previously proved in other proof files. An aggregation circuit will
    need to check that the theory used by that proof is a subset of the theory
    for the corrent proof.

    All patterns on the stack after running this file are considered proved lemmas.

    TODO: Should we allow notation from these as well?
    If we do, composing proofs may get difficult---notation may accumulate
    forcing the checker to use a lot more memory than needed.

3.  `proof`: A file with instructions to construct proofs about the theory.
    This file is private, and should be rolled-up by ZK.

The verifier consumes the theory file. The stack should now only include `Pattern` terms.
These are moved into the initial entries of the memory, as `Proof` terms.
The verifier then consumes the `proof` file and produces a "journal"[^2],
containing a list of instructions to construct the patterns of theorems proved.

[^1]: This needs input from the ZK folk for the exact input mechanism.
[^2]: Using Risc Zero terminology

The verifier state consists of a stack of `Term`s, and
an indexed list of saved `Term`s, called the memory.

Composition
===========

We may compose proofs together, by allowing proofs to reuse results contained in another proofs journal.
A subset of the contents of the journal of a proof $p$ may be included as the input lemmas of another proof $q$,
**so long as** the gamma of $p$ is subset of gamma of $q$.

