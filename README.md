Henk Barendregt: Pure Type System
---------------------------------

<img src="https://henk.groupoid.space/img/Henk%20Barendregt.jpg">

**Henk** languages described first by Erik Meijer and Simon Peyton Jones in 1997.
Later on in 2015 a new implementation of the ideas in Haskell appeared, called Morte.
It used the Böhm-Berarducci encoding of recursive data types into non-recursive terms.
Morte has constants, variables, and kinds, is based only on **П**, **λ** and **apply** constructions,
one axiom and four deduction rules. The Henk language resembles Henk design and Morte implementation.
This language is indended to be small, concise, easily provable, clean and
be able to produce verifiable programs that can be distributed over the networks and compiled at target with safe linkage.

```
$ mix deps.get
$ iex -S mix
```

The Henk Syntax is the following:

```
   <> ::= #option

    I ::= #identifier

    U ::= * < #number >

    O ::= U | I | ( O ) | O O
            | λ ( I : O ) → O
            | ∀ ( I : O ) → O
```

Henk is an implementation of PTS with an Infinite Number of Universes, the pure lambda calculus with dependent types.
It can be compiled (code extraction) to bytecode of Erlang virtual machines BEAM and LING.

Trusted PTS with an Infinite Universes
--------------------------------------

In repository `henk` you may find the following parts of core:

* [Parser](https://github.com/groupoid/henk/blob/main/src/om_parse.erl)
* [Typechecker](https://github.com/groupoid/henk/blob/main/src/om_type.erl)
* [Eraser](https://github.com/groupoid/henk/blob/main/src/om_erase.erl)
* [Code Extractor](https://github.com/groupoid/henk/blob/main/src/om_extract.erl)

Henk ships with different "modes" (spaces of types with own encodings), or "preludes", which
you may find in `lib` directory. They are selectable with `om:mode("normal")`.

#### [normal](https://github.com/groupoid/henk/tree/main/lib/normal)

```sh
henk.groupoid.space/lib/normal/
  ├── Bool
  ├── Cmd
  ├── Eq
  ├── Equ
  ├── Frege
  ├── IO
  ├── IOI
  ├── Lazy
  ├── Leibnitz
  ├── List
  ├── Maybe
  ├── Mon
  ├── Monad
  ├── Monoid
  ├── Morte
  ├── Nat
  ├── Path
  ├── Prod
  ├── Prop
  ├── Sigma
  ├── Simple
  ├── String
  ├── Unit
  └── Vector
```

This is a minimal practical prelude similar to Morte's base library of Gabriella Gonzalez.
It contains common inductive constructions encoded using plain Church (or Böhm-Berarducci if you wish) encoding,
and two basic (co)monadic effect systems: IO (free monad, for finite I/O) and IOI (free comonad,
for infinitary I/O, long-term processes). The generated code is being sewed with
Erlang effects that are passed as parameters to pure functions.

Note: all these folders (modules) are encoded in plain CoC in Henk repository to demonstrate
you the basic principles how things work. Later all these should be written in Per
languages and translated to Henk automatically (if possible). You may think of Henk as the low-level
typed assembler of type theory.

PTS
---

* <a href="https://pure.tue.nl/ws/portalfiles/portal/2039924/256169.pdf">AUTOMATH, a language for mathematics.</a> [Nicolaas Govert de Bruijn]
* <a href="https://home.ttic.edu/~dreyer/course/papers/barendregt.pdf">Lambda Calculi with Types</a> [Henk Barendregt]
* <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a> [Thierry Coquand, Gerard Huet]
* <a href="https://www.cambridge.org/core/services/aop-cambridge-core/content/view/869991BA6A99180BF96A616894C6D710/S0956796800020025a.pdf/introduction-to-generalized-type-systems.pdf">Introduction to Generalized Type Systems</a> [Henk Barendregt]
* <a href="https://www.cse.chalmers.se/~coquand/v1.pdf">Some remarks about Dependent Type Theory</a> [Thierry Coquand]
* <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/henk.pdf">Henk: a typed intermediate language</a> [Erik Meijer, Simon Peyton Jones]
* <a href="https://www.haskellforall.com/2014/09/morte-intermediate-language-for-super.html">Morte: an intermediate language for super-optimizing functional programs </a> [Gabriella Gonzalez]
* <a href="https://henk.groupoid.space/doc/pts.pdf">Henk: Pure Type System for Erlang</a> [Maksym Sokhatskyi]
* <a href="https://henk.groupoid.space/doc/pts_ua.pdf">Система доведення теорем з однiєю аксiомою</a> [Maksym Sokhatskyi]

Credits
-------

* <a itemprop="sameAs" content="https://orcid.org/0000-0001-7127-8796" href="https://orcid.org/0000-0001-7127-8796" target="orcid.widget" rel="me noopener noreferrer" style="vertical-align:top;white-space: nowrap;">Maksym Sokhatskyi <img src="https://orcid.org/sites/default/files/images/orcid_16x16.png"> 🇺🇦</a>
