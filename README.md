Henk Barendregt: Pure Type System
---------------------------------

<img src="https://henk.groupoid.space/img/Henk%20Barendregt.jpg" height=400>

# Abstract

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

## Syntax

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

## Semantics

### Hierarchy

The hierarchy function computes the universe level of a type constructor (e.g., a function or product type)
by delegating to dep with a configurable mode. In the code, `hierarchy Arg Out -> dep Arg Out (env om hierarchy impredicative)`
uses an environment variable to choose between impredicative (default) and predicative settings,
allowing flexibility in the type system’s universe structure. Formally, Barendregt describes the hierarchy in PTS via the rules R,
where the resulting sort s3 of a product `Πx:A.B` depends on the sorts of A and B: in impredicative CoC,
while in predicative systems, it may lift to a higher universe. He writes, "The choice of hierarchy rule
determines the expressiveness and consistency of the system" (Barendregt, Lambda Calculus: Its Syntax and
Semantics, 1992, p. 567), which the code reflects by parameterizing this choice. He writes, "The choice of
hierarchy rule determines the expressiveness and consistency of the system" (Barendregt, Lambda Calculus:
Its Syntax and Semantics, 1992, p. 567), which the code reflects by parameterizing this choice.

### Star

The star function extracts or validates the numeric level of a universe sort, central to the infinite hierarchy of types.
In the code, `star (star,N) -> N` returns the integer `N` from a universe term `star N` (e.g., \*0, \*1,
while `star S -> error ("universe",\*,S)` errors out for invalid inputs. Formally, Barendregt defines sorts in PTS as a set 
S, such as `{∗,□}` in CoC, or an infinite sequence `\*0 : \*1 : \*2 : ...` in systems with universes, where each 
`**n : **(n+1)`. He states, "Sorts form the backbone of the type hierarchy, with each level governing the types
below it" (Barendregt, Introduction to Generalized Type Systems, 1991, p. 6), and the code’s star function directly
supports this by managing universe indices.

### Equality

The `eq` function tests convertibility between two terms, a key aspect of type checking in PTS.
It checks dependent products for equality by comparing domains and codomains with substitution,
while `eq (app (F1,A)) (app (F2,A2)) -> eq(F1, F2), eq(A1, A2)` handles applications.
Formally, Barendregt defines equality as beta-convertibility: 
`M =_β N` if `M` and `N` reduce to the same normal form. He writes, "Equality in typed
lambda calculi relies on convertibility, ensuring types align under reduction" (Barendregt,
Introduction to Generalized Type Systems, 1991, p. 17), which eq implements via structural
and substitution-based comparison.

### Shift

The shift function adjusts the indices of free variables in a term to account for changes in the binding context,
such as when a term is moved under a new binder (e.g., a lambda or universal quantifier). In the code,
`shift (var (N,I)) N P when I >= P -> var (N,I+1)` increments the index `I` of a variable named `N` by `1`
if I >= P (the cutoff point), while `shift (∀,(N,0)) (I,O) N P` recursively shifts indices
in the input `I` and output `O` of a dependent function type, adjusting `O` under an additional
binder `P+1`. Formally, per Barendregt, shifting (often denoted as an "up" operation) is defined as:
for a term t, the shifted term `t↑_c^d` increases all free variable indices `i≥c` by `d`, where `c`
is the cutoff and `d` is the shift amount (typically 1). Barendregt states, "The operation `t↑_c^d`
is used to avoid capture of variables when substituting under binders" (Barendregt, Lambda Calculus: Its Syntax and Semantics, 1992, p. 49),
ensuring that free variables retain their intended references during term manipulation.

### Substitution

The subst function performs substitution, replacing a variable in a term with another term,
while respecting the binding structure to avoid variable capture. In the code,
`subst (var (N,L)) N V L -> V` replaces a variable with index L matching the
current level with the value `V`, while `subst ((λ,(N,0)),(I,O)) N V L  -> ((λ,(N,0)),(subst I N V L, subst O N shift(V,N,0) L+1))`
substitutes in a lambda term, shifting `V` to adjust for the new binder in `O`.
Formally, Barendregt defines substitution as: for a term `t`, variable `x`, and term `u`,
the substitution `t[x:=u]` replaces all free occurrences of `x` in `t` with `u`,
with indices adjusted to prevent capture by binders. He writes, "Substitution `t[x:=u]`
must ensure that free variables in `u` are not accidentally bound by binders in 
`t`, necessitating a careful adjustment of indices" (Barendregt, Introduction to
Generalized Type Systems, 1991, p. 15), which aligns with the code’s use of shift
within subst to maintain correctness in dependent type systems like the Calculus of Constructions.

### Normalization

The norm function computes the normal form of a term, performing beta reduction and structural
normalization. In the code, `norm (app (F,A)) -> case norm(F) of ((λ,(N,0)),(O,O)) -> norm(subst(O,N,A))`
reduces applications by substituting into lambdas, while `norm (→,(I,O)) -> ((∀,(_,0)),(norm(I),norm(O)))`
rewrites function types as dependent products. Formally, Barendregt defines normalization as reducing a
term to its normal form via beta reduction, where `(λx.M)N→M[x:=N]`, ensuring strong normalization
in systems like CoC. He states, "Normalization guarantees that every typable term has a unique
normal form, critical for consistency" (Barendregt, Lambda Calculus: Its Syntax and Semantics, 1992, p. 62),
which norm achieves through recursive reduction.

### Type Inference

The type function infers or checks the type of a term in a given context, enforcing the PTS typing rules.
In the code, `type (star N) _ -> star (N+1)` assigns each universe its successor, `type ((∀,(N,0)),(I,O)) D -> star hierarchy(star(type(I,D)), star(type(O,[{N,norm(I)}|D])))`
types dependent products, and `type (app (F,A)) D` handles applications by matching function
types and substituting. Formally, Barendregt defines typing in PTS via judgments `Γ ⊢ M : A`,
governed by rules like `Γ⊢Πx:A.B:s3 if Γ⊢A:s1 /\ Γ,x:A⊢B:s2` for products. He notes, "The typing
relation ensures that every term inhabits a sort or type, preserving the hierarchy" (Barendregt,
Lambda Calculus: Its Syntax and Semantics, 1992, p. 568), which type upholds by recursively computing types within the context.

## Artefact

In repository `henk` you may find the following parts of core:

* [Parser](https://github.com/groupoid/henk/blob/main/src/elixir/syntax/morte/om_parse.erl)
* [Type Checker](https://github.com/groupoid/henk/blob/main/src/elixir/typechecker/om_type.erl)
* [Eraser](https://github.com/groupoid/henk/blob/main/src/elixir/extractor/om_erase.erl)
* [Code Extractor](https://github.com/groupoid/henk/blob/main/src/elixir/extractor/om_extract.erl)

Henk ships with different "modes" (spaces of types with own encodings), or "preludes", which
you may find in `lib` directory. They are selectable with `om:mode("normal")`.

#### [Henk Library](https://github.com/groupoid/henk/tree/main/src/elixir/priv/Morte)

```sh
henk.groupoid.space/src/elixir/priv/Morte
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
