Henk: Pure Type System in Elixir
=================================

[![Actions Status](https://github.com/groupoid/henk/workflows/ci/badge.svg)](https://github.com/groupoid/henk/actions)
[![Hex pm](http://img.shields.io/hexpm/v/henk.svg?style=flat)](https://hex.pm/packages/henk)

**Henk** is an implementation of a Pure Type System (PTS) with an infinite
universe hierarchy, written in Elixir/OTP.  It was described first by
Erik Meijer and Simon Peyton Jones in 1997, and later inspired the Morte
intermediate language by Gabriella Gonzalez.

<img src="https://henk.groupoid.space/img/Henk%20Barendregt.jpg" height=400>

## Install

```sh
# Linux / WSL
sudo apt install elixir

# macOS
brew install elixir
```

```sh
mix deps.get
mix henk.repl
```

## Modules

### `Henk.Lexer` — `lib/henk/lexer.ex`

Recursive-descent character scanner.  Produces a flat token list with
line/column positions.  Supports:

* Unicode arrows `→` (U+2192) as well as ASCII `->`.
* Haskell/PureScript-style line comments `--`.
* Numeric literals, string literals, identifiers (with primes `'` and
  Unicode subscripts U+2080–U+2089).
* Universe literals `*N` (e.g. `*0`, `*1`).
* Keywords: `module`, `where`, `import`, `data`, `let`, `in`,
  `if`/`then`/`else`, `case`/`of`, `foreign`, `forall`.
* Operator sequences: `=`, `|`, `:`, `::`, and arbitrary operator strings.

Additional lexers for the alternative syntaxes live in
`lib/henk/extensions/`.

### `Henk.Layout` — `lib/henk/layout.ex`

Haskell-style layout rule: converts significant indentation into virtual
`{`, `}`, and `;` tokens so the parser remains context-free.

### `Henk.Parser` — `lib/henk/parser.ex`

Hand-written recursive-descent parser.  Produces `Henk.AST.*` structs.

| Construct | AST node |
|-----------|----------|
| Module header | `AST.Module` |
| Value definition | `AST.DeclValue` |
| `data` declaration | `AST.DeclData` |
| Type signature | `AST.DeclTypeSignature` |
| `foreign` binding | `AST.DeclForeign` |
| Lambda `\x -> e` | `AST.Lambda` / `AST.Lam` |
| Application | `AST.App` |
| Dependent product `∀(x:A) → B` | `AST.Pi` |
| Universe `*N` | `AST.Universe` |
| Variable | `AST.Var` |
| `case … of` | `AST.Case` |
| `let … in` | `AST.Let` |
| List literal | `AST.ListLiteral` |

### `Henk.Desugar` — `lib/henk/desugar.ex`

Transforms the surface AST into core CoC terms:

* `data` declarations are Church/Böhm-Berarducci-encoded into lambda terms.
* Multi-argument lambdas and local `where` clauses are elaborated.
* `let x = e in b` is rewritten as `(\x -> b) e`.
* Pattern-matching `case` is compiled to constructor-elimination terms.
* Collects inductive type constructors into the typechecker environment.

### `Henk.Typechecker` — `lib/henk/typechecker.ex`

Bidirectional type checker for pure CoC with an infinite universe hierarchy.
All state is passed explicitly as `%Henk.Typechecker.Env{}`:

| Field | Purpose |
|-------|---------|
| `ctx` | Typing context `[{name, type}]` |
| `defs` | Global definitions `%{name => term}` |
| `name_to_mod` | Qualified-name to module map |
| `type_constrs` | Constructor → type-name index |
| `foreign_defs` | `%{name => {erl_mod, erl_func}}` |
| `in_progress` | `MapSet` for cycle detection |
| `deadline` | Monotonic-ms normalisation timeout |

Key operations according to Maksym's article:

* **`infer/2`** — type inference for universes, variables, Π-types, λ-terms, applications.
* **`normalize/2`** — full beta-reduction with fuel (50 000 steps) and deadline.
* **`subst/3`** — capture-avoiding substitution.
* **`equal?/3`** — definitional equality via normalisation.

### `Henk.Codegen` — `lib/henk/codegen.ex`

Translates desugared CoC terms into Core Erlang abstract-syntax forms
(`:cerl`), which are then compiled to BEAM bytecode via `:compile.forms/2`.
`foreign` declarations are mapped directly to calls into existing Erlang
modules, letting pure Henk functions interoperate with the OTP ecosystem.

### `Henk.Compiler` — `lib/henk/compiler.ex`

Orchestrates the full pipeline via `compile_module/2`.  Also handles:

* **Implicit Prelude** — `priv/henk/Prelude.henk` is loaded automatically
  for every module that isn't the Prelude itself.
* **Import resolution** — explicit `import Module` and implicit qualified
  references `Module.name` both trigger module loading.
* **Multi-syntax dispatch** — selects the right lexer/parser based on file
  extension (`.henk` → Miranda, `.aut` → AUT-68, no extension → Morte).
* **Module search paths** — `priv/henk/`, `priv/aut-68/`, `priv/morte/`,
  `test/henk/`.

## Syntax

The default (Miranda-like) syntax:

```
<> ::= #option
 I ::= #identifier
 U ::= * <#number>
 O ::= U | I | ( O ) | O O
         | \ ( I : O ) -> O     -- lambda
         | forall ( I : O ) -> O -- pi / forall
```

Alternative syntaxes (`aut-68`, `morte`) are available via the `:syntax`
option to `Henk.Compiler.compile_module/2` or the `:syntax` REPL command.

## Library (`priv/`)

The `priv/aut-68/` directory contains the standard prelude encoded in
Böhm-Berarducci style:

```
Bool  Cmd   Eq    Equ   Frege IO    IOI
Lazy  List  Maybe Mon   Monad Monoid Morte
Nat   Path  Prod  Prop  Sigma String Unit  Vector
```

`priv/henk/` holds the same prelude rewritten in Miranda syntax.

## Reference Models

The Erlang implementation (`src/erlang/`) and the OCaml model (if present
under `src/ocaml/`) served as the reference designs for this Elixir port.
They provide a compact, pure-functional Morte library type checker and
extractor that the Elixir code faithfully reproduces and extends.

## References

* <a href="https://pure.tue.nl/ws/portalfiles/portal/2039924/256169.pdf">AUTOMATH, a language for mathematics</a> [Nicolaas Govert de Bruijn]
* <a href="https://home.ttic.edu/~dreyer/course/papers/barendregt.pdf">Lambda Calculi with Types</a> [Henk Barendregt]
* <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a> [Thierry Coquand, Gerard Huet]
* <a href="https://www.cambridge.org/core/services/aop-cambridge-core/content/view/869991BA6A99180BF96A616894C6D710/S0956796800020025a.pdf/introduction-to-generalized-type-systems.pdf">Introduction to Generalized Type Systems</a> [Henk Barendregt]
* <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/henk.pdf">Henk: a typed intermediate language</a> [Erik Meijer, Simon Peyton Jones]
* <a href="https://www.haskellforall.com/2014/09/morte-intermediate-language-for-super.html">Morte: an intermediate language for super-optimizing functional programs</a> [Gabriella Gonzalez]
* <a href="https://henk.groupoid.space/doc/henk.pdf">Henk: Pure Type System for Erlang</a> [Maksym Sokhatskyi]

## Credits

* <a itemprop="sameAs" content="https://orcid.org/0000-0001-7127-8796" href="https://orcid.org/0000-0001-7127-8796" target="orcid.widget" rel="me noopener noreferrer">Maksym Sokhatskyi <img src="https://orcid.org/sites/default/files/images/orcid_16x16.png"> 🇺🇦</a>
