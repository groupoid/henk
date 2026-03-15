Om Hacking
==========

Henk Erlang Core is built as a compact, pure functional system.

Developers
----------

```
$ git clone git://github.com/groupoid/om && cd om
$ cd src/erlang
$ rebar3 om base --root=../.. --verbose
$ rebar3 om test --root=../..
$ rebar3 om repl --root=../..
```

Implementation Architecture
---------------------------

The core logic is implemented in compact modules:

- `core/om_tok.erl`: Tokenizer using functional recursion.
- `core/om_parse.erl`: Fast forward/backward pass parser.
- `core/om_type.erl`: Typechecker and normalizer state.
- `core/om_erase.erl`: Program eraser (extraction preparation).
- `core/om_extract.erl`: Morte-to-BEAM extractor.
- `core/om_cache.erl`: Functional cache for types and normal forms.

Infrastructure:

- `repl/om_state.erl`: Definition of the core `#state{}` record.
- `repl/om_repl.erl`: REPL process and state manager.

State Management
----------------

All state (caches, configuration) is managed via the `#state{}` record defined in `om_state.erl`. The REPL process manages this state in its process dictionary. Session example with Henk:

```erlang
> om_repl:start().
"morte"

> om_repl:test([]).
...

> om_repl:mode("morte").
"morte"

> om_repl:extr("morte/Bool.henk").
Saving compiled 'morte.Bool.beam' module.
ok
```

### Result AST

The internal representation is a compact tuple-based AST:

```erlang
% star   : {star, N}
% var    : {var, {Name, Index}}
% remote : {remote, Name}
% app    : {app, {Func, Arg}}
% lambda : {{<<"λ"/utf8>>, {Name, 0}}, {Input, Output}}
% pi     : {{<<"∀"/utf8>>, {Name, 0}}, {Input, Output}}
% arrow  : {{<<"→"/utf8>>, {Input, Output}}}
```

### Core Operations

#### Normalization

Rreturns `{Result, NewState}`.

```erlang
{Norm, S1} = om_type:norm(Term, S0).
```

#### Typechecking

Returns `{Type, NewState}`.

```erlang
{Type, S1} = om_type:type(Term, S0).
```
#### Erasure 

Rreturns `{{Erased, Type}, NewState}`.

```erlang
{E, S1} = om_erase:erase(Term, S0).
```

Guidelines for Hacking
----------------------

1. **Pure Functions**: Ensure core logic functions use thread `State` explicitly.
2. **Compactness**: KUse functional recursion over complex imperative structures.
3. **State Record**: All configuration and caches MUST live in `#state{}`.

