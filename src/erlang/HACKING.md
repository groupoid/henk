Om/Henk Erlang Hacking
=======================

Compact, pure-functional Morte library type checker and extractor in Erlang.

## Quick Start

```sh
cd src/erlang

# Compile base Morte library → ebin/*.beam
rebar3 om base --root=../../

# Open interactive REPL
rebar3 om repl --root=../../

# Run tests
rebar3 om test --root=../../
```

## Manual compile (no rebar3)

```sh
erlc +debug_info -o ebin/ \
  src/repl/om_state.erl \
  src/core/om_tok.erl src/core/om_parse.erl \
  src/core/om_type.erl src/core/om_erase.erl \
  src/core/om_extract.erl src/repl/om_repl.erl \
  src/henk.erl

erl -pa ebin -eval 'application:set_env(om, root, "../.."), om_repl:start(), om_repl:scan(false), init:stop().'
```

## Module Map

| File | Role |
|------|------|
| `core/om_tok.erl` | Tokenizer (stateful scanner → token list) |
| `core/om_parse.erl` | Parser (forward/backward pass → AST) |
| `core/om_type.erl` | Type checker + normalizer |
| `core/om_erase.erl` | Type erasure → Core Erlang AST |
| `core/om_extract.erl` | Morte-to-BEAM extractor (saves `.beam`) |
| `repl/om_state.erl` | Pure `#state{}` record + cache maps |
| `repl/om_repl.erl` | Entry points: `start`, `scan`, `parse`, `name` |
| `plugins/om/src/om_prv_base.erl` | `rebar3 om base` provider |
| `plugins/om/src/om_prv_repl.erl` | `rebar3 om repl` provider |

## AST Representation

All nodes use plain Erlang strings for constructor names (charlists):

```erlang
{star, N}                             %% * (kind N)
{var,  {Name, Index}}                 %% variable with De Bruijn index
{remote, "Module/Name"}               %% cross-module reference
{app,  {Func, Arg}}                   %% application
{{"λ", {Name, 0}}, {InputType, Body}} %% lambda abstraction
{{"∀", {Name, 0}}, {InputType, Body}} %% pi (forall) type
{"→", {InputType, OutputType}}        %% arrow shorthand
```

> **Note:** `"λ"` in Erlang is the charlist `[955]`, `"∀"` is `[8704]`, `"→"` is `[8594]`.

## State Passing Architecture

All functions are **pure** — no ETS, no process dictionary.
The `#state{}` record carries type/norm/erased caches as maps.

```erlang
%% State-threaded operations
{Norm,  S1} = om_type:norm(Term, S0).
{Type,  S1} = om_type:type(Term, S0).
{{B,T}, S1} = om_erase:erase(Term, Env, S0).

%% Stateless helpers (no remotes required to be in cache)
Term  = om_parse:expr(om_tok:tokens(Binary, 0), 0).
Type  = om_type:type_s(Term, Env).
Norm  = om_type:norm(Term).
```

## Caching

Remote terms (`#Module/Name`) are cached in `#state{}` maps:

```erlang
%% Looks up N in state cache, or loads/parses/evaluates from disk
{Value, S1} = om_state:cache(norm | type | erased, N, S0).
```

## Guidelines

1. **No ETS, no `put/get`** — pass `S` explicitly through all operations.
2. **Stateless helpers** (`norm/1`, `type_s/2`, `erase_s/2`) load remote files directly from disk when needed.
3. **`om_extract` catches errors** per-file so one bad file doesn't abort the whole extraction.
