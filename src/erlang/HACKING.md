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

## Console Session (rebar3 om repl --root=../../)

### Setup

```erlang
%% Start — returns initial state S
S = om_repl:start().
```

### Parse (`om:a`)

Parse term and remote references.

```erlang
T = om_repl:parse(<<"\\(x:*)->x">>).
% {{"λ",{x,0}},{{star,1},{var,{x,0}}}}
T2 = om_repl:parse(<<"#List/@">>).
% {remote,"List/@"}
```

### Norm (`om:norm`)

Normalize a local term and unfold a remote like `om:norm(om:a("#List/map"))`.

```erlang
{Norm1, _} = om_type:norm(T, S).
{Norm2, _} = om_state:cache(norm, "List/map", S).
```

### Type (`om:type`)

Typechecks a local or remote term like `om:type(om:a("#IO/[>>=]"))`.

```erlang
{Type1, _} = om_type:type(T, S).
{Type2, _} = om_state:cache(type, "IO/[>>=]", S).
```

### Erase (`om:erase`)

Erase a local term.

```erlang
{{Body, ErasedType}, _} = om_erase:erase(T, [], S).
```

### Show (`om:show`)

Parse and print a library file like `om:show("List/@")`.

```erlang
T = om_repl:parse(om_repl:read(om_repl:name("List/@"))).
io:format("~ts~n", [om_parse:print(T, 0)]).
```

### Scan (`om:scan`)

Scan+extract all files in current mode with verbose and quite effects.

```erlang
om_repl:scan(true).
om_repl:scan(false).
```

### Mode (`om:mode`)

Get or sets current mode.

```erlang
om_repl:mode().
om_repl:mode("morte").
```

## AST Representation

```erlang
{star, N}                             %% * (kind N)
{var,  {Name, Index}}                 %% variable (De Bruijn index)
{remote, "Module/Name"}               %% cross-module reference
{app,  {Func, Arg}}                   %% application
{{"λ", {Name, 0}}, {InputType, Body}} %% lambda abstraction
{{"∀", {Name, 0}}, {InputType, Body}} %% pi (forall) type
{"→", {InputType, OutputType}}        %% arrow shorthand
```

## UTF-8

> `"λ"` = charlist `[955]`, `"∀"` = `[8704]`, `"→"` = `[8594]`.

## State Passing

State-threaded.

```erlang
{Norm,  S1} = om_type:norm(Term, S0).
{Type,  S1} = om_type:type(Term, S0).
{Value, S1} = om_state:cache(norm | type | erased, N, S0).
```

Stateless helpers (load remotes from disk on demand).

```
Term = om_repl:parse(Binary).
Type = om_type:type_s(Term, Env).
Norm = om_type:norm(Term).
```

## Guidelines

1. **No ETS, no `put/get`** — pass `S` explicitly through all operations.
2. **Stateless helpers** (`norm/1`, `type_s/2`, `erase_s/2`) load remote files from disk when needed.
3. **`om_extract` catches errors** per-file so one bad file doesn't abort extraction.
