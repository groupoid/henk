defmodule Henk.AST do
  import Kernel, except: [to_string: 1]

  @moduledoc """
  Abstract Syntax Tree for the Henk compiler.

  Surface / intermediate forms (used by parser and desugarer):
    Module, DeclValue, DeclData, DeclTypeSignature, DeclForeign,
    Inductive, Case, Lambda, BinderVar, BinderConstructor, Let

  Pure CoC core terms (post-desugar, seen by typechecker + codegen):
    Var, Universe, Pi, Lam, App

  The desugarer transforms:
    DeclData  → Inductive (first pass)
    Inductive → Church-encoded DeclValues (second pass: Pi-type + Lam constructors)
    Case      → Church-fold application: e Any (\\x->b1) (\\y->b2)
    Let       → App(Lam): (\\x -> body) expr   (let has no primitives in CoC)
  """

  # ── Surface declarations ──────────────────────────────────────────────────

  defmodule Module do
    defstruct [:name, :declarations]
  end

  defmodule DeclValue do
    defstruct [:name, :binders, :expr, :guards, :where_decls]
  end

  defmodule DeclTypeSignature do
    defstruct [:name, :type]
  end

  # data T p1 p2 = C1 t1 t2 | C2 t3   (parser output)
  defmodule DeclData do
    defstruct [:name, :params, :constructors]
  end

  defmodule DeclForeign do
    defstruct [:name, :type, :erl_mod, :erl_func]
  end

  # ── Surface expressions ───────────────────────────────────────────────────

  # case e of C1 x -> b1 | C2 y z -> b2   (parser output)
  defmodule Case do
    defstruct [:expr, :branches]
  end

  # \x y -> body   (parser output)
  defmodule Lambda do
    defstruct [:binders, :body]
  end

  defmodule BinderVar do
    defstruct [:name]
  end

  defmodule BinderConstructor do
    defstruct [:name, :args]
  end

  # ── Intermediate form ─────────────────────────────────────────────────────
  # Produced by first-pass desugaring of DeclData.
  # name: type name, params: [{name, kind}], constrs: [{name, [arg_type]}]
  # Consumed by second-pass desugaring → Church-encoded DeclValues.

  defmodule Inductive do
    @moduledoc "Intermediate representation of a data type, before Church encoding."
    defstruct [:name, :params, :constrs]
    # constrs :: [{constr_name, [arg_type_term]}]
  end

  # ── Surface: let-expression ──────────────────────────────────────────────
  # Desugared to App(Lam): let x = e in body  →  (λx → body) e

  defmodule Let do
    defstruct [:decls, :body]
  end

  # ── Pure CoC core terms ───────────────────────────────────────────────────

  defmodule Var do
    defstruct [:name]
  end

  defmodule Universe do
    defstruct [:level]
  end

  defmodule Pi do
    defstruct [:name, :domain, :codomain]
  end

  defmodule Lam do
    defstruct [:name, :domain, :body]
  end

  defmodule App do
    defstruct [:func, :arg]
  end

  defmodule String do
    defstruct [:value]
  end

  # ── Pretty Printing ───────────────────────────────────────────────────────

  def to_string(term) do
    case term do
      %Var{name: name} ->
        name

      %Universe{level: l} ->
        "U#{l}"

      %Pi{name: "_", domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "#{domain_str} -> #{to_string(b)}"

      %Pi{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "(#{x} : #{domain_str}) -> #{to_string(b)}"

      %Lam{name: x, body: b} ->
        "\\#{x} -> #{to_string(b)}"

      %App{func: f, arg: a} ->
        f_str = if binds_tightly?(f), do: to_string(f), else: "(#{to_string(f)})"
        a_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "#{f_str} #{a_str}"

      %Let{decls: decls, body: body} ->
        decls_str =
          Enum.map_join(decls, "; ", fn {name, expr} ->
            "#{name} = #{to_string(expr)}"
          end)

        "let #{decls_str} in #{to_string(body)}"  # surface only

      %Inductive{name: n} ->
        n

      %Case{expr: e} ->
        "case #{to_string(e)} of ..."

      %String{value: v} ->
        "\"#{v}\""

      _ ->
        inspect(term)
    end
  end

  defp complex?(%App{}), do: true
  defp complex?(%Lam{}), do: true
  defp complex?(%Pi{}), do: true
  defp complex?(_), do: false

  defp binds_tightly?(%Var{}), do: true
  defp binds_tightly?(%App{}), do: true
  defp binds_tightly?(_), do: false

  # ── Helpers ───────────────────────────────────────────────────────────────

  def pi(name, domain, codomain), do: %Pi{name: name, domain: domain, codomain: codomain}
  def arrow(a, b), do: %Pi{name: "_", domain: a, codomain: b}
  def universe(i), do: %Universe{level: i}
  def any(), do: %Var{name: "Any"}

  def extract_vars(term), do: extract_vars(term, MapSet.new())

  defp extract_vars(%Var{name: n}, acc), do: MapSet.put(acc, n)
  defp extract_vars(%App{func: f, arg: a}, acc) do
    acc = extract_vars(f, acc)
    extract_vars(a, acc)
  end
  defp extract_vars(%Lam{domain: d, body: b}, acc) do
    acc = extract_vars(d, acc)
    extract_vars(b, acc)
  end
  defp extract_vars(%Pi{domain: d, codomain: c}, acc) do
    acc = extract_vars(d, acc)
    extract_vars(c, acc)
  end
  defp extract_vars(%Let{decls: decls, body: b}, acc) do
    acc = Enum.reduce(decls, acc, fn {_, e}, a -> extract_vars(e, a) end)
    extract_vars(b, acc)
  end
  defp extract_vars(%Case{expr: e, branches: bs}, acc) do
    acc = extract_vars(e, acc)
    Enum.reduce(bs, acc, fn {_, b}, a -> extract_vars(b, a) end)
  end
  defp extract_vars(%Module{declarations: decls}, acc) do
    Enum.reduce(decls, acc, fn
      %DeclValue{expr: e}, a -> extract_vars(e, a)
      %DeclTypeSignature{type: t}, a -> extract_vars(t, a)
      %DeclData{params: ps, constructors: cs}, a ->
        a = Enum.reduce(ps, a, fn 
          {_, k}, a2 -> extract_vars(k, a2)
          n, a2 when is_binary(n) -> a2
          _, a2 -> a2
        end)
        Enum.reduce(cs, a, fn 
          {_, ts}, a2 -> Enum.reduce(ts, a2, &extract_vars/2)
          _, a2 -> a2
        end)
      _, a -> a
    end)
  end

  defp extract_vars(name, acc) when is_binary(name), do: MapSet.put(acc, name)
  defp extract_vars(_, acc), do: acc
end
