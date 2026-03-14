defmodule Henk.AST do
  import Kernel, except: [to_string: 1]

  @moduledoc """
  Abstract Syntax Tree structures for the Henk compiler.
  """

  # --- Surface Language Declarations ---

  defmodule Module do
    defstruct [:name, :declarations]
  end

  defmodule DeclValue do
    defstruct [:name, :binders, :expr, :guards, :where_decls]
  end

  defmodule DeclTypeSignature do
    defstruct [:name, :type]
  end

  defmodule DeclData do
    defstruct [:name, :params, :constructors]
  end

  defmodule DeclForeign do
    defstruct [:name, :type, :erl_mod, :erl_func]
  end

  defmodule Case do
    defstruct [:expr, :branches]
  end

  defmodule Lambda do
    defstruct [:binders, :body]
  end

  # --- Core Language Terms (CIC) ---

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

  defmodule Inductive do
    defstruct [:name, :params, :level, :constrs]
  end

  defmodule Let do
    defstruct [:decls, :body]
  end

  # Constructor implementation: index, inductive definition, and arguments
  defmodule Constr do
    defstruct [:index, :inductive, :args]
  end

  # Induction operator: inductive definition, motive (P), cases, and target term
  defmodule Ind do
    defstruct [:inductive, :motive, :cases, :term]
  end

  # Helper for surface binders
  defmodule BinderVar do
    defstruct [:name]
  end

  defmodule BinderConstructor do
    defstruct [:name, :args]
  end

  # --- Pretty Printing ---

  def to_string(term) do
    case term do
      %Var{name: name} ->
        name

      %Universe{level: l} ->
        "U#{l}"

      %Pi{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "(#{x} : #{domain_str}) -> #{to_string(b)}"

      %Lam{name: x, body: b} ->
        "\\#{x} -> #{to_string(b)}"

      %App{func: f, arg: a} ->
        # f a b ...
        f_str = if binds_tightly?(f), do: to_string(f), else: "(#{to_string(f)})"
        a_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "#{f_str} #{a_str}"

      %Inductive{name: name, params: params} ->
        if params == [] do
          name
        else
          params_str = Enum.map_join(params, " ", fn {n, _} -> n end)
          "(#{name} #{params_str})"
        end

      %Constr{index: i, inductive: d, args: args} ->
        name =
          case Enum.find(d.constrs, fn {idx, _, _} -> idx == i end) do
            {_, n, _} -> n
            _ -> "Constr#{i}"
          end

        if args == [] do
          name
        else
          args_str =
            Enum.map_join(args, " ", fn arg ->
              if complex?(arg), do: "(#{to_string(arg)})", else: to_string(arg)
            end)

          "(#{name} #{args_str})"
        end

      %Ind{inductive: d, term: t} ->
        "ind_#{d.name}(#{to_string(t)})"

      %Let{decls: decls, body: body} ->
        decls_str =
          Enum.map_join(decls, "; ", fn {name, expr} ->
            "#{name} = #{to_string(expr)}"
          end)

        "let #{decls_str} in #{to_string(body)}"

      _ ->
        inspect(term)
    end
  end

  defp complex?(%App{}), do: true
  defp complex?(%Lam{}), do: true
  defp complex?(%Pi{}), do: true
  defp complex?(%Let{}), do: true
  defp complex?(%Ind{}), do: true
  defp complex?(%Constr{args: [_ | _]}), do: true
  defp complex?(_), do: false

  # App func only needs parens if it's a binder or complex operator
  defp binds_tightly?(%Var{}), do: true
  defp binds_tightly?(%App{}), do: true
  defp binds_tightly?(%Constr{args: []}), do: true
  defp binds_tightly?(%Inductive{params: []}), do: true
  defp binds_tightly?(_), do: false

  # --- Type/Term Utilities ---

  def pi(name, domain, codomain), do: %Pi{name: name, domain: domain, codomain: codomain}
  def arrow(a, b), do: %Pi{name: "_", domain: a, codomain: b}
  def universe(i), do: %Universe{level: i}
  def nat(), do: %Var{name: "Nat"}
  def bool(), do: %Var{name: "Bool"}
  def unit(), do: %Var{name: "Unit"}
end
