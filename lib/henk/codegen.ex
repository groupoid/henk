defmodule Henk.Codegen do
  @moduledoc """
  Translates pure CoC terms (Var/Universe/Pi/Lam/App) to Erlang Abstract Format.

  Type erasure: Universe and Pi are unit terms at runtime (atom :type).
  Only Lam/App/Var carry runtime meaning.
  """
  alias Henk.AST

  def generate(%AST.Module{name: mod_name, declarations: decls}, env \\ %Henk.Typechecker.Env{}) do
    current_mod = String.to_atom(mod_name)
    functions = Enum.flat_map(decls, &generate_decl(&1, env, current_mod))

    forms = [
      {:attribute, 1, :module, current_mod},
      {:attribute, 1, :compile, :export_all}
      | functions
    ] ++ [{:eof, 1}]

    {:ok, forms}
  end

  defp generate_decl(%AST.DeclValue{name: name, expr: expr}, env, mod) do
    body = generate_expr(expr, MapSet.new(), env, mod)
    clause = {:clause, 1, [], [], [body]}
    [{:function, 1, String.to_atom(name), 0, [clause]}]
  end

  defp generate_decl(%AST.DeclForeign{}, _env, _mod), do: []  # emitted inline via foreign_defs

  defp generate_decl(_decl, _env, _mod), do: []

  # ── Expression code generation ────────────────────────────────────────────

  # Any is a type-erasure sentinel — emit as atom at runtime
  defp generate_expr(%AST.Var{name: "Any"}, _loc, _env, _mod), do: {:atom, 1, :any}

  defp generate_expr(%AST.Var{name: name}, local_vars, env, mod) do
    cond do
      MapSet.member?(local_vars, name) ->
        {:var, 1, erl_var(name)}

      # Foreign FFI: emit direct 0-arg remote call (args collected by App case below)
      Map.has_key?(env.foreign_defs, name) ->
        {erl_mod, erl_func} = env.foreign_defs[name]
        {:call, 1,
         {:remote, 1, {:atom, 1, String.to_atom(erl_mod)}, {:atom, 1, String.to_atom(erl_func)}},
         []}

      true ->
        mod_str = Atom.to_string(mod)
        case Map.get(env.name_to_mod, name) do
          nil     -> {:call, 1, {:atom, 1, String.to_atom(name)}, []}
          ^mod_str -> {:call, 1, {:atom, 1, String.to_atom(name)}, []}
          m       -> {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(m)}, {:atom, 1, String.to_atom(name)}}, []}
        end
    end
  end

  # Types are erased at runtime
  defp generate_expr(%AST.Universe{}, _loc, _env, _mod), do: {:atom, 1, :type}
  defp generate_expr(%AST.Pi{}, _loc, _env, _mod), do: {:atom, 1, :type}

  defp generate_expr(%AST.Lam{name: x, body: body}, local_vars, env, mod) do
    erl_x = {:var, 1, erl_var(x)}
    new_loc = MapSet.put(local_vars, x)
    {:fun, 1, {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body, new_loc, env, mod)]}]}}
  end

  # App where the func is a foreign: collect all args and emit multi-arg remote call
  defp generate_expr(%AST.App{func: f, arg: arg}, loc, env, mod) do
    {base_func, collected_args} = collect_foreign_app(f, [arg], env)
    case base_func do
      %AST.Var{name: name} when is_map_key(env.foreign_defs, name) ->
        {erl_mod, erl_func} = env.foreign_defs[name]
        args_code = Enum.map(collected_args, &generate_expr(&1, loc, env, mod))
        {:call, 1,
         {:remote, 1, {:atom, 1, String.to_atom(erl_mod)}, {:atom, 1, String.to_atom(erl_func)}},
         args_code}

      _ ->
        {:call, 1, generate_expr(f, loc, env, mod), [generate_expr(arg, loc, env, mod)]}
    end
  end

  # Collect left-spine App arguments for multi-arg foreign calls
  defp collect_foreign_app(%AST.App{func: f, arg: a}, acc, env) do
    collect_foreign_app(f, [a | acc], env)
  end
  defp collect_foreign_app(other, acc, _env), do: {other, acc}

  defp generate_expr(other, _loc, _env, _mod) do
    # Fallback: emit undefined atom
    {:atom, 1, :undefined}
    |> tap(fn _ -> IO.warn("Codegen: unhandled term #{inspect(other, limit: 5)}", []) end)
  end

  # Erlang variable names must start with uppercase
  defp erl_var("_"), do: :_
  defp erl_var(name) do
    name
    |> String.replace(~r/[^a-zA-Z0-9_]/, "_")
    |> then(fn s ->
      first = String.first(s)
      if first == String.upcase(first), do: s, else: String.capitalize(s)
    end)
    |> String.to_atom()
  end
end
