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
          nil ->
            # Not found in env, maybe it's a local call or built-in
            {:call, 1, {:atom, 1, String.to_atom(name)}, []}

          ^mod_str ->
            # Local call: strip module prefix if present
            local_name = if String.starts_with?(name, mod_str <> "."),
              do: String.slice(name, (String.length(mod_str) + 1)..-1//1),
              else: name
            {:call, 1, {:atom, 1, String.to_atom(local_name)}, []}

          m ->
            # Remote call: split if name is qualified
            remote_func = if String.starts_with?(name, m <> "."),
              do: String.slice(name, (String.length(m) + 1)..-1//1),
              else: name
            {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(m)}, {:atom, 1, String.to_atom(remote_func)}}, []}
        end
    end
  end

  # Types are erased at runtime
  defp generate_expr(%AST.Universe{}, _loc, _env, _mod), do: {:atom, 1, :type}
  defp generate_expr(%AST.Pi{}, _loc, _env, _mod), do: {:atom, 1, :type}

  defp generate_expr(%AST.String{value: v}, _loc, _env, _mod) do
    {:bin, 1, [{:bin_element, 1, {:string, 1, String.to_charlist(v)}, :default, :default}]}
  end

  defp generate_expr(%AST.Lam{name: x, body: body}, local_vars, env, mod) do
    erl_x = {:var, 1, erl_var(x)}
    new_loc = MapSet.put(local_vars, x)
    {:fun, 1, {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body, new_loc, env, mod)]}]}}
  end

  # App where the func is a foreign: collect all args and emit multi-arg remote call
  defp generate_expr(%AST.App{func: f, arg: arg} = app, loc, env, mod) do
    if depth(app) > 100 do
      {decls, final_app} = flatten_app(app)
      generate_expr(%AST.Let{decls: decls, body: final_app}, loc, env, mod)
    else
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
  end

  # Let: desugar to App(Lam) or handle natively as block
  defp generate_expr(%AST.Let{decls: decls, body: body}, loc, env, mod) do
    # Native Erlang block: begin X1 = E1, ... Body end
    {exprs, final_loc} =
      Enum.reduce(decls, {[], loc}, fn {name, expr}, {acc_exprs, acc_loc} ->
        erl_v = {:var, 1, erl_var(name)}
        match = {:match, 1, erl_v, generate_expr(expr, acc_loc, env, mod)}
        {[match | acc_exprs], MapSet.put(acc_loc, name)}
      end)

    exprs = Enum.reverse(exprs) ++ [generate_expr(body, final_loc, env, mod)]
    {:block, 1, exprs}
  end

  # Case: desugar on the fly if it reaches codegen
  defp generate_expr(%AST.Case{} = c, loc, env, mod) do
    desugared = Henk.Desugar.desugar_expr(c, env)
    generate_expr(desugared, loc, env, mod)
  end

  defp generate_expr(other, _loc, _env, _mod) do
    # Fallback: emit undefined atom
    {:atom, 1, :undefined}
    |> tap(fn _ -> IO.warn("Codegen: unhandled term #{inspect(other, limit: 5)}", []) end)
  end

  # ── Helpers ───────────────────────────────────────────────────────────────

  defp depth(%AST.App{func: f, arg: a}), do: 1 + max(depth(f), depth(a))
  defp depth(%AST.Lam{body: b}), do: 1 + depth(b)
  defp depth(%AST.Pi{codomain: c}), do: 1 + depth(c)
  defp depth(%AST.Let{body: b}), do: 1 + depth(b)
  defp depth(_), do: 1

  # Flatten f (g (h x)) -> [V1 = h x, V2 = g V1, V3 = f V2], V3
  defp flatten_app(app) do
    {decls, final_var, _count} = do_flatten_app(app, [], 0)
    {Enum.reverse(decls), final_var}
  end

  defp do_flatten_app(%AST.App{func: f, arg: a}, acc_decls, count) do
    # In CoC, we usually have f applied to arg.
    # We flatten the right leaning tree: Succ (Succ (Succ Zero))
    {acc_decls, f_var, count} = ensure_flat(f, acc_decls, count)
    {acc_decls, a_var, count} = ensure_flat(a, acc_decls, count)
    
    unique_name = "_tmp_#{count}"
    new_app = %AST.App{func: f_var, arg: a_var}
    {[{unique_name, new_app} | acc_decls], %AST.Var{name: unique_name}, count + 1}
  end

  defp ensure_flat(%AST.App{} = app, acc_decls, count) do
    do_flatten_app(app, acc_decls, count)
  end
  defp ensure_flat(other, acc_decls, count), do: {acc_decls, other, count}

  # Collect left-spine App arguments for multi-arg foreign calls
  defp collect_foreign_app(%AST.App{func: f, arg: a}, acc, env) do
    collect_foreign_app(f, [a | acc], env)
  end
  defp collect_foreign_app(other, acc, _env), do: {other, acc}

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
