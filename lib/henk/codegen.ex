defmodule Henk.Codegen do
  @moduledoc """
  Translates Henk.AST into Erlang Abstract Format.
  """
  alias Henk.AST

  def generate(%AST.Module{name: mod_name, declarations: decls}, env \\ %Henk.Typechecker.Env{}) do
    current_mod = String.to_atom(mod_name)
    functions = Enum.flat_map(decls, &generate_decl(&1, env, current_mod))

    module_attr = {:attribute, 1, :module, current_mod}
    export_all = {:attribute, 1, :compile, :export_all}

    forms = [module_attr, export_all] ++ functions ++ [{:eof, 1}]
    {:ok, forms}
  end

  defp generate_decl(%AST.Inductive{constrs: constrs}, _env, _mod) do
    Enum.map(constrs, fn {idx, name, ty} ->
      # Generate curried constructor function: name() -> \a1 -> \a2 -> {idx, a1, a2}
      body = generate_constr_body(idx, ty, [])
      clause = {:clause, 1, [], [], [body]}
      {:function, 1, String.to_atom(name), 0, [clause]}
    end)
  end

  defp generate_decl(%AST.DeclValue{name: name, expr: expr}, env, mod) do
    clause = {:clause, 1, [], [], [generate_expr(expr, MapSet.new(), env, mod)]}
    [{:function, 1, String.to_atom(name), 0, [clause]}]
  end

  defp generate_decl(
         %AST.DeclForeign{name: name, erl_mod: mod, erl_func: func, type: _ty},
         _env,
         _mod
       ) do
    # For now, simple arity extraction. Type should have arity.
    # Assume arity 1 for now.
    args = [{:var, 1, :X1}]

    call =
      {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(mod)}, {:atom, 1, String.to_atom(func)}},
       args}

    [{:function, 1, String.to_atom(name), 1, [{:clause, 1, args, [], [call]}]}]
  end

  defp generate_decl(_, _, _), do: []

  defp generate_constr_body(idx, %AST.Pi{codomain: next}, vars) do
    v_name = {:var, 1, String.to_atom("C#{length(vars) + 1}")}

    {:fun, 1,
     {:clauses, [{:clause, 1, [v_name], [], [generate_constr_body(idx, next, [v_name | vars])]}]}}
  end

  defp generate_constr_body(idx, _, vars) do
    {:tuple, 1, [{:integer, 1, idx} | Enum.reverse(vars)]}
  end

  defp generate_expr(%AST.Var{name: name}, local_env, env, current_mod) do
    # Map to Erlang variable (Capitalized) or atom if it's a global
    if MapSet.member?(local_env, name) do
      {:var, 1, String.capitalize(name) |> String.to_atom()}
    else
      # Global call: check if it's local or remote
      case Map.get(env.name_to_mod, name) do
        nil ->
          # Unknown, assume local 0-arity
          {:call, 1, {:atom, 1, String.to_atom(name)}, []}

        mod_str ->
          mod = String.to_atom(mod_str)

          if mod == current_mod do
            {:call, 1, {:atom, 1, String.to_atom(name)}, []}
          else
            {:call, 1, {:remote, 1, {:atom, 1, mod}, {:atom, 1, String.to_atom(name)}}, []}
          end
      end
    end
  end

  defp generate_expr(%AST.Universe{level: i}, _local_env, _env, _mod) do
    {:integer, 1, i}
  end

  defp generate_expr(%AST.Lam{name: x, body: body}, local_env, env, mod) do
    erl_x = {:var, 1, String.capitalize(x) |> String.to_atom()}
    new_local_env = MapSet.put(local_env, x)

    {:fun, 1,
     {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body, new_local_env, env, mod)]}]}}
  end

  defp generate_expr(%AST.App{func: f, arg: arg}, local_env, env, mod) do
    # f arg -> f(arg)
    {:call, 1, generate_expr(f, local_env, env, mod), [generate_expr(arg, local_env, env, mod)]}
  end

  defp generate_expr(%AST.Constr{index: j, args: args}, local_env, env, mod) do
    # Represent as tuple {Index, Args...}
    {:tuple, 1, [{:integer, 1, j} | Enum.map(args, &generate_expr(&1, local_env, env, mod))]}
  end

  defp generate_expr(%AST.Let{decls: decls, body: body}, local_env, env, mod) do
    # Generate: begin Var1 = Expr1, Var2 = Expr2, ..., Body end
    new_local_env = Enum.reduce(decls, local_env, fn {name, _}, acc -> MapSet.put(acc, name) end)

    matches =
      Enum.map(decls, fn {name, expr} ->
        {:match, 1, {:var, 1, String.capitalize(name) |> String.to_atom()},
         generate_expr(expr, local_env, env, mod)}
      end)

    {:block, 1, matches ++ [generate_expr(body, new_local_env, env, mod)]}
  end

  defp generate_expr(%AST.Ind{inductive: ind, cases: cases, term: t}, local_env, env, mod) do
    ind_func_name = :F_ind
    ind_var = {:var, 1, ind_func_name}

    clauses =
      Enum.zip(ind.constrs, cases)
      |> Enum.map(fn {{idx, _cname, c_ty}, case_expr} ->
        arg_types = get_arg_types(c_ty)
        n_args = length(arg_types)

        arg_vars =
          if n_args > 0,
            do: Enum.map(1..n_args, fn i -> {:var, 1, String.to_atom("A#{i}")} end),
            else: []

        pattern = {:tuple, 1, [{:integer, 1, idx} | arg_vars]}

        case_args =
          Enum.zip(arg_vars, arg_types)
          |> Enum.flat_map(fn {a_v, a_ty} ->
            is_rec = is_recursive_type(a_ty, ind.name)

            ih_v =
              if is_rec do
                {:call, 1, ind_var, [a_v]}
              else
                {:atom, 1, :unused_ih}
              end

            [a_v, ih_v]
          end)

        case_body = apply_lam(generate_expr(case_expr, local_env, env, mod), case_args)
        {:clause, 1, [pattern], [], [case_body]}
      end)

    final_clauses =
      if clauses == [] do
        # Empty induction (e.g. on Empty type)
        [
          {:clause, 1, [{:var, 1, :_}], [],
           [{:call, 1, {:atom, 1, :error}, [{:atom, 1, :empty_induction}]}]}
        ]
      else
        clauses
      end

    named_fun = {:named_fun, 1, ind_func_name, final_clauses}
    {:call, 1, named_fun, [generate_expr(t, local_env, env, mod)]}
  end

  defp get_arg_types(%AST.Pi{domain: d, codomain: c}), do: [d | get_arg_types(c)]
  defp get_arg_types(_), do: []

  defp is_recursive_type(%AST.Var{name: name}, ind_name), do: name == ind_name
  defp is_recursive_type(%AST.App{func: f}, ind_name), do: is_recursive_type(f, ind_name)

  defp is_recursive_type(%AST.Pi{codomain: c}, ind_name), do: is_recursive_type(c, ind_name)

  defp is_recursive_type(_, _), do: false

  defp apply_lam(lam, []), do: lam

  defp apply_lam(lam, [arg | rest]) do
    apply_lam({:call, 1, lam, [arg]}, rest)
  end
end
