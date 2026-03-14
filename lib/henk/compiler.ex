defmodule Henk.Compiler do
  @moduledoc """
  Main entry point for the Henk compiler.
  """
  alias Henk.{Lexer, Layout, Parser, Desugar, Codegen, AST}

  def compile_module(source, opts \\ []) do
    with {:ok, tokens} <- Lexer.lex(source),
         resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- Parser.parse(resolved) do
      env = resolve_imports(ast, %Henk.Typechecker.Env{}, opts)
      env = collect_local_names(ast, env)
      desugared = Desugar.desugar(ast, env)
      final_env = populate_local_env(desugared, env)
      typecheck_res =
        if Keyword.get(opts, :typecheck, true) do
          case Henk.Typechecker.check_module(desugared, final_env) do
            :ok -> :ok
            {:error, reason} -> {:error, {:type_error, reason}}
          end
        else
          :ok
        end

      if typecheck_res == :ok and Keyword.get(opts, :check_only, false) do
        {:ok, desugared.name, :check_only}
      else
        with :ok <- typecheck_res,
             {:ok, forms} <- Codegen.generate(desugared, env) do
          case :compile.forms(forms, [:return_errors, :debug_info]) do
            {:ok, mod, bin} -> {:ok, mod, bin}
            {:error, errors, warnings} -> {:error, {:erl_compile, errors, warnings}}
          end
        end
      end
    else
      {:error, _} = err -> err
    end
  end

  defp populate_local_env(%AST.Module{name: _mod_name, declarations: decls}, env) do
    Enum.reduce(decls, env, fn
      %AST.DeclValue{name: n, expr: e}, acc ->
        ty = Henk.Typechecker.infer(acc, e)
        %{acc | defs: Map.put(acc.defs, n, e), ctx: [{n, ty} | acc.ctx]}

      %AST.Inductive{} = ind, acc ->
        acc = %{acc | env: Map.put(acc.env, ind.name, ind)}
        acc = %{acc | defs: add_constructors(ind, acc.defs)}
        %{acc | ctx: add_constructors_to_ctx(ind, acc.ctx)}

      _, acc ->
        acc
    end)
  end

  defp collect_local_names(%AST.Module{name: mod_name, declarations: decls}, env) do
    new_mapping =
      Enum.reduce(decls, env.name_to_mod, fn
        %AST.DeclValue{name: n}, acc ->
          Map.put(acc, n, mod_name)

        %AST.Inductive{name: n, constrs: cs}, acc ->
          acc = Map.put(acc, n, mod_name)
          Enum.reduce(cs, acc, fn {_, cn, _}, a -> Map.put(a, cn, mod_name) end)

        _, acc ->
          acc
      end)

    %{env | name_to_mod: new_mapping}
  end

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
    # Implicitly import Prelude if it exists and we are not in Prelude
    env =
      if mod_name != "Prelude" do
        case load_module_to_env("Prelude", env, opts) do
          {:ok, new_env} -> new_env
          _ -> env
        end
      else
        env
      end

    Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        case load_module_to_env(name, acc, opts) do
          {:ok, new_env} -> new_env
          _ -> acc
        end

      _, acc ->
        acc
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    case find_module_path(mod_name) do
      {:ok, path} ->
        source = File.read!(path)

        with {:ok, tokens} <- Lexer.lex(source),
             resolved <- Layout.resolve(tokens),
             {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do
          # 1. Resolve imports of the sub-module first (recursive)
          env_with_imports = resolve_imports(mod, env, opts)

          # 2. Add declarations of the current module to env
          {new_defs, new_types, new_names, new_ctx} =
            Enum.reduce(
              mod.declarations,
              {env_with_imports.defs, env_with_imports.env, env_with_imports.name_to_mod,
               env_with_imports.ctx},
              fn
                %AST.DeclValue{} = v, {d_acc, t_acc, n_acc, c_acc} ->
                  current_env = %{
                    env_with_imports
                    | defs: d_acc,
                      env: t_acc,
                      name_to_mod: n_acc,
                      ctx: c_acc
                  }

                  desugared_v = Desugar.desugar_decl(v, current_env)
                  val_ty = Henk.Typechecker.infer(current_env, desugared_v.expr)

                  {Map.put(d_acc, desugared_v.name, desugared_v.expr), t_acc,
                   Map.put(n_acc, desugared_v.name, mod_name),
                   [{desugared_v.name, val_ty} | c_acc]}

                %AST.DeclData{} = data, {d_acc, t_acc, n_acc, c_acc} ->
                  current_env = %{
                    env_with_imports
                    | defs: d_acc,
                      env: t_acc,
                      name_to_mod: n_acc,
                      ctx: c_acc
                  }

                  desugared_ind = Desugar.desugar_decl(data, current_env)
                  new_t_acc = Map.put(t_acc, desugared_ind.name, desugared_ind)
                  new_d_acc = add_constructors(desugared_ind, d_acc)
                  new_c_acc = add_constructors_to_ctx(desugared_ind, c_acc)

                  n_acc2 = Map.put(n_acc, desugared_ind.name, mod_name)

                  n_acc3 =
                    Enum.reduce(desugared_ind.constrs, n_acc2, fn {_, cn, _}, a ->
                      Map.put(a, cn, mod_name)
                    end)

                  {new_d_acc, new_t_acc, n_acc3, new_c_acc}

                _, acc ->
                  acc
              end
            )

          {:ok,
           %{
             env_with_imports
             | defs: new_defs,
               env: new_types,
               name_to_mod: new_names,
               ctx: new_ctx
           }}
        else
          err -> {:error, err}
        end

      nil ->
        {:error, :module_not_found}
    end
  end

  def find_module_path(mod_name) do
    # Search in priv/henk and test/henk
    path1 = "priv/henk/" <> String.replace(mod_name, ".", "/") <> ".henk"
    path2 = "test/henk/" <> String.replace(mod_name, ".", "/") <> ".henk"

    cond do
      File.exists?(path1) -> {:ok, path1}
      File.exists?(path2) -> {:ok, path2}
      true -> nil
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      Map.put(acc, name, term)
    end)
  end

  defp add_constructors_to_ctx(ind, ctx) do
    Enum.reduce(ind.constrs, ctx, fn {_, name, ty}, acc ->
      [{name, ty} | acc]
    end)
  end

  defp make_constr_term(idx, ind, ty, vars) do
    case ty do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        name = if x == "_", do: "a#{length(vars)}", else: x
        %AST.Lam{name: name, domain: a, body: make_constr_term(idx, ind, b, [name | vars])}

      _ ->
        args = Enum.reverse(vars) |> Enum.map(fn n -> %AST.Var{name: n} end)
        %AST.Constr{index: idx, inductive: ind, args: args}
    end
  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
