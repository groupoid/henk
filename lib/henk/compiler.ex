defmodule Henk.Compiler do
  @moduledoc """
  Main entry point for the Henk compiler.

  Compiles a .henk source string through:
    Lexer → Layout → Parser → Desugar (Church encoding) → Typechecker → Codegen → :compile
  """
  alias Henk.{Lexer, Layout, Parser, Desugar, Codegen, AST}
  alias Henk.Typechecker.Env

  # ── Compile ───────────────────────────────────────────────────────────────

  def compile_module(source, opts \\ []) do
    syntax = Keyword.get(opts, :syntax, :miranda)
    env = Keyword.get(opts, :env, %Env{})

    case parse_ast(source, syntax, opts) do
      {:ok, ast} ->
        do_compile(ast, source, env, opts)
      {:error, reason} -> {:error, reason}
      {:error, reason, _metadata} -> {:error, reason}
      err -> {:error, err}
    end
  end

  defp do_compile(ast, _source, env, opts) do
    # Build initial env by resolving imports
    env = resolve_imports(ast, env, opts)

    # Desugar: DeclValue expansion, Let -> App(Lam), etc.
    desugared = Desugar.desugar(ast, env)

    # Populate env with the declarations of this module
    final_env = populate_env(desugared, env)

    typecheck_res =
      if Keyword.get(opts, :typecheck, true) do
        case Henk.Typechecker.check_module(desugared, final_env) do
          {:ok, _} -> :ok
          :ok      -> :ok
          {:error, reason} -> {:error, {:type_error, reason}}
        end
      else
        :ok
      end

    if typecheck_res == :ok and Keyword.get(opts, :check_only, false) do
      {:ok, desugared.name, :check_only}
    else
      with :ok <- typecheck_res,
           {:ok, forms} <- Codegen.generate(desugared, final_env) do
        case :compile.forms(forms, [:return_errors, :debug_info]) do
          {:ok, mod, bin}              -> {:ok, mod, bin}
          {:error, errors, _warnings} -> {:error, {:erl_compile, errors}}
        end
      end
    end
  end

  # ── Env population ────────────────────────────────────────────────────────

  defp populate_env(%AST.Module{declarations: decls}, env) do
    Enum.reduce(decls, env, fn
      %AST.DeclValue{name: n, expr: e}, acc ->
        ty = Henk.Typechecker.infer(acc, e)
        %{acc | defs: Map.put(acc.defs, n, e), ctx: [{n, ty} | acc.ctx]}

      %AST.DeclForeign{name: n, erl_mod: erl_mod, erl_func: erl_func}, acc ->
        any = %AST.Var{name: "Any"}
        %{acc |
          defs:         Map.put(acc.defs, n, any),
          ctx:          [{n, any} | acc.ctx],
          foreign_defs: Map.put(acc.foreign_defs, n, {erl_mod, erl_func})}

      _, acc ->
        acc
    end)
  end

  # ── Import resolution ─────────────────────────────────────────────────────

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls} = mod, env, opts) do
    # Implicit Prelude for all non-Prelude modules
    env =
      if mod_name != "Prelude" do
        case load_module_to_env("Prelude", env, opts) do
          {:ok, new_env} -> new_env
          _              -> env
        end
      else
        env
      end

    # 1. Resolve explicit imports (Miranda style)
    env = Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        case load_module_to_env(name, acc, opts) do
          {:ok, new_env} -> new_env
          _              -> acc
        end
      _, acc ->
        acc
    end)

    # 2. Resolve implicit imports from qualified Var names (Morte/AUT-68 style)
    all_vars = AST.extract_vars(mod)
    Enum.reduce(all_vars, env, fn var_name, acc ->
      if String.contains?(var_name, ".") do
        parts = String.split(var_name, ".")
        mod_prefix = parts |> Enum.slice(0..-2//1) |> Enum.join(".")
        if mod_prefix != "" and mod_prefix != mod_name and not Map.has_key?(acc.defs, var_name) do
          case load_module_to_env(mod_prefix, acc, opts) do
            {:ok, new_env} -> new_env
            _              -> acc
          end
        else
          acc
        end
      else
        acc
      end
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    case find_module_path(mod_name) do
      {:ok, path} ->
        source = File.read!(path)
        
        # Detect syntax from path
        syntax = cond do
          Path.extname(path) == ".aut" -> :aut68
          String.contains?(path, "priv/morte") -> :morte
          true -> :miranda
        end

        with {:ok, mod} <- parse_ast(source, syntax, Keyword.put(opts, :module_name, mod_name)) do
          env_with_imports = resolve_imports(mod, env, opts)
          {_, type_constrs} = Desugar.collect_inductives(mod.declarations)
          env_with_constrs = %{env_with_imports | type_constrs: Map.merge(env_with_imports.type_constrs, type_constrs)}

          desugared = Desugar.desugar(mod, env_with_constrs)

          loaded_env =
            Enum.reduce(desugared.declarations, env_with_constrs, fn
              %AST.DeclValue{name: n, expr: e}, acc ->
                ty = Henk.Typechecker.infer(acc, e)
                qualified = "#{mod_name}.#{n}"
                acc
                |> put_in_env(n, e, ty, mod_name)
                |> put_in_env(qualified, e, ty, mod_name)

              %AST.DeclForeign{name: n, erl_mod: er_m, erl_func: er_f}, acc ->
                any = %AST.Var{name: "Any"}
                qualified = "#{mod_name}.#{n}"
                acc
                |> put_in_env(n, any, any, mod_name, {er_m, er_f})
                |> put_in_env(qualified, any, any, mod_name, {er_m, er_f})

              _, acc -> acc
            end)

          {:ok, loaded_env}
        else
          err -> {:error, err}
        end

      nil ->
        {:error, :module_not_found}
    end
  end

  def update_env_with_module(env, mod_name, source, syntax, opts \\ []) do
    with {:ok, mod} <- parse_ast(source, syntax, Keyword.put(opts, :module_name, mod_name)) do
      env_with_imports = resolve_imports(mod, env, opts)
      desugared = Desugar.desugar(mod, env_with_imports)

      Enum.reduce(desugared.declarations, env_with_imports, fn
        %AST.DeclValue{name: n, expr: e}, acc ->
          ty = Henk.Typechecker.infer(acc, e)
          qualified = "#{mod_name}.#{n}"
          acc
          |> put_in_env(n, e, ty, mod_name)
          |> put_in_env(qualified, e, ty, mod_name)

        %AST.DeclForeign{name: n, erl_mod: er_m, erl_func: er_f}, acc ->
          any = %AST.Var{name: "Any"}
          qualified = "#{mod_name}.#{n}"
          acc
          |> put_in_env(n, any, any, mod_name, {er_m, er_f})
          |> put_in_env(qualified, any, any, mod_name, {er_m, er_f})

        _, acc -> acc
      end)
    else
      _ -> env
    end
  end

  defp put_in_env(env, name, expr, type, mod_name, foreign \\ nil) do
    env1 = %{env |
      defs: Map.put(env.defs, name, expr),
      name_to_mod: Map.put(env.name_to_mod, name, mod_name),
      ctx: [{name, type} | env.ctx]
    }
    if foreign do
      %{env1 | foreign_defs: Map.put(env1.foreign_defs, name, foreign)}
    else
      env1
    end
  end

  defp parse_ast(source, syntax, opts) do
    case syntax do
      :miranda ->
        with {:ok, tokens} <- Lexer.lex(source),
             resolved <- Layout.resolve(tokens),
             {:ok, %AST.Module{} = mod, _rest} <- Parser.parse(resolved) do
          {:ok, mod}
        end

      :aut68 ->
        with {:ok, tokens} <- Henk.Lexer.AUT68.lex(source),
             {:ok, expr, _} <- Henk.Parser.AUT68.parse(tokens) do
          mod_name = Keyword.get(opts, :module_name, "Main")
          {:ok, %AST.Module{
            name: mod_name,
            declarations: [%AST.DeclValue{name: "main", expr: expr, binders: [], guards: [], where_decls: []}]
          }}
        end

      :morte ->
        with {:ok, tokens} <- Henk.Lexer.Morte.lex(source),
             {:ok, expr, _} <- Henk.Parser.Morte.parse(tokens) do
          mod_name = Keyword.get(opts, :module_name, "Main")
          {:ok, %AST.Module{
            name: mod_name,
            declarations: [%AST.DeclValue{name: "main", expr: expr, binders: [], guards: [], where_decls: []}]
          }}
        end
    end
  end

  def find_module_path(mod_name) do
    base = String.replace(mod_name, ".", "/")
    
    # Try different locations and extensions
    candidates = [
      "priv/henk/#{base}.henk",
      "priv/aut-68/#{base}.aut",
      "priv/aut-68/#{base}/@.aut",
      "priv/morte/#{base}",
      "priv/morte/#{base}/@",
      "test/henk/#{base}.henk"
    ]

    Enum.find_value(candidates, nil, fn path ->
      if File.exists?(path) and not File.dir?(path), do: {:ok, path}
    end)
  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
