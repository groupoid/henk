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
    with {:ok, tokens}      <- Lexer.lex(source),
         resolved           <- Layout.resolve(tokens),
         {:ok, ast, _rest}  <- Parser.parse(resolved) do

      # Build initial env by resolving imports
      env = resolve_imports(ast, %Env{}, opts)

      # Desugar: DeclData → Church, Case → fold, Let → App(Lam)
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
    else
      {:error, _} = err -> err
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

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
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

    Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        case load_module_to_env(name, acc, opts) do
          {:ok, new_env} -> new_env
          _              -> acc
        end
      _, acc ->
        acc
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    case find_module_path(mod_name) do
      {:ok, path} ->
        source = File.read!(path)

        with {:ok, tokens}     <- Lexer.lex(source),
             resolved          <- Layout.resolve(tokens),
             {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do

          env_with_imports = resolve_imports(mod, env, opts)
          desugared = Desugar.desugar(mod, env_with_imports)

          loaded_env =
            Enum.reduce(desugared.declarations, env_with_imports, fn
              %AST.DeclValue{name: n, expr: e}, acc ->
                ty = Henk.Typechecker.infer(acc, e)
                %{acc |
                  defs: Map.put(acc.defs, n, e),
                  name_to_mod: Map.put(acc.name_to_mod, n, mod_name),
                  ctx: [{n, ty} | acc.ctx]}

              %AST.DeclForeign{name: n, erl_mod: erl_mod, erl_func: erl_func}, acc ->
                any = %AST.Var{name: "Any"}
                %{acc |
                  defs:         Map.put(acc.defs, n, any),
                  name_to_mod:  Map.put(acc.name_to_mod, n, mod_name),
                  ctx:          [{n, any} | acc.ctx],
                  foreign_defs: Map.put(acc.foreign_defs, n, {erl_mod, erl_func})}

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

  def find_module_path(mod_name) do
    base = String.replace(mod_name, ".", "/")
    candidates = [
      "priv/henk/#{base}.henk",
      "test/henk/#{base}.henk"
    ]

    Enum.find_value(candidates, nil, fn path ->
      if File.exists?(path), do: {:ok, path}
    end)
  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
