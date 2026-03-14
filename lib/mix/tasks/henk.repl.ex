defmodule Mix.Tasks.Henk.Repl do
  use Mix.Task

  alias Henk.{Lexer, Layout, Parser, Desugar, Typechecker, AST}

  @shortdoc "Henk interactive REPL"

  def run(_) do
    IO.puts(
      "🧊 Henk Programming Language version 0.3.11 [Miranda Syntax]\n" <>
      "Copyright (c) 2016-2026 Groupoid Infinity\n" <>
      "https://groupoid.github.io/henk/\n" <>
      "Commands: import <Mod>  run_io <Mod.fn>  run_ioi <Mod.fn>  :q\n"
    )

    # Compile and load all .henk modules into both typechecker env AND Erlang VM.
    # priv/henk first (stdlib, in dependency order), then test/henk (demos).
    priv_paths = Path.wildcard("priv/henk/*.henk") ++ Path.wildcard("priv/henk/**/*.henk")
    test_paths = Path.wildcard("test/henk/*.henk") ++ Path.wildcard("test/henk/**/*.henk")
    all_paths  = priv_paths ++ test_paths

    env =
      Enum.reduce(all_paths, %Typechecker.Env{}, fn path, acc_env ->
        mod_name = path_to_mod_name(path)
        src      = File.read!(path)

        # Load into typechecker env
        acc_env =
          case Henk.Compiler.load_module_to_env(mod_name, acc_env) do
            {:ok, new_env} -> new_env
            _              -> acc_env
          end

        # Compile and beam-load into Erlang VM
        case Henk.Compiler.compile_module(src, typecheck: false) do
          {:ok, mod, bin} -> Henk.Compiler.load_module(mod, bin)
          _               -> :skip
        end

        acc_env
      end)

    loop(env)
  end

  # ── REPL loop ──────────────────────────────────────────────────────────────

  defp loop(env) do
    input = IO.gets("henk> ")

    case input do
      nil    -> :ok
      ":q\n" -> :ok
      "\n"   -> loop(env)

      "import " <> rest ->
        mod_name = String.trim(rest)
        case Henk.Compiler.load_module_to_env(mod_name, env) do
          {:ok, new_env} ->
            IO.puts("Loaded #{mod_name}.")
            loop(new_env)
          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end

      "run_io " <> rest ->
        run_program(String.trim(rest), :io, env)
        loop(env)

      "run_ioi " <> rest ->
        run_program(String.trim(rest), :ioi, env)
        loop(env)

      _ ->
        case eval(input, env) do
          {:ok, result} ->
            IO.puts("= #{AST.to_string(result)}")
            loop(env)
          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end
    end
  end

  # ── run_io / run_ioi ───────────────────────────────────────────────────────
  #
  # run_program "Test.Recursive.main" :io env
  #   → compiles Test.Recursive, loads beam, calls IO.run_io().(Test.Recursive.main())
  #
  # run_program "Test.Corecursive.corecursive" :ioi env
  #   → compiles Test.Corecursive, loads beam, calls IOI.run_ioi().(Test.Corecursive.corecursive())

  defp run_program(qualified, mode, _env) do
    with {:ok, mod_atom, func_atom} <- split_qualified(qualified),
         :ok                        <- ensure_beam_loaded(mod_atom),
         value                      <- apply(mod_atom, func_atom, []) do
      case mode do
        :io  ->
          runner = apply(:"Control.IO", :run_io, [])
          runner.(value)

        :ioi ->
          runner = apply(:"Control.IOI", :run_ioi, [])
          runner.(value)
      end
    else
      {:error, err} -> IO.puts("run error: #{inspect(err)}")
    end
  rescue
    e -> IO.puts("runtime error: #{Exception.message(e)}")
  end

  # Parse "Test.Recursive.main" → {:ok, :"Test.Recursive", :main}
  defp split_qualified(qualified) do
    parts = String.split(qualified, ".")
    case parts do
      [_] ->
        {:error, :qualify_as_Module_dot_function}
      _ ->
        {mod_parts, [func_part]} = Enum.split(parts, length(parts) - 1)
        mod_name = Enum.join(mod_parts, ".")
        {:ok, String.to_atom(mod_name), String.to_atom(func_part)}
    end
  end

  # Compile and beam-load a module if not already in the VM
  defp ensure_beam_loaded(mod_atom) do
    if :code.is_loaded(mod_atom) != false do
      :ok
    else
      mod_name = Atom.to_string(mod_atom)
      case Henk.Compiler.find_module_path(mod_name) do
        {:ok, path} ->
          src = File.read!(path)
          case Henk.Compiler.compile_module(src, typecheck: false) do
            {:ok, mod, bin} -> Henk.Compiler.load_module(mod, bin); :ok
            {:error, err}   -> {:error, {:compile, err}}
          end
        nil -> {:error, {:not_found, mod_name}}
      end
    end
  end

  # ── Expression evaluator ───────────────────────────────────────────────────

  defp eval(input, env) do
    input = String.trim(input)
    if input == "" do
      {:error, :empty_input}
    else
      with {:ok, tokens}   <- Lexer.lex(input),
           resolved        <- Layout.resolve(tokens),
           {:ok, expr, _}  <- Parser.parse_expression(resolved) do
        desugared = Desugar.desugar_expr(expr, env)
        {:ok, Typechecker.normalize(env, desugared)}
      else
        err -> {:error, err}
      end
    end
  end

  # ── Helpers ────────────────────────────────────────────────────────────────

  defp path_to_mod_name(path) do
    Path.split(path)
    |> Enum.drop_while(&(&1 != "henk"))
    |> Enum.drop(1)
    |> List.update_at(-1, &Path.rootname/1)
    |> Enum.join(".")
  end
end
