defmodule Mix.Tasks.Henk.Repl do
  use Mix.Task

  alias Henk.{Lexer, Layout, Parser, Desugar, Typechecker, AST}

  @shortdoc "Henk interactive REPL"

  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [syntax: :string])
    syntax_arg = Keyword.get(opts, :syntax, "miranda")
    syntax = case syntax_arg do
      "aut-68" -> :aut68
      "aut68"  -> :aut68
      "morte"  -> :morte
      "miranda" -> :miranda
      "henk" -> :miranda
      _ -> :miranda
    end

    IO.puts(
      "🧊 Henk Programming Language version 0.3.11 [#{syntax_arg} syntax]\n" <>
        "Copyright (c) 2015-2026 Groupoid Infinity\n" <>
        "https://groupoid.github.io/henk/\n"
    )

    # Add ebin subfolders to code path
    :code.add_pathz(~c"ebin/miranda")
    :code.add_pathz(~c"ebin/aut-68")
    :code.add_pathz(~c"ebin/morte")

    # Compile and load all modules
    priv_paths = Path.wildcard("priv/henk/**/*.henk") ++
                 Path.wildcard("priv/aut-68/**/*.aut") ++
                 Path.wildcard("priv/morte/**/*") |> Enum.reject(&File.dir?/1)
    
    test_paths = Path.wildcard("test/henk/**/*.henk")
    all_paths = priv_paths ++ test_paths

    env =
      Enum.reduce(all_paths, %Typechecker.Env{}, fn path, acc_env ->
        # Detect syntax from path
        file_syntax = cond do
          Path.extname(path) == ".aut" -> :aut68
          String.contains?(path, "priv/morte") -> :morte
          true -> :miranda
        end

        # Derive module name from path
        mod_name = derive_module_name(path)

        # Load into typechecker env
        acc_env =
          case Henk.Compiler.load_module_to_env(mod_name, acc_env, syntax: file_syntax) do
            {:ok, new_env} -> new_env
            _ -> acc_env
          end

        # Compile and beam-load into Erlang VM if not matching the REPL's main syntax
        # (Usually we want everything available)
        src = File.read!(path)
        case Henk.Compiler.compile_module(src, typecheck: false, syntax: file_syntax, module_name: mod_name) do
          {:ok, mod, bin} -> Henk.Compiler.load_module(mod, bin)
          _ -> :skip
        end

        acc_env
      end)

    loop(env, syntax, syntax_arg)
  end

  defp derive_module_name(file) do
    module_name = cond do
      String.contains?(file, "priv/henk") ->
        file |> Path.relative_to("priv/henk") |> Path.rootname() |> String.replace("/", ".")
      String.contains?(file, "priv/aut-68") ->
        file |> Path.relative_to("priv/aut-68") |> Path.rootname() |> String.replace("/", ".")
      String.contains?(file, "priv/morte") ->
        file |> Path.relative_to("priv/morte") |> String.replace("/", ".")
      String.contains?(file, "test/henk") ->
        file |> Path.relative_to("test/henk") |> Path.rootname() |> String.replace("/", ".")
      true ->
        "Main"
    end

    # Normalize: remove trailing @ or dot
    module_name = module_name 
      |> String.replace_trailing(".@", "") 
      |> String.replace_trailing("@", "")
      |> String.replace_trailing(".", "")
    if module_name == "", do: "Main", else: module_name
  end

  # ── REPL loop ──────────────────────────────────────────────────────────────

  defp loop(env, syntax, syntax_name) do
    prompt = "#{syntax_name}> "
    input = IO.gets(prompt)

    case input do
      nil -> :ok
      ":q\n" -> :ok
      "\n" -> loop(env, syntax, syntax_name)

      ":syntax " <> rest ->
        name = String.trim(rest)
        {new_syntax, final_name} = case name do
          "aut-68" -> {:aut68, "aut-68"}
          "aut68"  -> {:aut68, "aut68"}
          "morte"  -> {:morte, "morte"}
          "miranda" -> {:miranda, "miranda"}
          "henk"    -> {:miranda, "henk"}
          _ -> {syntax, syntax_name}
        end
        if new_syntax != syntax or final_name != syntax_name do
          IO.puts("Switched to #{new_syntax} syntax.")
          loop(env, new_syntax, final_name)
        else
          IO.puts("Unknown or same syntax: #{name}")
          loop(env, syntax, syntax_name)
        end

      "import " <> rest ->
        mod_name = String.trim(rest)
        case Henk.Compiler.load_module_to_env(mod_name, env) do
          {:ok, new_env} ->
            IO.puts("Loaded #{mod_name}.")
            loop(new_env, syntax, syntax_name)
          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax, syntax_name)
        end

      ":print " <> rest ->
        handle_introspection(String.trim(rest), :print, env, syntax)
        loop(env, syntax, syntax_name)

      ":eval " <> rest ->
        handle_introspection(String.trim(rest), :eval, env, syntax)
        loop(env, syntax, syntax_name)

      ":check " <> rest ->
        handle_introspection(String.trim(rest), :check, env, syntax)
        loop(env, syntax, syntax_name)

      "run_io " <> rest ->
        run_program(String.trim(rest), :io, env)
        loop(env, syntax, syntax_name)

      "run_ioi " <> rest ->
        run_program(String.trim(rest), :ioi, env)
        loop(env, syntax, syntax_name)

      _ ->
        case eval(input, env, syntax) do
          :stop -> :ok
          {:ok, result} ->
            IO.puts("= #{AST.to_string(result)}")
            loop(env, syntax, syntax_name)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax, syntax_name)
        end
    end
  end

  defp handle_introspection(input, mode, env, syntax) do
    case parse_and_desugar(input, env, syntax) do
      {:ok, term} ->
        case Typechecker.infer(env, term) do
          {:error, err} ->
            IO.puts("Type Error: #{inspect(err)}")

          ty ->
            case mode do
              :check ->
                IO.puts("TYPE: #{AST.to_string(ty)}")

              :eval ->
                norm = Typechecker.normalize(env, term)
                IO.puts("TYPE: #{AST.to_string(ty)}")
                IO.puts("TERM: #{AST.to_string(norm)}")

              :print ->
                case ty do
                  %AST.Universe{} ->
                    IO.puts("TYPE: #{AST.to_string(term)}")

                  _ ->
                    IO.puts("TYPE: #{AST.to_string(ty)}")
                    IO.puts("TERM: #{AST.to_string(term)}")
                end
            end
        end

      {:error, err} ->
        IO.puts("Error: #{inspect(err)}")
    end
  end

  defp parse_and_desugar(input, env, syntax) do
    input = String.trim(input)

    case syntax do
      :miranda ->
        with {:ok, tokens} <- Lexer.lex(input),
             resolved <- Layout.resolve(tokens),
             {:ok, expr, _} <- Parser.parse_expression(resolved) do
          {:ok, Desugar.desugar_expr(expr, env)}
        end

      :aut68 ->
        with {:ok, tokens} <- Henk.Lexer.AUT68.lex(input),
             {:ok, expr, _} <- Henk.Parser.AUT68.parse(tokens) do
          {:ok, Desugar.desugar_expr(expr, env)}
        end

      :morte ->
        with {:ok, tokens} <- Henk.Lexer.Morte.lex(input),
             {:ok, expr, _} <- Henk.Parser.Morte.parse(tokens) do
          {:ok, Desugar.desugar_expr(expr, env)}
        end
    end
  end

  defp run_program(qualified, mode, _env) do
    with {:ok, mod_atom, func_atom} <- split_qualified(qualified),
         :ok <- ensure_beam_loaded(mod_atom),
         value <- apply(mod_atom, func_atom, []) do
      case mode do
        :io ->
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

  defp split_qualified(qualified) do
    parts = String.split(qualified, ".")
    case parts do
      [_] -> {:error, :qualify_as_Module_dot_function}
      _ ->
        {mod_parts, [func_part]} = Enum.split(parts, length(parts) - 1)
        mod_name = Enum.join(mod_parts, ".")
        {:ok, String.to_atom(mod_name), String.to_atom(func_part)}
    end
  end

  defp ensure_beam_loaded(mod_atom) do
    if :code.is_loaded(mod_atom) != false do
      :ok
    else
      mod_name = Atom.to_string(mod_atom)
      case Henk.Compiler.find_module_path(mod_name) do
        {:ok, path} ->
          src = File.read!(path)
          # Detect syntax from path for on-demand loading
          syntax = cond do
            Path.extname(path) == ".aut" -> :aut68
            String.contains?(path, "priv/morte") -> :morte
            true -> :miranda
          end
          case Henk.Compiler.compile_module(src, typecheck: false, syntax: syntax, module_name: mod_name) do
            {:ok, mod, bin} ->
              Henk.Compiler.load_module(mod, bin)
              :ok
            {:error, err} ->
              {:error, {:compile, err}}
          end
        nil ->
          {:error, {:not_found, mod_name}}
      end
    end
  end

  defp eval(:eof, _, _), do: :stop
  defp eval(input, env, syntax) do
    case parse_and_desugar(input, env, syntax) do
      {:ok, term} -> {:ok, Typechecker.normalize(env, term)}
      err -> err
    end
  end
end
