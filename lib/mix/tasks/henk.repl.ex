defmodule Mix.Tasks.Henk.Repl do
  use Mix.Task

  alias Henk.{Lexer, Layout, Parser, Desugar, Typechecker, AST}

  @shortdoc "Henk interactive REPL"
  def run(_) do
    IO.puts("🧊 Henk Programming Language version 0.3.11 [Miranda Syntax]\n" <>
            "Copyright (c) 2016-2026 Groupoid Infinity\n" <>
            "https://groupoid.github.io/henk/\n"
            )

    env = %Typechecker.Env{}

    # Auto-load all modules from priv/henk
    paths = Path.wildcard("{priv,test}/henk/**/*.henk") ++ Path.wildcard("{priv,test}/henk/*.henk")

    env =
      Enum.reduce(paths, env, fn path, acc_env ->
        mod_parts =
          Path.split(path)
          |> Enum.drop_while(&(&1 != "henk"))
          |> Enum.drop(1)
          |> List.update_at(-1, &Path.rootname/1)

        mod_name = Enum.join(mod_parts, ".")
        case load_module(mod_name, acc_env) do
          {:ok, new_env} -> new_env
          {:error, _}    -> acc_env
        end
      end)

    loop(env)
  end

  defp loop(env) do
    input = IO.gets("henk> ")

    case input do
      nil     -> :ok
      ":q\n"  -> :ok
      "\n"    -> loop(env)

      "import " <> rest ->
        mod_name = String.trim(rest)
        case load_module(mod_name, env) do
          {:ok, new_env} -> loop(new_env)
          {:error, err}  ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end

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

  defp load_module(mod_name, env) do
    Henk.Compiler.load_module_to_env(mod_name, env)
  end

  defp eval(input, env) do
    input = String.trim(input)
    if input == "" do
      {:error, :empty_input}
    else
      with {:ok, tokens}    <- Lexer.lex(input),
           resolved         <- Layout.resolve(tokens),
           {:ok, expr, _}   <- Parser.parse_expression(resolved) do
        desugared = Desugar.desugar_expr(expr, env)
        {:ok, Typechecker.normalize(env, desugared)}
      else
        err -> {:error, err}
      end
    end
  end
end
