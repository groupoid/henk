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

    # Auto-load all modules from priv/henk and test/henk
    paths = Path.wildcard("{priv,test}/henk/**/*.henk")

    env =
      Enum.reduce(paths, env, fn path, acc_env ->
        # Extract module name from path (e.g., priv/henk/Data/Nat.henk -> Data.Nat)
        parts = Path.split(path)

        # Drop until we find 'henk'
        mod_parts =
          parts
          |> Enum.drop_while(&(&1 != "henk"))
          |> Enum.drop(1)
          # Drop extension
          |> List.update_at(-1, &Path.rootname/1)

        mod_name = Enum.join(mod_parts, ".")

        case load_module(mod_name, acc_env) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            new_env

          {:error, err} ->
            IO.puts("Error loading #{mod_name}: #{inspect(err)}")
            acc_env
        end
      end)

    loop(env)
  end

  defp loop(env) do
    input = IO.gets("henk> ")

    case input do
      nil ->
        :ok

      ":q\n" ->
        :ok

      "\n" ->
        loop(env)

      "import " <> rest ->
        mod_name = String.trim(rest)

        case load_module(mod_name, env) do
          {:ok, new_env} ->
            loop(new_env)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end

      _ ->
        case eval(input, env) do
          {:ok, result} ->
            IO.puts("Result: #{AST.to_string(result)}")
            loop(env)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end
    end
  end

  defp load_module(mod_name, env) do
    # Try to find the file in priv/henk or test/henk
    path1 = "priv/henk/" <> String.replace(mod_name, ".", "/") <> ".henk"
    path2 = "test/henk/" <> String.replace(mod_name, ".", "/") <> ".henk"

    path = if File.exists?(path1), do: path1, else: path2

    if File.exists?(path) do
      source = File.read!(path)

      with {:ok, tokens} <- Lexer.lex(source),
           resolved <- Layout.resolve(tokens),
           {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do
        # Add declarations to env.defs and env.env
        {new_defs, new_types} =
          Enum.reduce(mod.declarations, {env.defs, env.env}, fn
            %AST.DeclValue{} = v, {d_acc, t_acc} ->
              current_env = %{env | defs: d_acc, env: t_acc}
              desugared_v = Desugar.desugar_decl(v, current_env)
              IO.puts("  Defining: #{desugared_v.name}")
              {Map.put(d_acc, desugared_v.name, desugared_v.expr), t_acc}

            %AST.DeclData{} = data, {d_acc, t_acc} ->
              current_env = %{env | defs: d_acc, env: t_acc}
              desugared_ind = Desugar.desugar_decl(data, current_env)
              new_t_acc = Map.put(t_acc, desugared_ind.name, desugared_ind)
              new_d_acc = add_constructors(desugared_ind, d_acc)
              {new_d_acc, new_t_acc}

            _, acc ->
              acc
          end)

        {:ok, %{env | defs: new_defs, env: new_types}}
      else
        err -> {:error, err}
      end
    else
      {:error, :module_not_found}
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      Map.put(acc, name, term)
    end)
  end

  def make_constr_term(idx, ind, ty, vars) do
    case ty do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        name = if x == "_", do: "a#{length(vars)}", else: x
        %AST.Lam{name: name, domain: a, body: make_constr_term(idx, ind, b, [name | vars])}

      _ ->
        args = Enum.reverse(vars) |> Enum.map(fn n -> %AST.Var{name: n} end)
        %AST.Constr{index: idx, inductive: ind, args: args}
    end
  end

  defp eval(input, env) do
    # Trim input
    input = String.trim(input)

    if input == "" do
      {:error, :empty_input}
    else
      with {:ok, tokens} <- Lexer.lex(input),
           resolved <- Layout.resolve(tokens),
           {:ok, expr, _} <- Parser.parse_expression(resolved) do
        desugared = Desugar.desugar_expression(expr, env)
        # Normalize
        {:ok, Typechecker.normalize(env, desugared)}
      else
        err -> {:error, err}
      end
    end
  end
end
