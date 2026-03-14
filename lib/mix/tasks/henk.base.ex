defmodule Mix.Tasks.Henk.Base do
  use Mix.Task

  @shortdoc "Compile Henk standard library"
  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [check_only: :boolean, syntax: :string])
    check_only = Keyword.get(opts, :check_only, false)
    syntax_arg = Keyword.get(opts, :syntax)

    if check_only do
      IO.puts("Typechecking Henk base library...")
    else
      IO.puts("Compiling Henk base library...")
    end

    # Discover all .henk, .aut, and morte files
    priv_henk  = Path.wildcard("priv/henk/**/*.henk")
    priv_aut   = Path.wildcard("priv/aut-68/**/*.aut")
    priv_morte = Path.wildcard("priv/morte/**/*") |> Enum.reject(&File.dir?/1)
    test_henk = Path.wildcard("test/henk/**/*.henk")
    
    all_files = priv_henk ++ priv_aut ++ priv_morte ++ test_henk

    base_files = if syntax_arg do
      target_syntax = case syntax_arg do
        "aut68" -> :aut68
        "aut-68" -> :aut68
        "morte" -> :morte
        "miranda" -> :miranda
        "henk" -> :miranda
        _ -> nil
      end

      Enum.filter(all_files, fn file ->
        file_syntax = cond do
          Path.extname(file) == ".aut" -> :aut68
          String.contains?(file, "priv/morte") -> :morte
          true -> :miranda
        end
        file_syntax == target_syntax
      end)
    else
      all_files
    end

    Enum.reduce(base_files, %Henk.Typechecker.Env{}, fn file, acc_env ->
      action_str = if check_only, do: "Checking", else: "Compiling"
      source = File.read!(file)

      syntax = cond do
        syntax_arg == "aut68" -> :aut68
        syntax_arg == "morte" -> :morte
        syntax_arg == "miranda" -> :miranda
        Path.extname(file) == ".aut" -> :aut68
        String.contains?(file, "priv/morte") -> :morte
        true -> :miranda
      end

      syntax_dir = case syntax do
        :aut68   -> "aut-68"
        :morte   -> "morte"
        :miranda -> "miranda"
      end
      out_dir = Path.join("ebin", syntax_dir)
      File.mkdir_p!(out_dir)

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

      module_name = module_name 
        |> String.replace_trailing(".@", "") 
        |> String.replace_trailing("@", "")
        |> String.replace_trailing(".", "")
      module_name = if module_name == "", do: "Main", else: module_name

      IO.write("  #{action_str} [#{syntax}] #{file} -> #{module_name}... ")

      compile_opts = [source_path: file, syntax: syntax, module_name: module_name, env: acc_env] ++ opts
      case Henk.Compiler.compile_module(source, compile_opts) do
        {:ok, _mod, :check_only} ->
          IO.puts("OK (checked)")
          acc_env

        {:ok, mod, bin} ->
          beam_path = Path.join(out_dir, "#{mod}.beam")
          File.write!(beam_path, bin)
          Henk.Compiler.load_module(mod, bin)
          IO.puts("OK")
          Henk.Compiler.update_env_with_module(acc_env, module_name, source, syntax, opts)

        {:error, reason} ->
          IO.puts("FAILED: #{inspect(reason, pretty: true)}")
          acc_env
      end
    end)

    finished_str = if check_only, do: "verification", else: "compilation"
    IO.puts("\nHenk base library #{finished_str} finished.")
  end
end
