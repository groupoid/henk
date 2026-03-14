defmodule Mix.Tasks.Henk.Base do
  use Mix.Task

  @shortdoc "Compile Henk standard library"
  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [check_only: :boolean])
    check_only = Keyword.get(opts, :check_only, false)

    if check_only do
      IO.puts("Typechecking Henk base library...")
    else
      IO.puts("Compiling Henk base library...")
    end

    # Discover all .henk files — priv/henk/ (stdlib) and test/henk/ (demos).
    # Top-level files first so subdirectory modules can import them.
    priv_top  = Path.wildcard("priv/henk/*.henk")
    priv_sub  = Path.wildcard("priv/henk/**/*.henk")
    test_top  = Path.wildcard("test/henk/*.henk")
    test_sub  = Path.wildcard("test/henk/**/*.henk")
    base_files = priv_top ++ priv_sub ++ test_top ++ test_sub

    out_dir = "ebin"
    File.mkdir_p!(out_dir)

    Enum.each(base_files, fn file ->
      action_str = if check_only, do: "Checking", else: "Compiling"
      IO.write("  #{action_str} #{file}... ")
      source = File.read!(file)

      case Henk.Compiler.compile_module(source, [source_path: file] ++ opts) do
        {:ok, _mod, :check_only} ->
          IO.puts("OK (checked)")

        {:ok, mod, bin} ->
          beam_path = Path.join(out_dir, "#{mod}.beam")
          File.write!(beam_path, bin)
          IO.puts("OK")

        {:error, reason} ->
          IO.puts("FAILED: #{inspect(reason, pretty: true)}")
      end
    end)

    finished_str = if check_only, do: "verification", else: "compilation"
    IO.puts("\nHenk base library #{finished_str} finished.")
  end
end
