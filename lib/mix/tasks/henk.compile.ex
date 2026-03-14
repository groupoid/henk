defmodule Mix.Tasks.Henk.Compile do
  use Mix.Task

  @shortdoc "Compile Henk files"
  def run(args) do
    {opts, files, _} = OptionParser.parse(args, switches: [out: :string, syntax: :string], aliases: [o: :out])
    out_dir = Keyword.get(opts, :out, "ebin")
    syntax_arg = Keyword.get(opts, :syntax)
    File.mkdir_p!(out_dir)

    Enum.each(files, fn file ->
      source = File.read!(file)

      # Detect syntax:
      syntax = cond do
        syntax_arg == "aut68" -> :aut68
        syntax_arg == "aut-68" -> :aut68
        syntax_arg == "morte" -> :morte
        syntax_arg == "miranda" -> :miranda
        syntax_arg == "henk" -> :miranda
        Path.extname(file) == ".aut" -> :aut68
        true -> :miranda
      end

      IO.write("Compiling [#{syntax}] #{file}... ")

      case Henk.Compiler.compile_module(source, [source_path: file, syntax: syntax] ++ opts) do
        {:ok, mod, bin} ->
          beam_path = Path.join(out_dir, "#{mod}.beam")
          File.write!(beam_path, bin)
          IO.puts("OK -> #{beam_path}")

        {:error, reason} ->
          IO.puts("FAILED: #{inspect(reason)}")
      end
    end)
  end
end
