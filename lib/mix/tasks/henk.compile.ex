defmodule Mix.Tasks.Henk.Compile do
  use Mix.Task

  @shortdoc "Compile Henk files"
  def run(args) do
    {opts, files, _} = OptionParser.parse(args, switches: [out: :string], aliases: [o: :out])
    out_dir = Keyword.get(opts, :out, "ebin")
    File.mkdir_p!(out_dir)

    Enum.each(files, fn file ->
      IO.puts("Compiling #{file}...")
      source = File.read!(file)

      case Henk.Compiler.compile_module(source, source_path: file) do
        {:ok, mod, bin} ->
          beam_path = Path.join(out_dir, "#{mod}.beam")
          File.write!(beam_path, bin)
          IO.puts("Successfully compiled to #{beam_path}")

        {:error, reason} ->
          IO.puts("Error compiling #{file}: #{inspect(reason)}")
      end
    end)
  end
end
