defmodule Mix.Tasks.Henk.Test do
  use Mix.Task

  @shortdoc "Run Henk tests"
  def run(_) do
    IO.puts("Running Henk tests...")

    test_files = Path.wildcard("test/henk/**/*.henk")

    results =
      Enum.map(test_files, fn file ->
        IO.write("  Testing #{file}... ")
        source = File.read!(file)

        case Henk.Compiler.compile_module(source, source_path: file) do
          {:ok, mod, _bin} ->
            IO.puts("OK (#{mod})")
            :ok

          {:error, _reason} ->
            IO.puts("FAILED")
            :error
        end
      end)

    failures = Enum.count(results, &(&1 == :error))

    if failures > 0 do
      IO.puts("\n#{failures} tests failed.")
      System.halt(1)
    else
      IO.puts("\nAll Henk tests passed.")
    end
  end
end
