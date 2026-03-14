defmodule Mix.Tasks.Henk.Test do
  use Mix.Task

  @shortdoc "Run Henk integration tests"
  @moduledoc """
  Compiles all .henk files under test/henk/ and reports results.

  Options:
    --verbose   Show per-file output (OK / FAILED + reason).
                Without this flag only errors are printed (grep-friendly).

  Usage:
    mix henk.test
    mix henk.test --verbose
    mix henk.test --verbose | grep error | wc -l
  """

  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [verbose: :boolean])
    verbose = Keyword.get(opts, :verbose, false)

    test_files = Path.wildcard("test/henk/**/*.henk") ++ Path.wildcard("test/henk/*.henk")

    if test_files == [] and verbose do
      IO.puts("No .henk test files found under test/henk/")
    end

    results =
      Enum.map(test_files, fn file ->
        source = File.read!(file)

        case Henk.Compiler.compile_module(source, source_path: file, typecheck: true) do
          {:ok, mod, _} ->
            if verbose, do: IO.puts("ok: #{file} (#{mod})")
            :ok

          {:error, reason} ->
            msg = format_error(reason)
            IO.puts("error: #{file}: #{msg}")
            :error
        end
      end)

    failures = Enum.count(results, &(&1 == :error))

    if verbose do
      IO.puts("\n#{length(results)} files, #{failures} errors.")
    end

    if failures > 0, do: System.halt(1)
  end

  defp format_error({:type_error, reason}), do: "type error: #{inspect(reason, limit: 10)}"
  defp format_error({:erl_compile, errs}),  do: "compile error: #{inspect(errs, limit: 5)}"
  defp format_error(other),                 do: inspect(other, limit: 10)
end
