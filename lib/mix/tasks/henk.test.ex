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
    {opts, _, _} = OptionParser.parse(args, switches: [verbose: :boolean, syntax: :string])
    verbose = Keyword.get(opts, :verbose, false)
    syntax_arg = Keyword.get(opts, :syntax)

    target_syntax =
      case syntax_arg do
        "aut68" -> :aut68
        "aut-68" -> :aut68
        "morte" -> :morte
        "miranda" -> :miranda
        "henk" -> :miranda
        nil -> nil
        _ -> nil
      end

    all_test_files =
      (Path.wildcard("test/henk/**/*.{henk,aut}") ++
         Path.wildcard("test/morte/**/*") ++
         Path.wildcard("test/auth-68/**/*"))
      |> Enum.uniq()

    test_files =
      if target_syntax do
        Enum.filter(all_test_files, fn file ->
          if File.dir?(file), do: false, else: file_syntax(file) == target_syntax
        end)
      else
        Enum.reject(all_test_files, &File.dir?/1)
      end

    if test_files == [] and verbose do
      IO.puts("No matching test files found.")
    end

    results =
      Enum.map(test_files, fn file ->
        case File.read(file) do
          {:ok, source} ->
            syntax = file_syntax(file)
            IO.write("  Compiling [#{syntax}] #{file}... ")

            case Henk.Compiler.compile_module(
                   source,
                   [source_path: file, typecheck: true, syntax: syntax] ++ opts
                 ) do
              {:ok, mod, _} ->
                IO.puts(IO.ANSI.green() <> "OK" <> IO.ANSI.reset() <> " (#{mod})")
                :ok

              {:error, reason} ->
                msg = format_error(reason)
                IO.puts(IO.ANSI.red() <> "FAILED" <> IO.ANSI.reset() <> ": #{msg}")
                :error
            end

          _ ->
            IO.puts(IO.ANSI.red() <> "FAILED" <> IO.ANSI.reset() <> ": could not read file")
            :error
        end
      end)

    failures = Enum.count(results, &(&1 == :error))

    if verbose do
      IO.puts("\n#{length(results)} files, #{failures} errors.")
    end

    if failures > 0, do: System.halt(1)
  end

  defp file_syntax(file) do
    cond do
      Path.extname(file) == ".aut" -> :aut68
      String.contains?(file, "test/auth-68") -> :aut68
      String.contains?(file, "test/morte") -> :morte
      String.contains?(file, "priv/morte") -> :morte
      true -> :miranda
    end
  end

  defp format_error({:type_error, reason}), do: "type error: #{inspect(reason, limit: 10)}"
  defp format_error({:erl_compile, errs}), do: "compile error: #{inspect(errs, limit: 5)}"
  defp format_error(other), do: inspect(other, limit: 10)
end
