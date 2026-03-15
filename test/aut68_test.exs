
# 1. Lexing
source = "(A: *) (a:A) a"
IO.puts("Source: #{source}")
{:ok, tokens} = Henk.Lexer.AUT68.lex(source)
IO.inspect(tokens, label: "Tokens")

# 2. Parsing
case Henk.Parser.AUT68.parse(tokens) do
  {:ok, expr, rest} ->
    IO.puts("\nParsed AST: #{inspect expr}")
    IO.puts("Pretty: #{Henk.AST.to_string(expr)}")
    IO.inspect(rest, label: "Rest")
  err ->
    IO.inspect(err, label: "Parse Error")
end

# 3. Test Pi
source2 = "[A: *] [a:A] A"
IO.puts("\nSource 2: #{source2}")
{:ok, tokens2} = Henk.Lexer.AUT68.lex(source2)
case Henk.Parser.AUT68.parse(tokens2) do
  {:ok, expr, _} ->
    IO.puts("Parsed AST: #{inspect expr}")
    IO.puts("Pretty: #{Henk.AST.to_string(expr)}")
  err ->
    IO.inspect(err, label: "Parse Error")
end

# 4. Test Pi Type (non-dependent)
source3 = "[A: *] [x: A] A"
IO.puts("\nSource 3: #{source3}")
{:ok, tokens3} = Henk.Lexer.AUT68.lex(source3)
case Henk.Parser.AUT68.parse(tokens3) do
  {:ok, expr, _} ->
    IO.puts("Parsed AST: #{inspect expr}")
    IO.puts("Pretty: #{Henk.AST.to_string(expr)}")
  err ->
    IO.inspect(err, label: "Parse Error")
end
