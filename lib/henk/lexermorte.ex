defmodule Henk.Lexer.Morte do
  @moduledoc """
  Lexer for Morte syntax.
  Supports UTF-8 binders (λ, ∀, Π), backslash lambda (\\), and Morte forall (\\/).
  Handles -- comments and correctly identifies #path identifiers including [ ].
  """

  def lex(input) do
    lex(String.codepoints(input), 1, 1, [])
  end

  defp lex([], _line, _col, acc), do: {:ok, Enum.reverse(acc)}

  defp lex(["\n" | rest], line, _col, acc), do: lex(rest, line + 1, 1, acc)
  defp lex([s | rest], line, col, acc) when s in [" ", "\r", "\t"] do
    new_col = if s == "\t", do: col + 4, else: col + 1
    lex(rest, line, new_col, acc)
  end

  # Comments (PureScript/Haskell style --)
  defp lex(["-", "-" | rest], line, col, acc) do
    rest2 = Enum.drop_while(rest, fn c -> c != "\n" end)
    lex(rest2, line, col, acc)
  end

  # Special symbols
  defp lex(["(" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:left_paren, line, col} | acc])
  defp lex([")" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:right_paren, line, col} | acc])
  defp lex([":" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:colon, line, col} | acc])

  # UTF-8 symbols & Binders
  defp lex(["\\" , "/" | rest], line, col, acc), do: lex(rest, line, col + 2, [{:forall, line, col} | acc])
  defp lex(["λ" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:backslash, line, col} | acc])
  defp lex(["∀" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:forall, line, col} | acc])
  defp lex(["Π" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:forall, line, col} | acc])
  defp lex(["\\" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:backslash, line, col} | acc])
  defp lex(["→" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:arrow, line, col} | acc])
  defp lex(["-" , ">" | rest], line, col, acc), do: lex(rest, line, col + 2, [{:arrow, line, col} | acc])

  # Universe (Type / *)
  defp lex(["*" | rest], line, col, acc) do
    {num_chars, rest2} = take_while_digit(rest)
    num = if num_chars == [], do: 0, else: String.to_integer(Enum.join(num_chars))
    lex(rest2, line, col + 1 + length(num_chars), [{:universe, line, col, num} | acc])
  end

  # Morte/Path Identifier (#path/to/file)
  defp lex(["#" | rest], line, col, acc) do
    {ident_chars, rest2} = take_path_ident(rest)
    ident = "#" <> Enum.join(ident_chars)
    lex(rest2, line, col + 1 + length(ident_chars), [{:ident, line, col, ident} | acc])
  end

  # Standard Identifiers & Numbers
  defp lex([c | rest], line, col, acc) do
    cond do
      is_digit(c) ->
        {num_chars, rest2} = take_while_digit([c | rest])
        num = String.to_integer(Enum.join(num_chars))
        lex(rest2, line, col + length(num_chars), [{:number, line, col, num} | acc])

      is_start_ident_char(c) ->
        {ident_chars, rest2} = take_ident([c | rest])
        ident = Enum.join(ident_chars)
        lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])

      true ->
        {:error, "Unexpected character in Morte: #{c} at #{line}:#{col}"}
    end
  end

  defp take_ident([c | rest]) do
    if is_ident_char(c) do
      {rest_ident, rest2} = take_ident(rest)
      {[c | rest_ident], rest2}
    else
      {[], [c | rest]}
    end
  end
  defp take_ident([]), do: {[], []}

  # In Morte, paths can include [ ]
  defp take_path_ident([c | rest]) do
    if c not in [" ", "\n", "\r", "\t", "(", ")", "{", "}", ",", ";"] do
      {rest_ident, rest2} = take_path_ident(rest)
      {[c | rest_ident], rest2}
    else
      {[], [c | rest]}
    end
  end
  defp take_path_ident([]), do: {[], []}

  defp take_while_digit([c | rest]) do
    if is_digit(c) do
      {matched, remaining} = take_while_digit(rest)
      {[c | matched], remaining}
    else
      {[], [c | rest]}
    end
  end
  defp take_while_digit([]), do: {[], []}

  defp is_digit(c), do: c >= "0" and c <= "9"
  
  defp is_start_ident_char(c) do
    (c >= "a" and c <= "z") or (c >= "A" and c <= "Z") or 
    c in ["_", "/", "@", ".", "+", "-", "<", ">", "!", "&", "|", "?", "=", "[", "]"]
  end

  defp is_ident_char(c) do
    is_start_ident_char(c) or is_digit(c) or c == "'"
  end
end
