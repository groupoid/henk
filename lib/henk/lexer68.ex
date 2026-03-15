defmodule Henk.Lexer.AUT68 do
  @moduledoc """
  Lexer for AUT-68 (Automath) in a minimalist Caramel style.
  Supports (...) for Lambda, [...] for Pi, Type/Universe with subscripts.
  Strictly excludes arrows and UTF-8 binders (λ, ∀, Π).
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

  # Backslash
  defp lex(["\\" | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:backslash, line, col} | acc])

  # Special symbols
  defp lex(["(" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:left_paren, line, col} | acc])
  defp lex([")" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:right_paren, line, col} | acc])
  defp lex(["[" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:left_square, line, col} | acc])
  defp lex(["]" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:right_square, line, col} | acc])
  defp lex([":" | rest], line, col, acc), do: lex(rest, line, col + 1, [{:colon, line, col} | acc])

  # Universe (Type / *) with optional subscripts (*₁₀₁)
  defp lex(["*" | rest], line, col, acc) do
    {sub_chars, rest2} = take_subscripts(rest)
    num = if sub_chars == [], do: 0, else: subscripts_to_int(sub_chars)
    lex(rest2, line, col + 1 + length(sub_chars), [{:universe, line, col, num} | acc])
  end

  # Standard Identifiers & Numbers (including subscripts)
  defp lex([c | rest], line, col, acc) do
    cond do
      is_digit(c) ->
        {num_chars, rest2} = take_while_digit([c | rest])
        num = String.to_integer(Enum.join(num_chars))
        lex(rest2, line, col + length(num_chars), [{:number, line, col, num} | acc])

      is_alpha(c) ->
        {ident_chars, rest2} = take_ident([c | rest])
        ident = Enum.join(ident_chars)
        case ident do
          "type" -> 
            {sub_chars, rest3} = take_subscripts(rest2)
            num = if sub_chars == [], do: 0, else: subscripts_to_int(sub_chars)
            lex(rest3, line, col + 4 + length(sub_chars), [{:universe, line, col, num} | acc])
          _ -> 
            lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
        end

      true ->
        {:error, "Unexpected character in AUT-68: #{c} at #{line}:#{col}"}
    end
  end

  defp take_ident([c | rest]) do
    if is_ident_char(c) or is_subscript(c) do
      {rest_ident, rest2} = take_ident(rest)
      {[c | rest_ident], rest2}
    else
      {[], [c | rest]}
    end
  end
  defp take_ident([]), do: {[], []}

  defp take_subscripts([c | rest]) do
    if is_subscript(c) do
      {rest_sub, rest2} = take_subscripts(rest)
      {[c | rest_sub], rest2}
    else
      {[], [c | rest]}
    end
  end
  defp take_subscripts([]), do: {[], []}

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
  defp is_alpha(c), do: (c >= "a" and c <= "z") or (c >= "A" and c <= "Z") or c == "_"
  
  defp is_ident_char(c) do
    is_alpha(c) or is_digit(c) or c in ["'", "/", "@", ".", "+", "-", "<", ">", "!", "&", "|", "?", "="]
  end

  @subscripts %{
    "₀" => "0", "₁" => "1", "₂" => "2", "₃" => "3", "₄" => "4",
    "₅" => "5", "₆" => "6", "₇" => "7", "₈" => "8", "₉" => "9"
  }

  defp is_subscript(c), do: Map.has_key?(@subscripts, c)

  defp subscripts_to_int(chars) do
    chars 
    |> Enum.map(fn c -> Map.get(@subscripts, c) end) 
    |> Enum.join() 
    |> String.to_integer()
  end
end
