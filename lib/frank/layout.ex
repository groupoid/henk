defmodule Henk.Layout do
  def resolve(tokens) do
    res = process(tokens, [1], -1, false, [])

    case res do
      [{:module, line, col} | rest] ->
        [{:v_left_brace, line, col}, {:module, line, col} | rest] ++ [{:v_right_brace, 999, 1}]

      _ ->
        res
    end
  end

  defp process([], blocks, _prev_line, _wait, acc) do
    closes = for _ <- Enum.drop(blocks, 1), do: {:v_right_brace, 999, 1}
    Enum.reverse(acc) ++ closes
  end

  defp process([tok | rest], blocks, prev_line, wait, acc) do
    line = elem(tok, 1)
    col = elem(tok, 2)
    new_line = prev_line != -1 and line > prev_line

    {blocks, acc, _wait} =
      if wait and elem(tok, 0) not in [:right_paren, :right_square, :right_brace, :v_right_brace] do
        {[col | blocks], [{:v_left_brace, line, col} | acc], false}
      else
        {blocks, acc, false}
      end

    {blocks, acc} =
      if new_line do
        handle_newline(col, line, blocks, acc)
      else
        {blocks, acc}
      end

    wait_next = elem(tok, 0) in [:where, :of, :let]

    process(rest, blocks, line, wait_next, [tok | acc])
  end

  defp handle_newline(col, line, blocks, acc) do
    if blocks == [] do
      {[], acc}
    else
      b = hd(blocks)

      cond do
        col == b ->
          {blocks, [{:v_semicolon, line, col} | acc]}

        col < b ->
          {_, rest_blocks} = List.pop_at(blocks, 0)
          handle_newline(col, line, rest_blocks, [{:v_right_brace, line, col} | acc])

        true ->
          {blocks, acc}
      end
    end
  end
end
