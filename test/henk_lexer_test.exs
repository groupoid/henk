defmodule HenkLexerTest do
  use ExUnit.Case, async: true
  alias Henk.Lexer

  test "lex keywords" do
    {:ok, tokens} = Lexer.lex("module M where data Nat = Zero | Succ Nat")
    types = Enum.map(tokens, &elem(&1, 0))
    assert :module in types
    assert :where in types
    assert :data in types
    assert :pipe in types
  end

  test "lex lambda and arrow" do
    {:ok, tokens} = Lexer.lex("\\x -> x")
    types = Enum.map(tokens, &elem(&1, 0))
    assert :backslash in types
    assert :arrow in types
    assert Enum.any?(tokens, fn
      {:ident, _, _, "x"} -> true
      _ -> false
    end)
  end

  test "lex forall keyword" do
    {:ok, tokens} = Lexer.lex("forall")
    assert [{:forall, _, _}] = tokens
  end

  test "lex numbers" do
    {:ok, tokens} = Lexer.lex("0 1 42")
    nums = for {:number, _, _, n} <- tokens, do: n
    assert nums == [0, 1, 42]
  end

  test "lex comment stripping" do
    {:ok, tokens} = Lexer.lex("x -- this is a comment\ny")
    names = for {:ident, _, _, n} <- tokens, do: n
    assert names == ["x", "y"]
  end
end
