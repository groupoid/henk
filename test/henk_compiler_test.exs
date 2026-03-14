defmodule HenkCompilerTest do
  use ExUnit.Case, async: true

  @prelude """
  module Prelude where

  data Empty =

  data Unit = tt

  data Bool = False | True

  data Nat = Zero | Succ Nat

  id x = x

  const x y = x
  """

  @bool_src """
  module Data.Bool where

  import Prelude

  not b = case b of
      True  -> False
      False -> True
  """

  @nat_src """
  module Data.Nat where

  import Prelude

  plus m n = case m of
      Zero   -> n
      Succ p -> Succ p

  is_zero n = case n of
      Zero   -> True
      Succ p -> False
  """

  test "compiles Prelude" do
    assert {:ok, :"Prelude", _} = Henk.Compiler.compile_module(@prelude)
  end

  test "compiles Data.Bool" do
    assert {:ok, :"Data.Bool", _} = Henk.Compiler.compile_module(@bool_src)
  end

  test "compiles Data.Nat" do
    assert {:ok, :"Data.Nat", _} = Henk.Compiler.compile_module(@nat_src)
  end

  test "id compiles and runs correctly" do
    src = """
    module Test.Id where
    id x = x
    """
    {:ok, mod, bin} = Henk.Compiler.compile_module(src, typecheck: false)
    Henk.Compiler.load_module(mod, bin)
    # id is a function that returns its argument
    f = apply(mod, :id, [])
    assert is_function(f, 1)
    result = f.(:hello)
    assert result == :hello
  end

  test "const compiles and discards second arg" do
    src = """
    module Test.Const where
    const x y = x
    """
    {:ok, mod, bin} = Henk.Compiler.compile_module(src, typecheck: false)
    Henk.Compiler.load_module(mod, bin)
    f = apply(mod, :const, [])
    assert f.(:keep).(:discard) == :keep
  end

  test "Church Bool self-contained compiles and True/False are functions" do
    src = """
    module Test.BoolSelf where

    data Bool = False | True

    bool_id b = b
    """

    {:ok, mod, bin} = Henk.Compiler.compile_module(src, typecheck: false)
    Henk.Compiler.load_module(mod, bin)

    true_val  = apply(mod, :"True", [])
    false_val = apply(mod, :"False", [])

    # Church True = λR λt λf → t   — should be 1-arity fun returning 1-arity fun
    assert is_function(true_val, 1)
    assert is_function(false_val, 1)

    # data Bool = False | True
    # Church type: ∀R. R → R → R  (False=1st, True=2nd in constructor order)
    # False Any a b = a (1st constructor selects 1st branch)
    first = false_val.(:any).(:yes).(:no)
    assert first == :yes

    # True Any a b = b (2nd constructor selects 2nd branch)
    second = true_val.(:any).(:yes).(:no)
    assert second == :no
  end

  test "priv/henk/Prelude.henk compiles from disk" do
    if File.exists?("priv/henk/Prelude.henk") do
      src = File.read!("priv/henk/Prelude.henk")
      assert {:ok, :Prelude, _} = Henk.Compiler.compile_module(src, typecheck: false)
    else
      :ok
    end
  end
end
