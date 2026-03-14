defmodule HenkTypecheckerTest do
  use ExUnit.Case, async: true
  alias Henk.{Typechecker, AST}
  alias Typechecker.Env

  # ── Universe hierarchy ──────────────────────────────────────────────────

  test "U0 inhabits U1" do
    env = %Env{}
    assert Typechecker.infer(env, %AST.Universe{level: 0}) == %AST.Universe{level: 1}
  end

  test "U1 inhabits U2" do
    env = %Env{}
    assert Typechecker.infer(env, %AST.Universe{level: 1}) == %AST.Universe{level: 2}
  end

  # ── Lambda and application ────────────────────────────────────────────────

  test "identity function type" do
    # (λ(x:U0) → x) : (U0 → U0) — as Pi
    env = %Env{}
    id = %AST.Lam{name: "x", domain: %AST.Universe{level: 0}, body: %AST.Var{name: "x"}}
    ty = Typechecker.infer(env, id)
    assert %AST.Pi{name: "x"} = ty
  end

  test "beta reduction in normalize" do
    # (λx → x) y  →  y
    env = %Env{ctx: [{"y", %AST.Universe{level: 0}}]}
    app = %AST.App{
      func: %AST.Lam{name: "x", domain: %AST.Universe{level: 0}, body: %AST.Var{name: "x"}},
      arg: %AST.Var{name: "y"}
    }
    norm = Typechecker.normalize(env, app)
    assert norm == %AST.Var{name: "y"}
  end

  # ── Circular reference detection ──────────────────────────────────────────

  test "circular reference via in_progress" do
    # Definition loop: x = x
    env = %Env{defs: %{"x" => %AST.Var{name: "x"}}}
    # Normalising should not infinite-loop; in_progress blocks the cycle
    result = Typechecker.normalize(env, %AST.Var{name: "x"})
    assert result == %AST.Var{name: "x"}
  end

  # ── Church Bool ───────────────────────────────────────────────────────────

  test "Church True applied to case gives first branch" do
    # True : ∀R. R → R → R
    # True Any a b = a
    env = %Env{}

    church_true =
      %AST.Lam{name: "R", domain: %AST.Universe{level: 0},
        body: %AST.Lam{name: "t", domain: %AST.Var{name: "Any"},
          body: %AST.Lam{name: "f", domain: %AST.Var{name: "Any"},
            body: %AST.Var{name: "t"}}}}

    result =
      %AST.App{
        func: %AST.App{
          func: %AST.App{func: church_true, arg: %AST.Universe{level: 0}},
          arg: %AST.Var{name: "a"}},
        arg: %AST.Var{name: "b"}}

    norm = Typechecker.normalize(%{env | ctx: [{"a", %AST.Universe{level: 0}}, {"b", %AST.Universe{level: 0}}]}, result)
    assert norm == %AST.Var{name: "a"}
  end
end
