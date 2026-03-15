defmodule Henk.Desugar do
  @moduledoc """
  Desugarer: Miranda surface AST → pure CoC terms (Var/Universe/Pi/Lam/App).

  Two-pass approach:
    Pass 1: DeclData → Inductive (collect constructor ordering for case desugaring)
    Pass 2: Inductive → Church-encoded DeclValues (Pi-type + Lam constructors)
            Case      → Church-fold application: e Any (\\x->b1) (\\y->b2)
            Let       → nested App(Lam): (\\x->body) e
            Lambda    → nested Lam
            DeclValue binders → outer Lam wrappers

  Church (Böhm-Berarducci) encoding for `data T params = C1 a1..ak | C2 b1..bm`:

    T     = λ(p1:*).… ∀(R:*) → (a1'→..→ak'→R) → (b1'→..→bm'→R) → R
            where ai' = ai with T replaced by R (recursive → fold-result)

    Ci    = λ(x1:a1)..λ(xk:ak).λ(R:*).λ(c1:T1).…λ(cn:Tn). ci x1..xk

    case e of C1 x->b | C2 y z->b2
           => e Any (\\x->b) (\\y->\\z->b2)     -- branches in constructor order
  """

  alias Henk.AST

  # ─── Main entry point ─────────────────────────────────────────────────────

  def desugar(%AST.Module{declarations: decls} = m, env \\ %Henk.Typechecker.Env{}) do
    # Pass 1: DeclData → Inductive; collect type_constrs map
    {pass1_decls, type_constrs} = collect_inductives(decls)

    env1 = %{env | type_constrs: Map.merge(env.type_constrs, type_constrs)}

    # Pass 2: Inductive → Church DeclValues; desugar everything else
    result_decls =
      Enum.flat_map(pass1_decls, fn
        %AST.Inductive{} = ind -> church_encode(ind)
        decl -> [desugar_decl(decl, env1)]
      end)

    %AST.Module{m | declarations: result_decls}
  end

  # ─── Pass 1 ───────────────────────────────────────────────────────────────

  defp collect_inductives(decls) do
    Enum.reduce(decls, {[], %{}}, fn decl, {acc_decls, acc_map} ->
      case decl do
        %AST.DeclData{name: name, params: params, constructors: constrs} ->
          ind = %AST.Inductive{
            name: name,
            params: Enum.map(params, fn p -> {p, %AST.Universe{level: 0}} end),
            constrs: Enum.map(constrs, fn {cn, args} -> {cn, args} end)
          }
          constr_names = Enum.map(constrs, fn {cn, _} -> cn end)
          # Type→[ConstructorNames], ConstructorName→TypeName
          new_map =
            Map.put(acc_map, name, constr_names)
            |> then(fn m ->
              Enum.reduce(constr_names, m, fn cn, a -> Map.put(a, cn, name) end)
            end)
          {acc_decls ++ [ind], new_map}

        _ ->
          {acc_decls ++ [decl], acc_map}
      end
    end)
  end

  # ─── Pass 2a: Church-encode Inductive ────────────────────────────────────

  defp church_encode(%AST.Inductive{name: t_name, params: params, constrs: constrs}) do
    param_names = Enum.map(params, fn {p, _} -> p end)
    r = %AST.Var{name: "R"}

    # Fold type for T: ∀(R:*) → branch1_type → branch2_type → R
    branch_pis =
      Enum.reduce(Enum.reverse(constrs), r, fn {cn, args}, acc ->
        branch_ty = args_to_pi(args, r, t_name)
        %AST.Pi{name: downcase(cn), domain: branch_ty, codomain: acc}
      end)

    fold_ty = %AST.Pi{name: "R", domain: %AST.Universe{level: 0}, codomain: branch_pis}

    type_term = wrap_params_lam(param_names, fold_ty)

    type_decl = make_val(t_name, type_term)

    # One DeclValue per constructor
    constr_decls =
      Enum.map(constrs, fn {cn, args} ->
        make_val(cn, church_ctor(cn, args, constrs, t_name, param_names, r))
      end)

    [type_decl | constr_decls]
  end

  # Ci = λ(xi:ai). λ(R:*). λ(cn_j : branch_type_j). c_i x1..xk
  defp church_ctor(cn, args, all_constrs, t_name, param_names, r) do
    arg_vars = Enum.with_index(args, 1) |> Enum.map(fn {_, i} -> "x#{i}" end)

    # Body: (downcase(cn)) x1 x2 ... xk
    body =
      Enum.reduce(arg_vars, %AST.Var{name: downcase(cn)}, fn v, acc ->
        %AST.App{func: acc, arg: %AST.Var{name: v}}
      end)

    # Wrap in case lambdas: λ(c1:T1). λ(c2:T2). … body
    body_cases =
      Enum.reduce(Enum.reverse(all_constrs), body, fn {other_cn, other_args}, acc ->
        ty = args_to_pi(other_args, r, t_name)
        %AST.Lam{name: downcase(other_cn), domain: ty, body: acc}
      end)

    body_r = %AST.Lam{name: "R", domain: %AST.Universe{level: 0}, body: body_cases}

    # Wrap in λ(xi:ai)
    body_args =
      Enum.reduce(
        Enum.reverse(Enum.zip(arg_vars, args)),
        body_r,
        fn {v, ty}, acc -> %AST.Lam{name: v, domain: ty, body: acc} end
      )

    wrap_params_lam(param_names, body_args)
  end

  # (a1[T→R] → a2[T→R] → … → R)
  defp args_to_pi(args, r, t_name) do
    Enum.reduce(Enum.reverse(args), r, fn arg_ty, inner ->
      %AST.Pi{name: "_", domain: subst_type(arg_ty, t_name, r), codomain: inner}
    end)
  end

  # Replace T (recursive type name) with R in a type term
  defp subst_type(%AST.Var{name: n}, t_name, r) when n == t_name, do: r
  defp subst_type(%AST.App{func: f, arg: a}, t, r),
    do: %AST.App{func: subst_type(f, t, r), arg: subst_type(a, t, r)}
  defp subst_type(%AST.Pi{name: n, domain: d, codomain: c}, t, r),
    do: %AST.Pi{name: n, domain: subst_type(d, t, r), codomain: subst_type(c, t, r)}
  defp subst_type(other, _t, _r), do: other

  defp wrap_params_lam([], body), do: body
  defp wrap_params_lam([p | rest], body),
    do: %AST.Lam{name: p, domain: %AST.Universe{level: 0}, body: wrap_params_lam(rest, body)}

  defp downcase(s), do: String.downcase(s)
  defp make_val(n, e), do: %AST.DeclValue{name: n, binders: [], expr: e, guards: nil, where_decls: []}

  # ─── Pass 2b: desugar_decl ───────────────────────────────────────────────

  def desugar_decl(decl, env \\ %Henk.Typechecker.Env{})

  def desugar_decl(
        %AST.DeclValue{name: name, binders: binders, expr: expr, where_decls: where_decls},
        env
      ) do
    # Desugar where-clauses into a Let → App(Lam)
    desugared_where =
      Enum.map(where_decls || [], &desugar_decl(&1, env))

    inner_expr =
      if desugared_where == [] do
        expr
      else
        %AST.Let{
          decls: Enum.map(desugared_where, fn d -> {d.name, d.expr} end),
          body: expr
        }
      end

    # Binders f x y = body  →  f = λx.λy.body
    body =
      Enum.reduce(Enum.reverse(binders), desugar_expr(inner_expr, env), fn
        %AST.Var{name: vn}, acc ->
          %AST.Lam{name: vn, domain: %AST.Var{name: "Any"}, body: acc}
      end)

    make_val(name, body)
  end

  def desugar_decl(other, _env), do: other

  # ─── Expression desugarer ─────────────────────────────────────────────────

  def desugar_expr(expr, env \\ %Henk.Typechecker.Env{})

  # \x y -> body  →  λx.λy.body
  def desugar_expr(%AST.Lambda{binders: binders, body: body}, env) do
    Enum.reduce(
      Enum.reverse(binders),
      desugar_expr(body, env),
      fn %AST.Var{name: vn}, acc ->
        %AST.Lam{name: vn, domain: %AST.Var{name: "Any"}, body: acc}
      end
    )
  end

  # let x = e in body  →  (λx.body) e         (repeated for each binding)
  def desugar_expr(%AST.Let{decls: decls, body: body}, env) do
    desugared_body = desugar_expr(body, env)

    Enum.reduce(Enum.reverse(decls), desugared_body, fn {name, expr}, acc ->
      %AST.App{
        func: %AST.Lam{name: name, domain: %AST.Var{name: "Any"}, body: acc},
        arg: desugar_expr(expr, env)
      }
    end)
  end

  # case e of C1 x->b | C2 y z->b2  →  e Any (λx->b) (λy->λz->b2)
  def desugar_expr(%AST.Case{expr: e, branches: branches}, env) do
    desugared_e = desugar_expr(e, env)
    ordered = order_branches(branches, env)

    branch_lams =
      Enum.map(ordered, fn {pat, body} ->
        vars = pattern_vars(pat)
        desugared_body = desugar_expr(body, env)
        Enum.reduce(Enum.reverse(vars), desugared_body, fn v, acc ->
          %AST.Lam{name: v, domain: %AST.Var{name: "Any"}, body: acc}
        end)
      end)

    # e Any branch1 branch2 …
    base = %AST.App{func: desugared_e, arg: %AST.Var{name: "Any"}}
    Enum.reduce(branch_lams, base, fn lam, acc -> %AST.App{func: acc, arg: lam} end)
  end

  def desugar_expr(%AST.App{func: f, arg: a}, env),
    do: %AST.App{func: desugar_expr(f, env), arg: desugar_expr(a, env)}

  def desugar_expr(%AST.Pi{name: n, domain: d, codomain: c}, env),
    do: %AST.Pi{name: n, domain: desugar_expr(d, env), codomain: desugar_expr(c, env)}

  def desugar_expr(%AST.Lam{name: n, domain: d, body: b}, env),
    do: %AST.Lam{name: n, domain: desugar_expr(d, env), body: desugar_expr(b, env)}

  def desugar_expr(%AST.NatLiteral{value: v}, env) do
    if v <= 0 do
      %AST.Var{name: "Zero"}
    else
      %AST.App{
        func: %AST.Var{name: "Succ"},
        arg: desugar_expr(%AST.NatLiteral{value: v - 1}, env)
      }
    end
  end

  def desugar_expr(%AST.ListLiteral{values: vs}, env) do
    case vs do
      [] ->
        %AST.App{func: %AST.Var{name: "Nil"}, arg: %AST.Var{name: "Any"}}

      [h | t] ->
        %AST.App{
          func: %AST.App{
            func: %AST.App{func: %AST.Var{name: "Cons"}, arg: %AST.Var{name: "Any"}},
            arg: desugar_expr(h, env)
          },
          arg: desugar_expr(%AST.ListLiteral{values: t}, env)
        }
    end
  end

  def desugar_expr(other, _env), do: other

  # ─── Helpers ──────────────────────────────────────────────────────────────

  # Order branches to match constructor declaration order
  defp order_branches(branches, env) do
    type_name =
      Enum.find_value(branches, fn {pat, _} ->
        case pat do
          %AST.BinderConstructor{name: cn} -> Map.get(env.type_constrs, cn)
          _ -> nil
        end
      end)

    constr_order =
      if type_name do
        Map.get(env.type_constrs, type_name, [])
      else
        Enum.map(branches, fn {pat, _} -> constructor_name(pat) end)
      end

    Enum.map(constr_order, fn cn ->
      Enum.find(branches, fn {pat, _} -> constructor_name(pat) == cn end)
      || {%AST.BinderConstructor{name: cn, args: []}, %AST.Var{name: "missing_#{cn}"}}
    end)
  end

  defp constructor_name(%AST.BinderConstructor{name: n}), do: n
  defp constructor_name(%AST.Var{name: n}), do: n
  defp constructor_name(_), do: "_"

  defp pattern_vars(%AST.BinderConstructor{args: args}),
    do: Enum.map(args, fn %AST.Var{name: n} -> n end)
  defp pattern_vars(%AST.Var{name: n}), do: [n]
  defp pattern_vars(_), do: []
end
