defmodule Henk.Typechecker do
  alias Henk.AST

  @doc """
  Typing environment contains:
  - env: map of (name -> inductive)
  - ctx: list of (name, type)
  - defs: map of (name -> term)
  - deadline: monotonic time limit in ms
  """
  defmodule Env do
    defstruct env: %{}, ctx: [], defs: %{}, name_to_mod: %{}, deadline: nil
  end

  # Checks all declarations in a module.
  # Expects a desugared module.
  def check_module(%AST.Module{declarations: decls}, %Env{} = env) do
    # First, collect all types/signatures into the context if they aren't there yet.
    # Desugared declarations are either Inductive or DeclValue.
    # For now, we assume all necessary things are in the env or we add them.
    Enum.reduce_while(decls, :ok, fn
      %AST.Inductive{} = ind, _acc ->
        infer(env, ind)
        {:cont, :ok}

      %AST.DeclValue{name: _name, expr: expr}, _acc ->
        case infer(env, expr) do
          {:error, _} = err -> {:halt, err}
          _ty -> {:cont, :ok}
        end

      _, acc ->
        {:cont, acc}
    end)
  end

  def infer(%Env{} = e, %AST.Var{name: name}) do
    if name == "Any" do
      %AST.Var{name: "Any"}
    else
      case List.keyfind(e.ctx, name, 0) do
        {^name, ty} -> ty
        nil -> {:error, {:unbound_variable, name}}
      end
    end
  end

  def infer(%Env{}, %AST.Universe{level: i}) do
    %AST.Universe{level: i + 1}
  end

  def infer(%Env{} = _e, %AST.Inductive{level: level}) do
    %AST.Universe{level: level + 1}
  end

  def infer(%Env{} = e, %AST.Constr{index: j, inductive: d, args: args}) do
    {^j, _name, ty} = Enum.find(d.constrs, fn {idx, _, _} -> idx == j end)
    ty_subst = subst_many(d.params, ty)
    infer_ctor(e, ty_subst, args)
  end

  def infer(%Env{} = e, %AST.Ind{inductive: _d, motive: p, cases: _cases, term: t}) do
    # IO.inspect(p, label: "IND MOTIVE")
    _t_ty = infer(e, t)

    case infer(e, p) do
      %AST.Pi{name: x, domain: _a, codomain: b} ->
        subst(x, t, b)

      other ->
        {:error, {:motive_not_pi, other}}
    end
  end

  def infer(%Env{} = e, %AST.Pi{name: x, domain: a, codomain: b}) do
    # IO.inspect({a, b}, label: "PI INFER")
    u_a = universe_level(e, a)
    u_b = universe_level(%{e | ctx: [{x, a} | e.ctx]}, b)
    %AST.Universe{level: Kernel.max(u_a, u_b)}
  end

  def infer(%Env{} = e, %AST.Lam{name: x, domain: domain, body: body}) do
    %AST.Pi{name: x, domain: domain, codomain: infer(%{e | ctx: [{x, domain} | e.ctx]}, body)}
  end

  def infer(%Env{} = e, %AST.App{func: f, arg: arg}) do
    case infer(e, f) do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        check(e, arg, a)
        subst(x, arg, b)

      %AST.Var{name: "Any"} ->
        %AST.Var{name: "Any"}

      _other ->
        # IO.inspect({f, other}, label: "APP INFER FAIL: NOT A PI")
        {:error, :application_requires_pi}
    end
  end

  def infer(%Env{} = e, %AST.Let{decls: decls, body: body}) do
    new_env =
      Enum.reduce(decls, e, fn {name, expr}, acc ->
        ty = infer(acc, expr)
        %{acc | ctx: [{name, ty} | acc.ctx], defs: Map.put(acc.defs, name, expr)}
      end)

    infer(new_env, body)
  end

  def check(%Env{} = _e, _t, %AST.Var{name: "Any"}), do: :ok

  def check(%Env{} = e, t, ty) do
    inferred = infer(e, t)

    # Allow Any as inferred type to match everything
    if inferred == %AST.Var{name: "Any"} or equal?(e, inferred, ty) do
      :ok
    else
      # IO.inspect({t, inferred, ty}, label: "TYPE MISMATCH")
      {:error, {:type_mismatch, inferred, ty}}
    end
  end

  def universe_level(_e, %AST.Var{name: "Any"}), do: 0

  def universe_level(e, t) do
    case normalize(e, t) do
      %AST.Universe{level: i} ->
        i

      _ ->
        0
    end
  end

  def equal?(e, t1, t2) do
    normalize(e, t1) == normalize(e, t2)
  end

  def normalize(e, t) do
    deadline = e.deadline || System.monotonic_time(:millisecond) + 60_000
    e = %{e | deadline: deadline}
    t_red = reduce(e, t)

    case t_red do
      %AST.App{func: f, arg: arg} ->
        %AST.App{func: normalize(e, f), arg: normalize(e, arg)}

      %AST.Lam{name: x, domain: a, body: b} ->
        # Use WHNF: don't normalize the body to avoid infinite recursion
        %AST.Lam{name: x, domain: normalize(e, a), body: b}

      %AST.Pi{name: x, domain: a, codomain: b} ->
        %AST.Pi{name: x, domain: normalize(e, a), codomain: normalize(e, b)}

      %AST.Ind{inductive: d, motive: p, cases: cases, term: t_val} ->
        %AST.Ind{
          inductive: d,
          motive: normalize(e, p),
          cases: Enum.map(cases, &normalize(e, &1)),
          term: normalize(e, t_val)
        }

      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: Enum.map(args, &normalize(e, &1))}

      _ ->
        t_red
    end
  end

  def reduce(e, t, fuel \\ 50_000)

  def reduce(_e, t, 0) do
    raise "Out of fuel reducing: #{inspect(t, limit: 20)}"
  end

  def reduce(e, t, fuel) do
    if e.deadline && System.monotonic_time(:millisecond) > e.deadline do
      raise "Timeout reducing: #{inspect(t, limit: 20)}"
    end

    do_reduce(e, t, fuel)
  end

  defp do_reduce(e, %AST.App{func: f, arg: arg}, fuel) do
    f_red = reduce(e, f, fuel - 1)

    case f_red do
      %AST.Lam{name: x, body: body} ->
        reduce(e, subst(x, arg, body), fuel - 1)

      %AST.Constr{index: i, inductive: d, args: args} ->
        arg_red = reduce(e, arg, fuel - 1)
        %AST.Constr{index: i, inductive: d, args: args ++ [arg_red]}

      _ ->
        %AST.App{func: f_red, arg: arg}
    end
  end

  defp do_reduce(e, %AST.Ind{inductive: ind_def, motive: _p, cases: cases, term: t} = ind, fuel) do
    case reduce(e, t, fuel - 1) do
      %AST.Constr{index: j, args: args} ->
        # Find the constructor's Pi type signature to trace which arguments are recursive
        {^j, _cname, c_sig} = Enum.find(ind_def.constrs, fn {idx, _, _} -> idx == j end)

        case_val = Enum.at(cases, j - 1)
        res = apply_args(e, case_val, args, c_sig, ind)
        reduce(e, res, fuel - 1)

      _ ->
        ind
    end
  end

  defp do_reduce(e, %AST.Let{decls: decls, body: body}, fuel) do
    new_defs = Enum.reduce(decls, e.defs, fn {n, expr}, acc -> Map.put(acc, n, expr) end)
    reduce(%{e | defs: new_defs}, body, fuel - 1)
  end

  defp do_reduce(e, %AST.Var{name: name}, fuel) do
    case Map.get(e.defs, name) do
      nil -> %AST.Var{name: name}
      term -> reduce(e, term, fuel - 1)
    end
  end

  defp do_reduce(_e, t, _fuel), do: t

  defp apply_args(_e, f, [], _ty_sig, _ind), do: f

  defp apply_args(e, f, [arg | rest], ty_sig, %AST.Ind{} = ind) do
    # Extract domain of current argument from constructor signature
    {arg_domain, next_sig} =
      case ty_sig do
        %AST.Pi{domain: d, codomain: c} -> {d, c}
        _ -> {nil, ty_sig}
      end

    ind_name = ind.inductive.name

    is_inductive =
      case arg_domain do
        %AST.Var{name: ^ind_name} -> true
        %AST.App{func: %AST.Var{name: ^ind_name}} -> true
        %AST.Pi{codomain: %AST.Var{name: ^ind_name}} -> true
        %AST.Pi{codomain: %AST.App{func: %AST.Var{name: ^ind_name}}} -> true
        _ -> false
      end

    f_next = %AST.App{func: f, arg: arg}

    ih =
      if is_inductive do
        case arg_domain do
          %AST.Pi{name: x, domain: a} ->
            # Functional induction: \x -> Ind(ind.term = arg x)
            %AST.Lam{
              name: x,
              domain: a,
              body: %AST.Ind{ind | term: %AST.App{func: arg, arg: %AST.Var{name: x}}}
            }

          _ ->
            # Basic induction
            %AST.Ind{ind | term: arg}
        end
      else
        # Not an inductive argument, but Desugarer might still expect a placeholder binder?
        # Actually, Henk Desugarer only generates IH binders for identified recursive calls.
        # Wait, the Desugarer: Enum.reduce(binders, body, ...) wraps EVERYTHING in Lam(k, Lam(ih, ...))
        # if the constructor was defined with args.
        # So we MUST pass an IH placeholder if it's not inductive.
        %AST.Var{name: "unused_ih"}
      end

    apply_args(e, %AST.App{func: f_next, arg: ih}, rest, next_sig, ind)
  end

  def subst_many(params, ty) do
    Enum.reduce(params, ty, fn {name, val}, acc -> subst(name, val, acc) end)
  end

  defp infer_ctor(e, ty, args) do
    Enum.reduce(args, ty, fn arg, acc ->
      case acc do
        %AST.Pi{name: x, domain: a, codomain: b} ->
          check(e, arg, a)
          subst(x, arg, b)

        _ ->
          raise "Too many arguments to constructor"
      end
    end)
  end

  def subst(x, s, %AST.Var{name: name}), do: if(name == x, do: s, else: %AST.Var{name: name})

  def subst(x, s, %AST.Pi{name: n, domain: a, codomain: b}) do
    if n == x,
      do: %AST.Pi{name: n, domain: subst(x, s, a), codomain: b},
      else: %AST.Pi{name: n, domain: subst(x, s, a), codomain: subst(x, s, b)}
  end

  def subst(x, s, %AST.Lam{name: n, domain: a, body: b}) do
    if n == x,
      do: %AST.Lam{name: n, domain: subst(x, s, a), body: b},
      else: %AST.Lam{name: n, domain: subst(x, s, a), body: subst(x, s, b)}
  end

  def subst(x, s, %AST.App{func: f, arg: arg}),
    do: %AST.App{func: subst(x, s, f), arg: subst(x, s, arg)}

  def subst(x, s, %AST.Let{decls: decls, body: body}) do
    new_decls = Enum.map(decls, fn {name, expr} -> {name, subst(x, s, expr)} end)
    %AST.Let{decls: new_decls, body: subst(x, s, body)}
  end

  def subst(x, s, %AST.Ind{inductive: d, motive: p, cases: cases, term: t}) do
    %AST.Ind{
      inductive: d,
      motive: subst(x, s, p),
      cases: Enum.map(cases, &subst(x, s, &1)),
      term: subst(x, s, t)
    }
  end

  def subst(x, s, %AST.Constr{index: i, inductive: d, args: args}) do
    %AST.Constr{index: i, inductive: d, args: Enum.map(args, &subst(x, s, &1))}
  end

  def subst(_, _, t), do: t
end
