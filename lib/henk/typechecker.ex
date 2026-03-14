defmodule Henk.Typechecker do
  alias Henk.AST

  @moduledoc """
  Bidirectional type checker for pure CoC terms.

  Env carries all context as a pure functional argument:
    ctx          — typing context: [{name, type}]
    defs         — known definitions:  %{name => term}
    name_to_mod  — name → module mapping
    type_constrs — %{type_name => [constr_names], constr_name => type_name}
    in_progress  — MapSet of names being evaluated (circular ref detection)
    deadline     — monotonic ms deadline for normalisation
  """

  defmodule Env do
    defstruct ctx: [],
              defs: %{},
              name_to_mod: %{},
              type_constrs: %{},
              foreign_defs: %{},        # %{name => {erl_mod, erl_func}}
              in_progress: MapSet.new(),
              deadline: nil
  end

  # ── Module check ──────────────────────────────────────────────────────────

  def check_module(%AST.Module{declarations: decls}, %Env{} = env) do
    Enum.reduce_while(decls, {:ok, env}, fn
      %AST.DeclValue{name: name, expr: expr}, {:ok, acc} ->
        case infer(acc, expr) do
          {:error, _} = err ->
            {:halt, err}
          ty ->
            new_env = %{acc | ctx: [{name, ty} | acc.ctx], defs: Map.put(acc.defs, name, expr)}
            {:cont, {:ok, new_env}}
        end

      _, acc ->
        {:cont, acc}
    end)
  end

  # ── Type inference ────────────────────────────────────────────────────────

  def infer(%Env{} = env, term) do
    case term do
      %AST.Var{name: "Any"} ->
        %AST.Universe{level: 0}

      %AST.Var{name: name} ->
        # Check circular reference
        if MapSet.member?(env.in_progress, name) do
          {:error, {:circular_reference, name}}
        else
          case List.keyfind(env.ctx, name, 0) do
            {^name, ty} -> ty
            nil ->
              # Try global defs
              case Map.get(env.defs, name) do
                nil -> {:error, {:unbound_variable, name}}
                def_term ->
                  env2 = %{env | in_progress: MapSet.put(env.in_progress, name)}
                  infer(env2, def_term)
              end
          end
        end

      %AST.Universe{level: i} ->
        %AST.Universe{level: i + 1}

      %AST.Pi{name: x, domain: a, codomain: b} ->
        u_a = universe_level(env, a)
        u_b = universe_level(%{env | ctx: [{x, a} | env.ctx]}, b)
        %AST.Universe{level: max(u_a, u_b)}

      %AST.Lam{name: x, domain: domain, body: body} ->
        env2 = %{env | ctx: [{x, domain} | env.ctx]}
        %AST.Pi{name: x, domain: domain, codomain: infer(env2, body)}

      %AST.App{func: f, arg: arg} ->
        f_ty = infer(env, f)
        case normalize(env, f_ty) do
          %AST.Pi{name: x, domain: _a, codomain: b} ->
            subst(x, arg, b)

          %AST.Var{name: "Any"} ->
            %AST.Var{name: "Any"}

          other_ty ->
            {:error, {:application_requires_pi, f, other_ty}}
        end

      _ ->
        {:error, {:cannot_infer, term}}
    end
  end

  def check(%Env{} = _env, _t, %AST.Var{name: "Any"}), do: :ok

  def check(%Env{} = env, t, ty) do
    case infer(env, t) do
      {:error, _} = err -> err
      inferred ->
        if inferred == %AST.Var{name: "Any"} or equal?(env, inferred, ty) do
          :ok
        else
          {:error, {:type_mismatch, t, inferred, ty}}
        end
    end
  end

  def universe_level(_env, %AST.Var{name: "Any"}), do: 0

  def universe_level(env, t) do
    case normalize(env, t) do
      %AST.Universe{level: i} -> i
      _ -> 0
    end
  end

  def equal?(env, t1, t2) do
    normalize(env, t1) == normalize(env, t2)
  end

  # ── Normalisation ─────────────────────────────────────────────────────────

  def normalize(env, t) do
    deadline = env.deadline || System.monotonic_time(:millisecond) + 60_000
    env2 = %{env | deadline: deadline}
    t_red = reduce(env2, t)

    case t_red do
      %AST.App{func: f, arg: a} ->
        %AST.App{func: normalize(env2, f), arg: normalize(env2, a)}

      %AST.Lam{name: x, domain: d, body: b} ->
        %AST.Lam{name: x, domain: normalize(env2, d), body: b}

      %AST.Pi{name: x, domain: d, codomain: c} ->
        %AST.Pi{name: x, domain: normalize(env2, d), codomain: normalize(env2, c)}

      _ ->
        t_red
    end
  end

  def reduce(env, term, fuel \\ 50_000)

  def reduce(_env, t, 0), do: raise("Out of fuel: #{inspect(t, limit: 10)}")

  def reduce(env, t, fuel) do
    if env.deadline && System.monotonic_time(:millisecond) > env.deadline do
      raise "Timeout: #{inspect(t, limit: 10)}"
    end
    do_reduce(env, t, fuel)
  end

  defp do_reduce(env, %AST.App{func: f, arg: arg}, fuel) do
    f_red = reduce(env, f, fuel - 1)
    case f_red do
      %AST.Lam{name: x, body: body} ->
        reduce(env, subst(x, arg, body), fuel - 1)
      _ ->
        %AST.App{func: f_red, arg: arg}
    end
  end

  defp do_reduce(env, %AST.Var{name: name}, fuel) do
    if MapSet.member?(env.in_progress, name) do
      %AST.Var{name: name}
    else
      case Map.get(env.defs, name) do
        nil -> %AST.Var{name: name}
        term ->
          env2 = %{env | in_progress: MapSet.put(env.in_progress, name)}
          reduce(env2, term, fuel - 1)
      end
    end
  end

  defp do_reduce(_env, t, _fuel), do: t

  # ── Substitution ──────────────────────────────────────────────────────────

  def subst(x, s, %AST.Var{name: n}), do: if(n == x, do: s, else: %AST.Var{name: n})

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

  def subst(x, s, %AST.App{func: f, arg: a}),
    do: %AST.App{func: subst(x, s, f), arg: subst(x, s, a)}

  def subst(_, _, t), do: t
end
