defmodule Henk.Parser.Morte do
  @moduledoc """
  Parser for Morte syntax with de Bruijn index resolution.
  Handles λ (lambda), ∀ (forall), and #path identifiers.
  Translates Morte-style indices (var@n) to unique Henk-safe names by tracking binder depth.
  """
  alias Henk.AST

  def parse(tokens) do
    case parse_term(tokens, %{}) do
      {:ok, expr, []} -> {:ok, expr, []}
      {:ok, expr, rest} -> {:ok, expr, rest}
      err -> err
    end
  end

  defp parse_term(tokens, env) do
    tokens = skip_stray_delimiters(tokens)
    case parse_atom(tokens, env) do
      {:ok, left, rest} -> parse_app_tail(left, rest, env)
      err -> err
    end
  end

  defp skip_stray_delimiters([t | rest]) when elem(t, 0) == :right_paren, do: skip_stray_delimiters(rest)
  defp skip_stray_delimiters(tokens), do: tokens

  defp parse_atom([], _env) do
    {:error, :no_atom, []}
  end

  # Binders: λ (x : A) -> Body  OR  ∀ (x : A) -> Body
  defp parse_atom([t | rest], env) when elem(t, 0) in [:backslash, :forall] do
    binder_type = elem(t, 0)
    case rest do
      [{:left_paren, _, _} | rest2] ->
        case split_at_matching(rest2, :right_paren, 0) do
          {:ok, inside, after_paren} ->
            case parse_binder_content(inside, env) do
              {:ok, names, type} ->
                # Generate unique names and update environment
                {uniques, new_env} = bind_names(names, env)
                
                # Optional arrow
                rest3 = case after_paren do
                  [{:arrow, _, _} | tl] -> tl
                  _ -> after_paren
                end
                
                case parse_term(rest3, new_env) do
                  {:ok, body, rest4} ->
                    # Nest binders
                    # Names are in the order they were defined
                    nested = Enum.zip(names, uniques) 
                             |> Enum.reverse()
                             |> Enum.reduce(body, fn {_orig, unique}, acc ->
                               case binder_type do
                                 :backslash -> %AST.Lam{name: unique, domain: type, body: acc}
                                 :forall    -> %AST.Pi{name: unique, domain: type, codomain: acc}
                               end
                             end)
                    {:ok, nested, rest4}
                  err -> err
                end
              err -> err
            end
          _ -> {:error, :unmatched_paren}
        end
      _ -> {:error, :expected_left_paren_after_binder}
    end
  end

  # Universe (*)
  defp parse_atom([t | rest], _env) when elem(t, 0) == :universe do
    level = case t do
      {:universe, _, _, l} -> l
      {:universe, l} -> l
    end
    {:ok, %AST.Universe{level: level}, rest}
  end

  # Identifiers (including #paths and de Bruijn)
  defp parse_atom([t | rest], env) when elem(t, 0) == :ident do
    name = case t do
      {:ident, _, _, n} -> n
      {:ident, n} -> n
    end
    
    if String.starts_with?(name, "#") do
      {:ok, %AST.Var{name: translate_path(name)}, rest}
    else
      resolved = resolve_var(name, env)
      {:ok, %AST.Var{name: resolved}, rest}
    end
  end

  # Enclosed Term: (Term)
  defp parse_atom([t | rest], env) when elem(t, 0) == :left_paren do
    case split_at_matching(rest, :right_paren, 0) do
      {:ok, inside, after_paren} ->
        case parse_term(inside, env) do
          {:ok, term, _} -> {:ok, term, after_paren}
          err -> err
        end
      _ -> {:error, :unmatched_paren}
    end
  end

  defp parse_atom(tokens, _env), do: {:error, :no_atom, Enum.take(tokens, 5)}

  defp parse_app_tail(left, tokens, env) do
    case tokens do
      [{:arrow, _, _} | rest] ->
        case parse_term(rest, env) do
          {:ok, right, rest2} -> {:ok, %AST.Pi{name: "_", domain: left, codomain: right}, rest2}
          err -> err
        end
      _ ->
        case parse_atom(tokens, env) do
          {:ok, right, rest} -> parse_app_tail(%AST.App{func: left, arg: right}, rest, env)
          _ -> {:ok, left, tokens}
        end
    end
  end

  defp translate_path(name) do
    path = String.slice(name, 1..-1//1)
    translated = String.replace(path, "/", ".")
    
    normalized = translated 
      |> String.replace_trailing(".@", "") 
      |> String.replace_trailing("@", "")
      |> String.replace_trailing(".", "")
    
    (if normalized == "", do: "Main", else: normalized) <> ".main"
  end

  defp resolve_var(name, env) do
    {base, index} = case String.split(name, "@", parts: 2) do
      [b, i] -> {b, String.to_integer(i)}
      [b] -> {b, 0}
    end
    
    case Map.get(env, base) do
      nil -> translate_var(name) # External
      stack -> Enum.at(stack, index) || translate_var(name)
    end
  end

  defp translate_var(name) do
    name |> String.replace("@0", "") |> String.replace("@", "_at_")
  end

  defp bind_names(names, env) do
    Enum.reduce(names, {[], env}, fn name, {acc_names, acc_env} ->
      stack = Map.get(acc_env, name, [])
      # Unique name: name_count where count is absolute number of binders for this name
      # Actually, name_depth is simpler: name_#{length(stack)}
      unique = "#{name}_#{length(stack)}"
      {[unique | acc_names], Map.put(acc_env, name, [unique | stack])}
    end) |> (fn {uniques, env} -> {Enum.reverse(uniques), env} end).()
  end

  defp parse_binder_content(tokens, env) do
    case Enum.split_while(tokens, fn t -> elem(t, 0) != :colon end) do
      {name_tokens, [{:colon, _, _} | type_tokens]} when name_tokens != [] ->
        names = Enum.map(name_tokens, fn tok ->
          case tok do
            {:ident, _, _, n} -> n
            {:ident, n} -> n
            _ -> nil
          end
        end)
        
        if Enum.any?(names, &is_nil/1) do
          {:error, :invalid_binder_names}
        else
          # Type is parsed in OLD env (can't refer to the variables being bound yet)
          case parse_term(type_tokens, env) do
            {:ok, type, []} -> {:ok, names, type}
            {:ok, type, _}  -> {:ok, names, type}
            err -> err
          end
        end
      _ -> {:error, :invalid_binder}
    end
  end

  defp split_at_matching(tokens, target, depth) do
    split_at_matching(tokens, target, depth, [])
  end

  defp split_at_matching([], _, _, _), do: {:error, :unmatched}
  defp split_at_matching([t | rest], target, 0, acc) when elem(t, 0) == target do
    {:ok, Enum.reverse(acc), rest}
  end
  defp split_at_matching([t | rest], target, depth, acc) when elem(t, 0) == target do
    split_at_matching(rest, target, depth - 1, [t | acc])
  end

  defp split_at_matching([t | rest], target, depth, acc) when elem(t, 0) == :left_paren do
    new_depth = if target == :right_paren, do: depth + 1, else: depth
    split_at_matching(rest, target, new_depth, [t | acc])
  end
  defp split_at_matching([t | rest], target, depth, acc) when elem(t, 0) == :right_paren do
    new_depth = if target == :right_paren, do: depth - 1, else: depth
    split_at_matching(rest, target, new_depth, [t | acc])
  end

  defp split_at_matching([t | rest], target, depth, acc) do
    split_at_matching(rest, target, depth, [t | acc])
  end
end
