defmodule Henk.Parser.AUT68 do
  @moduledoc """
  Parser for AUT-68 (Automath) in a minimalist Caramel style.
  Handles (x : A) for Lambda and [x : A] for Pi types.
  Strictly no arrows; application by juxtaposition.
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

  # Skip stray symbols that might appear due to porting artifacts
  defp skip_stray_delimiters([t | rest]) when elem(t, 0) == :right_paren, do: skip_stray_delimiters(rest)
  defp skip_stray_delimiters(tokens), do: tokens


  # Universe (*)
  defp parse_atom([t | rest], _env) when elem(t, 0) == :universe do
    level = case t do
      {:universe, _, _, l} -> l
      {:universe, l} -> l
    end
    {:ok, %AST.Universe{level: level}, rest}
  end

  # Identifiers
  defp parse_atom([t | rest], env) when elem(t, 0) == :ident do
    name = case t do
      {:ident, _, _, n} -> n
      {:ident, n} -> n
    end
    resolved = resolve_var(name, env)
    {:ok, %AST.Var{name: resolved}, rest}
  end

  # (x : A) Body -> Lambda  OR  (Term)
  defp parse_atom([t | rest], env) when elem(t, 0) == :left_paren do
    case split_at_matching(rest, :right_paren, 0) do
      {:ok, inside, after_paren} ->
        if has_top_level_colon?(inside) do
          case parse_binder_content(inside, env) do
            {:ok, names, type} ->
              # Update environment
              {uniques, new_env} = bind_names(names, env)
              
              # Optional arrow
              rest2 = case after_paren do
                [{:arrow, _, _} | tl] -> tl
                _ -> after_paren
              end

              case parse_term(rest2, new_env) do
                {:ok, body, rest3} ->
                  nested = Enum.zip(names, uniques)
                           |> Enum.reverse()
                           |> Enum.reduce(body, fn {_orig, unique}, acc ->
                             %AST.Lam{name: unique, domain: type, body: acc}
                           end)
                  {:ok, nested, rest3}
                err -> err
              end
            err -> err
          end
        else
          # ENCLOSED TERM: (Term)
          case parse_term(inside, env) do
            {:ok, term, _} -> {:ok, term, after_paren}
            err -> err
          end
        end
      _ -> {:error, :unmatched_paren}
    end
  end

  # [x : A] Body -> Pi Type
  defp parse_atom([t | rest], env) when elem(t, 0) == :left_square do
    case split_at_matching(rest, :right_square, 0) do
      {:ok, inside, after_square} ->
        case parse_binder_content(inside, env) do
          {:ok, names, type} ->
            {uniques, new_env} = bind_names(names, env)
            
            # Optional arrow
            rest2 = case after_square do
              [{:arrow, _, _} | tl] -> tl
              _ -> after_square
            end

            case parse_term(rest2, new_env) do
              {:ok, body, rest3} ->
                nested = Enum.zip(names, uniques)
                         |> Enum.reverse()
                         |> Enum.reduce(body, fn {_orig, unique}, acc ->
                           %AST.Pi{name: unique, domain: type, codomain: acc}
                         end)
                {:ok, nested, rest3}
              err -> err
            end
          err -> err
        end
      _ -> {:error, :unmatched_square}
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
          case parse_term(type_tokens, env) do
            {:ok, type, []} -> {:ok, names, type}
            {:ok, type, _}  -> {:ok, names, type}
            err -> err
          end
        end
      _ -> {:error, :invalid_binder}
    end
  end

  defp resolve_var(name, env) do
    {base, index} = split_name_index(name)
    
    case Map.get(env, base) do
      nil -> name # External
      stack -> Enum.at(stack, index) || name
    end
  end

  defp split_name_index(name) do
    case Regex.run(~r/^(.+?)([₀₁₂₃₄₅₆₇₈₉]*)$/u, name) do
      [_, base, ""] -> {base, 0}
      [_, base, subs] -> {base, from_subscripts(subs)}
    end
  end

  defp from_subscripts(subs) do
    subs 
    |> String.codepoints()
    |> Enum.map(fn 
      "₀" -> "0"
      "₁" -> "1"
      "₂" -> "2"
      "₃" -> "3"
      "₄" -> "4"
      "₅" -> "5"
      "₆" -> "6"
      "₇" -> "7"
      "₈" -> "8"
      "₉" -> "9"
    end)
    |> Enum.join()
    |> String.to_integer()
  end

  defp bind_names(names, env) do
    Enum.reduce(names, {[], env}, fn name, {acc_names, acc_env} ->
      stack = Map.get(acc_env, name, [])
      unique = "#{name}_#{length(stack)}"
      {[unique | acc_names], Map.put(acc_env, name, [unique | stack])}
    end) |> (fn {uniques, env} -> {Enum.reverse(uniques), env} end).()
  end

  defp has_top_level_colon?(tokens) do
    has_top_level_colon?(tokens, 0)
  end

  defp has_top_level_colon?([], _depth), do: false
  defp has_top_level_colon?([{:colon, _, _} | _], 0), do: true
  defp has_top_level_colon?([{:left_paren, _, _} | rest], d), do: has_top_level_colon?(rest, d + 1)
  defp has_top_level_colon?([{:right_paren, _, _} | rest], d), do: has_top_level_colon?(rest, d - 1)
  defp has_top_level_colon?([{:left_square, _, _} | rest], d), do: has_top_level_colon?(rest, d + 1)
  defp has_top_level_colon?([{:right_square, _, _} | rest], d), do: has_top_level_colon?(rest, d - 1)
  defp has_top_level_colon?([_ | rest], d), do: has_top_level_colon?(rest, d)

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

  defp split_at_matching([t | rest], target, depth, acc) when elem(t, 0) == :left_square do
    new_depth = if target == :right_square, do: depth + 1, else: depth
    split_at_matching(rest, target, new_depth, [t | acc])
  end
  defp split_at_matching([t | rest], target, depth, acc) when elem(t, 0) == :right_square do
    new_depth = if target == :right_square, do: depth - 1, else: depth
    split_at_matching(rest, target, new_depth, [t | acc])
  end

  defp split_at_matching([t | rest], target, depth, acc) do
    split_at_matching(rest, target, depth, [t | acc])
  end
end
