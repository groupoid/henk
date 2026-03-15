
# scripts/port_morte.exs
import Path

morte_dir = "priv/morte"
aut_dir   = "priv/aut-68"

subscripts_map = %{"0"=>"₀","1"=>"₁","2"=>"₂","3"=>"₃","4"=>"₄","5"=>"₅","6"=>"₆","7"=>"₇","8"=>"₈","9"=>"₉"}
to_subs = fn str -> str |> String.codepoints() |> Enum.map(&(subscripts_map[&1] || &1)) |> Enum.join() end

if File.exists?(aut_dir), do: File.rm_rf!(aut_dir)
File.mkdir_p!(aut_dir)

defmodule PortHelper do
  def translate_all(s) do
    s |> strip_comments() |> standardize() |> transform() |> finalize()
  end

  def strip_comments(s), do: String.replace(s, ~r/--[^\n]*/, "", global: true) |> String.replace("\n", " ")

  def standardize(s) do
    s |> String.replace(~r/forall|∀|Π|\\\/|PI/, " PI ")
      |> String.replace(~r/lambda|λ|\\|LA/, " LA ")
      |> String.replace(~r/→/, " -> ")
  end

  def transform(s) do
    s = String.trim(s)
    cond do
      s == "" -> ""
      # 1. Binder with paren: PI (x:A) -> B
      match = Regex.run(~r/^(PI|LA)\s*\(/, s, return: :index) ->
        [{start, len} | _] = match
        after_sym = String.slice(s, start + len..-1//1)
        case find_matching(String.codepoints(after_paren = "(" <> after_sym), 0) do
          {:ok, end_idx} ->
            inner = String.slice(after_paren, 1, end_idx - 1)
            rest = String.slice(after_paren, end_idx + 1..-1//1)
            is_pi = String.contains?(String.slice(s, start, len), "PI")
            
            {name, type} = split_binder(inner)
            translated_type = transform(type)
            
            tag_open = if is_pi, do: "[", else: "("
            tag_close = if is_pi, do: "]", else: ")"
            
            final_rest = consume_arrow(rest)
            String.slice(s, 0, start) <> "#{tag_open}#{name}: #{translated_type}#{tag_close} " <> transform(final_rest)
          _ -> s
        end

      # 2. Binder without paren: PI x -> B
      match = Regex.run(~r/^(PI|LA)\s+([a-zA-Z0-9_\.@#\*]+)\s*/, s, return: :index) ->
        [{start, len} | _] = match
        [_, sym, name | _] = Regex.run(~r/^(PI|LA)\s+([a-zA-Z0-9_\.@#\*]+)\s*/, s)
        rest = String.slice(s, start + len..-1//1)
        final_rest = consume_arrow(rest)
        tag = if sym == "PI", do: "[_ : #{name}] ", else: "(_ : #{name}) "
        String.slice(s, 0, start) <> tag <> transform(final_rest)

      # 3. Top-level Arrow: A -> B
      res = find_top_arrow(s) ->
        {:ok, pos, len} = res
        lhs = String.slice(s, 0, pos)
        rhs = String.slice(s, pos + len..-1//1)
        "[_ : #{transform(lhs)}] " <> transform(rhs)

      # 4. Brackets recursion
      res = find_brackets(s) ->
        {:ok, start_p, end_p, o, c} = res
        before = String.slice(s, 0, start_p)
        inner = String.slice(s, start_p + 1, end_p - start_p - 1)
        after_all = String.slice(s, end_p + 1..-1//1)
        before <> o <> transform(inner) <> c <> transform(after_all)

      true -> s
    end
  end

  def split_binder(s) do
    case String.split(s, ":", parts: 2) do
      [name, type] -> {String.trim(name), String.trim(type)}
      [type] -> {"_", String.trim(type)}
    end
  end

  def consume_arrow(s) do
    trimmed = String.trim_leading(s)
    if String.starts_with?(trimmed, "->") do
      String.slice(trimmed, 2..-1//1)
    else
      s
    end
  end

  def find_top_arrow(s) do
    chars = String.codepoints(s)
    Enum.reduce_while(Enum.with_index(chars), 0, fn 
      c, d when elem(c,0) in ["(", "["] -> {:cont, d + 1}
      c, d when elem(c,0) in [")", "]"] -> {:cont, d - 1}
      {"-", i}, 0 -> if Enum.at(chars, i + 1) == ">", do: {:halt, {:ok, i, 2}}, else: {:cont, 0}
      _, d -> {:cont, d}
    end) |> case do {:ok, p, l} -> {:ok, p, l}; _ -> nil end
  end

  def find_brackets(s) do
    chars = String.codepoints(s)
    case Enum.find_index(chars, &(&1 in ["(", "["])) do
      nil -> nil
      start ->
        o = Enum.at(chars, start)
        case find_matching(chars, start) do
           {:ok, e} -> {:ok, start, e, o, if(o == "(", do: ")", else: "]")}
           _ -> nil
        end
    end
  end

  def find_matching(chars, start) do
    o = Enum.at(chars, start); c = if o == "(", do: ")", else: "]"
    Enum.reduce_while(Enum.drop(chars, start + 1), {start + 1, 1}, fn
      ^o, {i, d} -> {:cont, {i + 1, d + 1}}
      ^c, {i, 1} -> {:halt, {:ok, i}}
      ^c, {i, d} -> {:cont, {i + 1, d - 1}}
      _, {i, d} -> {:cont, {i + 1, d}}
    end) |> case do {:ok, i} -> {:ok, i}; _ -> :error end
  end

  def finalize(s), do: s |> String.replace(~r/\s+/, " ") |> String.trim()
end

Path.wildcard("#{morte_dir}/**/*") |> Enum.reject(&File.dir?/1) |> Enum.each(fn file ->
  rel = Path.relative_to(file, morte_dir)
  desc = Path.join(aut_dir, (rel |> String.replace("/", ".") |> String.replace(~r/[\[\]\*\+]/, "_") |> String.replace(".", "/")) <> ".aut")
  final = desc |> String.replace("/_.aut", "/@.aut")
  File.mkdir_p!(Path.dirname(final))
  IO.puts("Porting #{file} -> #{final}")
  
  c = File.read!(file) |> String.replace(~r/#[a-zA-Z0-9_\/@\-+\[\]\.<|>\?!&:\*=]+/, fn m ->
    p = String.slice(m, 1..-1//1)
    p |> String.replace("/", ".") |> String.replace(~r/[\[\]\*\+]/, "_") |> Kernel.<>(".main")
  end)

  c = PortHelper.translate_all(c)
  c = String.replace(c, ~r/\*([0-9]+)/, fn m -> "*" <> to_subs.(Regex.run(~r/[0-9]+/, m) |> hd()) end)
  c = String.replace(c, ~r/([a-zA-Z0-9_]+)@([0-9]+)/, fn m -> [_, n, i] = Regex.run(~r/([a-zA-Z0-9_]+)@([0-9]+)/, m); if i=="0", do: n, else: n <> to_subs.(i) end)
  File.write!(final, c)
end)
IO.puts("Done.")
