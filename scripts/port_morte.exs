
# scripts/port_morte.exs
# Port priv/morte/* to priv/aut-68/*.aut
# Refined for minimalist AUT-68/Caramel syntax (no arrows, subscripts)
# Robust binder handling for nested parentheses

import Path

morte_dir = "priv/morte"
aut_dir   = "priv/aut-68"

# Subscript mapping
subscripts_map = %{
  "0" => "₀", "1" => "₁", "2" => "₂", "3" => "₃", "4" => "₄",
  "5" => "₅", "6" => "₆", "7" => "₇", "8" => "₈", "9" => "₉"
}

to_subscripts = fn str ->
  str 
  |> String.codepoints()
  |> Enum.map(fn c -> Map.get(subscripts_map, c, c) end)
  |> Enum.join()
end

# 0. Clean the target directory
if File.exists?(aut_dir) do
  IO.puts("Cleaning #{aut_dir}...")
  File.rm_rf!(aut_dir)
end
File.mkdir_p!(aut_dir)

# Find all files recursively in priv/morte
all_morte_files = Path.wildcard("#{morte_dir}/**/*") 
        |> Enum.reject(&File.dir?/1)
        |> Enum.sort()

files = Enum.reject(all_morte_files, fn f ->
  if String.ends_with?(f, ".Aut") do
    base = String.slice(f, 0..-5//1)
    Enum.member?(all_morte_files, base)
  else
    false
  end
end)

# Robust binder translator
translate_binders = fn content ->
  # Use placeholders for symbols to simplify regexes
  text = content
    |> String.replace("forall", "PI_SYM")
    |> String.replace("lambda", "LAM_SYM")
    |> String.replace("∀", "PI_SYM")
    |> String.replace("Π", "PI_SYM")
    |> String.replace("λ", "LAM_SYM")
    |> String.replace("\\/", "PI_SYM") # Single backslash followed by slash
    |> String.replace("\\", "LAM_SYM")  # Single backslash

  process = fn s, start_sym, target_start, target_end ->
    parts = String.split(s, start_sym)
    [head | tail] = parts
    Enum.reduce(tail, head, fn part, acc ->
      if String.starts_with?(part, "(") or String.starts_with?(part, " (") do
        trimmed_part = String.trim_leading(part)
        # Manual bracket matching
        find_matching = fn chars_list ->
          Enum.reduce_while(chars_list, {[], 1}, fn
            "(", {i, d} -> {:cont, {["(" | i], d + 1}}
            ")", {i, 1} -> {:halt, {i, 0}}
            ")", {i, d} -> {:cont, {[")" | i], d - 1}}
            c,   {i, d} -> {:cont, {[c | i], d}}
          end)
        end

        chars = String.codepoints(trimmed_part)
        {inside_chars, depth} = find_matching.(Enum.drop(chars, 1))
        
        if depth == 0 do
          inside = inside_chars |> Enum.reverse() |> Enum.join()
          total_len = String.length(inside) + 2
          # account for leading spaces we trimmed
          leading_spaces = String.length(part) - String.length(trimmed_part)
          remainder = String.slice(trimmed_part, total_len..-1//1)
          acc <> String.duplicate(" ", leading_spaces) <> target_start <> inside <> target_end <> remainder
        else
          acc <> start_sym <> part
        end
      else
        acc <> start_sym <> part
      end
    end)
  end

  text
  |> process.("PI_SYM", " [", "] ")
  |> process.("LAM_SYM", " (", ") ")
  |> String.replace("PI_SYM", " ")
  |> String.replace("LAM_SYM", " ")
end

Enum.each(files, fn file ->
  rel_path = Path.relative_to(file, morte_dir)
  safe_rel = rel_path 
    |> String.replace("[", "_") 
    |> String.replace("]", "_")
    |> String.replace("*", "_")
    |> String.replace("+", "_")
    |> String.replace(".", "_") # Except final dot
  
  dest_path = Path.join(aut_dir, safe_rel <> ".aut")
  File.mkdir_p!(Path.dirname(dest_path))
  IO.puts("Porting #{file} -> #{dest_path}")
  
  content = File.read!(file)
  
  content = content
    |> String.replace(~r/#[a-zA-Z0-9_\/@\-+\[\]\.<|>\?!&:\*=]+/, fn match ->
      path = String.slice(match, 1..-1//1)
      translated = String.replace(path, "/", ".")
      translated = translated 
        |> String.replace("[", "_") 
        |> String.replace("]", "_")
        |> String.replace("*", "_")
        |> String.replace("+", "_")
      translated <> ".main"
    end)

  content = translate_binders.(content)

  content = content
    |> String.replace(~r/forall/, "[_ :") # Will be followed by type and closing ]
    |> String.replace(~r/lambda/, "(_ :")
    |> String.replace(" . ", " ")

  content = String.replace(content, ~r/\*([0-9]+)/, fn match ->
    [_, num] = Regex.run(~r/\*([0-9]+)/, match)
    "*" <> to_subscripts.(num)
  end)

  content = String.replace(content, ~r/([a-zA-Z0-9_]+)@([0-9]+)/, fn match ->
    [_, name, index] = Regex.run(~r/([a-zA-Z0-9_]+)@([0-9]+)/, match)
    if index == "0" do
      name
    else
      name <> to_subscripts.(index)
    end
  end)

  File.write!(dest_path, content)
end)

IO.puts("\nPorting complete.")
