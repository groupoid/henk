defmodule AUTOMATH do
  @moduledoc """
      50 years of Pure Type Systems

      AUTOMATH (c) 1968, Nicolaas Govert de Bruijn
      Calculus of Construction (c) 1988, Thierry Coquand
      Morte (c) 2014, Gabriella Gonzalez
      Henk (c) 2018, Namdak Tonpa

      CoC Syntax:

      *₁₀₁        -- 101-th Universe
      [x : A] Exp -- Universal Quantifier
      (x : A) Exp -- Lambda
      M N         -- Application
      L₁          -- Variable with de Bruijn index 1
      """

  def ilst(x), do: :erlang.integer_to_list(x)
  def lsti(x), do: :erlang.list_to_integer(x)
  def lstb(x), do: :binary.list_to_bin(x)
  def lbin(x), do: :erlang.list_to_binary(x)
  def atmb(x), do: :erlang.atom_to_binary(x)
  def utf8(x), do: :unicode.characters_to_binary(x)

  def sub(x) when x >= 0 and x < 10, do: utf8([8320+x])
  def sub(x), do: lstb(:lists.map(fn x -> sub(lsti([x])) end, ilst(x)))
  def bin(x) when is_list(x),        do: lbin(x)
  def bin(x) when is_binary(x),      do: x
  def bin(x) when is_atom(x),        do: atmb(x)
  def name(s,x),                     do: bin(s) <> sub(x)

  def ext({:star,x}),                do: name("*",x)
  def ext({:var,{s,x}}),             do: name(s,x)
  def ext({:app,{a,b}}),             do: {ext(a),ext(b)}
  def ext({{"∀",{s,x}},{i,o}}),      do: {:"П",name(s,x),ext(i),ext(o)}
  def ext({"→",{i,o}}),              do: {:"П",name("_",0),ext(i),ext(o)}
  def ext({{"λ",{s,x}},{i,o}}),      do: {:"λ",name(s,x),ext(i),ext(o)}

  def prn({:star,x}),                          do: name("*",x)
  def prn({:var,{s,x}}),                       do: name(s,x)
  def prn({:app,{{:app,{a,x}},{:app,{y,b}}}}), do: "#{prn(a)}∘#{prn(x)}∘(#{prn(y)}∘#{prn(b)})"
  def prn({:app,{{:app,{a,x}},b}}),            do: "#{prn(a)}∘#{prn(x)}∘#{prn(b)}"
  def prn({:app,{a,{:app,{x,b}}}}),            do: "#{prn(a)}∘(#{prn(x)}∘#{prn(b)})"
  def prn({:app,{a,b}}),                       do: "#{prn(a)}∘#{prn(b)}"
  def prn({"→",{i,o}}),                        do: "#{prn(i)}→#{prn(o)}"
  def prn({{"∀",{"_",_}},{i,o}}),              do: "#{prn(i)}→#{prn(o)}"
  def prn({{"∀",{s,x}},{i,o}}),                do: "[#{name(s,x)}:#{prn(i)}]#{prn(o)}"
  def prn({{"λ",{s,x}},{i,o}}),                do: "(#{name(s,x)}:#{prn(i)})#{prn(o)}"

end
