defmodule Henk.Mixfile do
  use Mix.Project
  def project do
    [ app: :henk,
      version: "1.0.0",
      elixir: ">= 1.9.0",
      description: "Groupoid Infinity Henk Programming Language",
      deps: deps(),
      package: package(),
    ]
  end
  def package do
    [ files: ["lib", "src", "priv", "mix.exs", "CNAME", "LICENSE"],
      maintainers: ["Namdak Tonpa"],
      licenses: ["ISC"],
      links: %{"GitHub" => "https://github.com/groupoid/henk"}
    ]
  end
  def application do
    [ extra_applications: [],
      mod: {:henk,[]}
    ]
  end
  def deps do
    [
      {:ex_doc, "~> 0.21", only: :dev}
    ]
  end
end
