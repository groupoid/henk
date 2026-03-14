defmodule Henk.MixProject do
  use Mix.Project

  def project do
    [
      app: :henk,
      version: "0.3.10",
      description: "The Henk Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [ extra_applications: [ :logger ] ]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: ["lib", "priv", "src", "test", "LICENSE", "README.md"],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :henk,
      links: %{"GitHub" => "https://github.com/groupoid/henk"}
    ]
  end

end
