defmodule Henk do
  use Application
  def start(_, _) do
      opts = [strategy: :one_for_one, name: App.Supervisor]
      :henk.start(:"Morte",[])
      Supervisor.start_link([], opts)
  end
end
