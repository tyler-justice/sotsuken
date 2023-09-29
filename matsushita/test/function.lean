def getGreeting (name : String) := s!"Hello {name}! Isn't Lean great"

def main : IO Unit :=
  let names := ["松下", "並河", "小木曽"]
  let greetings := names.map getGreeting
  for A in greetings do
    IO.println A 