import «HelloTypeSystem»
open HelloTypeSystem (PNat)

def answer : PNat := 42

def main : IO Unit :=
  IO.println s!"Hello, {answer}!"
