import «HelloTypeSystem»

def answer : PNat := 42

def main : IO Unit :=
  IO.println s!"Hello, {answer}!"
