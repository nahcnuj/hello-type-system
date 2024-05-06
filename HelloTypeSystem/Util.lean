namespace HelloTypeSystem

theorem Nat.add_same {n : _root_.Nat} : n + n = 2 * n :=
  calc
    _ = 1 * n + 1 * n := by rw [Nat.one_mul]
    _ = _             := Nat.add_mul 1 1 _ |> .symm
