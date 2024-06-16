namespace HelloTypeSystem

theorem Nat.add_same {n : _root_.Nat} : n + n = 2 * n :=
  calc
    _ = 1 * n + 1 * n := by rw [Nat.one_mul]
    _ = _             := Nat.add_mul 1 1 _ |> .symm

def Set (α : Type u) := α → Prop
instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False
instance : Singleton α (Set α) where
  singleton x := fun y => x = y
instance : Membership α (Set α) where
  mem x s := s x
instance : Union (Set α) where
  union a b := fun x => x ∈ a ∨ x ∈ b
instance : SDiff (Set α) where
  sdiff a b := fun x => x ∈ a ∧ ¬ x ∈ b
instance : HasSubset (Set α) where
  Subset a b := ∀ x ∈ a, x ∈ b

theorem singleton_mem_uniq {a x : α} : a ∈ ({ x } : Set α) → x = a := id
