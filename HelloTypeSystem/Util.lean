namespace HelloTypeSystem

theorem Nat.add_same {n : _root_.Nat} : n + n = 2 * n :=
  calc
    _ = 1 * n + 1 * n := by rw [Nat.one_mul]
    _ = _             := Nat.add_mul 1 1 _ |> .symm

abbrev ℤ := _root_.Int
abbrev 𝔹 := _root_.Bool

def Set (α : Type u) := α → Prop

@[simp]
instance : Membership α (Set α) where
  mem x s := s x

instance : HasSubset (Set α) where
  Subset a b := ∀ x ∈ a, x ∈ b
theorem Subset.trans {a b c : Set α} : a ⊆ b → b ⊆ c → a ⊆ c :=
  fun hab hbc x ha =>
    have hb := hab x ha
    hbc x hb

instance : Union (Set α) where
  union a b := fun x => x ∈ a ∨ x ∈ b
theorem Union.subset_intro_left  {a b : Set α} : a ⊆ a ∪ b := fun _ => Or.inl
theorem Union.subset_intro_right {a b : Set α} : b ⊆ a ∪ b := fun _ => Or.inr

instance : Insert α (Set α) where
  insert a as := fun x => x = a ∨ x ∈ as

instance : SDiff (Set α) where
  sdiff a b := fun x => x ∈ a ∧ ¬ x ∈ b

instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Singleton α (Set α) where
  singleton x := fun y => x = y
theorem Singleton.mem_iff_eq_elem {a x : α} : a ∈ ({ x } : Set α) ↔ x = a := ⟨id, id⟩

theorem subset_right_of_union {a b : Set α} : b ⊆ a ∪ b := fun _ => Or.inr

namespace Set

theorem union_assoc {a b c : Set α} : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  funext fun x => by
    simp [Membership.mem]
    exact Iff.intro
      (Or.elim ·
        (Or.elim · Or.inl (Or.inr ∘ Or.inl))
        (Or.inr ∘ Or.inr)
      )
      (Or.elim ·
        (Or.inl ∘ Or.inl)
        (Or.elim · (Or.inl ∘ Or.inr) Or.inr)
      )
