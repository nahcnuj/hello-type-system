import HelloTypeSystem.Meta.EvalML2

namespace HelloTypeSystem.ML2
open ML2

notation Γ " ⊢ " e " : " τ => Typed Γ e τ
notation "⊨ " E " : " Γ => Env.compat E Γ

/-!
# ML2に対する型付け
-/

/-
## 型付けの例
-/

example : [("y", .Int), ⟨"x", .Bool⟩] ⊢ .If "x" ("y" + 1) ("y" - 1) : .Int :=
  .If
    (.VarIr .Var)
    (.Add .Var .Int)
    (.Sub .Var .Int)

example : [] ⊢ .Let "x" (.LT 3 2) (.Let "y" 5 (.If "x" "y" 2)) : .Int :=
  .Let
    (.LT .Int .Int)
    (.Let
      (.Int)
      (.If
        (.VarIr .Var)
        (.Var)
        (.Int)
      )
    )

/-!
## 型安全性
-/

/--
TypingML2による型安全性
-/
theorem type_safety (compat : (⊨ E : Γ)) : (Γ ⊢ e : τ) → (E ⊢ e ⇓ r) → ∃ v : ML1.Value, r = .inr v ∧ (τ = .Int → ∃ i : Int, v = i) ∧ (τ = .Bool → ∃ b : Bool, v = b)
  | .Int,          .Int  (i := i) => ⟨i, rfl, fun _ => ⟨i, rfl⟩, Types.noConfusion⟩
  | .Bool,         .Bool (b := b) => ⟨b, rfl, Types.noConfusion, fun _ => ⟨b, rfl⟩⟩
  | .Var,          .Var  (v := v) => sorry
      -- have := if_pos (t := True) (e := False) rfl
      -- have := compat
      -- have := if_pos rfl compat
      -- sorry
      -- ⟨v, rfl, compat.left rfl⟩
  -- | .VarIr dt hne, .Var           => sorry -- type_safety (compat.right hne.symm) dt .Var
  -- | .VarIr (y := y) dt hne, .VarIr (y := y') (v := .Z i) dv hne2 =>
  --     sorry
  -- | .VarIr (y := y) dt hne, .VarIr (y := y') (v := v) dv hne2 =>
  --     compat.elim fun h1 _ =>
  --       Or.elim (Decidable.em (y' = y))
  --         (fun heq =>
  --           have := h1 heq
  --           sorry)
  --         (fun _ => sorry)
        -- ⟨v, rfl, sorry⟩
      -- have := compat.right sorry
      -- Or.elim (Decidable.em (y' = y))
      --   (fun heq =>
      --     have := compat.right sorry
      --     have compat' := heq ▸ compat
      --     have := compat'.left rfl
      --     have := type_safety sorry dt dv
      --     sorry)
      --   (sorry)
      -- have := compat.right hne
      -- sorry
  | _, _ => sorry
