import HelloTypeSystem.ML1

namespace HelloTypeSystem.ML1

/-!
# ML1に対する型付け

## 型付けの例
-/

theorem «3 + 5 : int» : Derivable (⊢ 3 + 5 : Int) :=
  ⟨.T_Plus .T_Int .T_Int⟩

theorem «if 2 < 3 then 5 + 1 else 7 - 1 : int» : Derivable (⊢ .If (.LT 2 3) (5 + 1) (7 - 1) : Int) :=
  ⟨.T_If
    (.T_LT .T_Int .T_Int)
    (.T_Plus .T_Int .T_Int)
    (.T_Minus .T_Int .T_Int)
  ⟩

theorem «if 3 < 2 then 5 < 7 else 13 < 11 : bool» : Derivable (⊢ .If (.LT 3 2) (.LT 5 7) (.LT 13 11) : Bool) :=
  ⟨.T_If
    (.T_LT .T_Int .T_Int)
    (.T_LT .T_Int .T_Int)
    (.T_LT .T_Int .T_Int)
  ⟩

/-!
## 型安全性
-/

set_option maxHeartbeats 0
-- theorem type_safety : (dt : Derivation (⊢ e : τ)) → (de : Derivation (e ⇓ r)) → ∃ v : Value, r = .inr v ∧ ((τ = Int → ∃ i : Int, v = .Z i) ∨ (τ = Bool → ∃ b : Bool, v = .B b))
--   | .T_Int,      .E_Int   (i := i)        => ⟨.Z i, rfl, .inl <| fun _ => ⟨i, rfl⟩⟩
--   | .T_Bool,     .E_Bool  (b := b)        => ⟨.B b, rfl, .inr <| fun _ => ⟨b, rfl⟩⟩
--   | .T_Plus _ _, .E_Plus  (i₃ := i) _ _ _ => ⟨.Z i, rfl, .inl <| fun _ => ⟨i, rfl⟩⟩
--   -- | .T_Plus _ dt₂, .E_PlusIntBool (b₂ := b₂) _ de₂ =>
--   --     have ⟨w, heq, h⟩ := type_safety dt₂ de₂
--   --     -- have : ¬ Sum.inl Error.Plus = Sum.inr (Value.Z 0) := Sum.noConfusion
--   --     have : False := ((Sum.inr.inj heq).symm ▸ h).elim
--   --       (fun h => have ⟨_, h⟩ := h rfl; Value.noConfusion h)
--   --       (fun h => h sorry)
--   --       -- (fun ⟨0, h⟩ => Value.noConfusion h)
--   --       -- (fun ⟨b, h⟩ => sorry)
--   --     ⟨.Z 0, sorry, .inl ⟨0, rfl⟩⟩
--   | .T_Minus _ _, _ => sorry
--   | .T_Times _ _, _ => sorry
--   | .T_LT _ _, _ => sorry
--   | .T_If _ _ _, _ => sorry
--   | _, _ => sorry

theorem type_safety_ : (dt : Derivation (⊢ e : τ)) → (de : Derivation (e ⇓ r)) → ∃ v : Value, r = .inr v ∧ ((∃ i : Int, v = .Z i) ∨ (∃ b : Bool, v = .B b)) :=
  fun dt de =>
    match de with
    | .E_Int   (i  := i)       => ⟨.Z i, rfl, .inl <| ⟨i, rfl⟩⟩
    | .E_Bool  (b  := b)       => ⟨.B b, rfl, .inr <| ⟨b, rfl⟩⟩
    | .E_Plus  (i₃ := i) _ _ _ => ⟨.Z i, rfl, .inl <| ⟨i, rfl⟩⟩
    | .E_Minus (i₃ := i) _ _ _ => ⟨.Z i, rfl, .inl <| ⟨i, rfl⟩⟩
    | .E_Times (i₃ := i) _ _ _ => ⟨.Z i, rfl, .inl <| ⟨i, rfl⟩⟩
    | .E_LT    (b  := b) _ _ _ => ⟨.B b, rfl, .inr <| ⟨b, rfl⟩⟩
    | .E_IfT   (v  := v) _ d   =>
        ⟨v, rfl,
          match dt with
          | .T_If _ (.T_Int  (i := i)) _ => .inl <| match d with | .E_Int  => ⟨i, rfl⟩
          | .T_If _ (.T_Bool (b := b)) _ => .inr <| match d with | .E_Bool => ⟨b, rfl⟩
          | .T_If _ (.T_Plus dt₁ _)    _ => .inl <|
              match d with
              | .E_Plus (i₁ := i₁) (i₂ := i₂) de₁ _ (.B_Plus heq) =>
                  have ⟨_, heq₁, h₁⟩ := type_safety_ dt₁ de₁
                  h₁.elim
                    (fun ⟨i, h⟩ => ⟨i₁ + i₂, heq ▸ rfl⟩)
                    (fun ⟨b, h⟩ => (Sum.inr.inj heq₁).symm ▸ h |> Value.noConfusion)
          | .T_If _ (.T_Minus dt₁ _) _ => .inl <|
              match d with
              | .E_Minus (i₁ := i₁) (i₂ := i₂) de₁ _ (.B_Minus heq) =>
                  have ⟨_, heq₁, h₁⟩ := type_safety_ dt₁ de₁
                  h₁.elim
                    (fun ⟨i, h⟩ => ⟨i₁ - i₂, heq ▸ rfl⟩)
                    (fun ⟨b, h⟩ => (Sum.inr.inj heq₁).symm ▸ h |> Value.noConfusion)
          | .T_If _ (.T_Times dt₁ _) _ => .inl <|
              match d with
              | .E_Times (i₁ := i₁) (i₂ := i₂) de₁ _ (.B_Times heq) =>
                  have ⟨_, heq₁, h₁⟩ := type_safety_ dt₁ de₁
                  h₁.elim
                    (fun ⟨i, h⟩ => ⟨i₁ * i₂, heq ▸ rfl⟩)
                    (fun ⟨b, h⟩ => (Sum.inr.inj heq₁).symm ▸ h |> Value.noConfusion)
          | .T_If _ (.T_LT _ _) _ => .inr <|
              match d with
              | .E_LT (b := true)  _ _ (.B_LTT _) => ⟨true,  rfl⟩
              | .E_LT (b := false) _ _ (.B_LTF _) => ⟨false, rfl⟩
          | .T_If _ (.T_If _ dt₂ dt₃) _ =>
              match d with
              | .E_IfT _ de₂ =>
                  have ⟨_, heq, h⟩ := type_safety_ dt₂ de₂
                  Sum.inr.inj heq ▸ h
              | .E_IfF _ de₃ =>
                  have ⟨_, heq, h⟩ := type_safety_ dt₃ de₃
                  Sum.inr.inj heq ▸ h
        ⟩
    | _ => sorry
