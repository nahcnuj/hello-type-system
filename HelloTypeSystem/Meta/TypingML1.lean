import HelloTypeSystem.ML1

namespace HelloTypeSystem.ML1

/-!
# ML1に対する型付け

## 型付けの例
-/

theorem «3 + 5 : int» : Derivable (⊢ 3 + 5 : .Int) :=
  ⟨.T_Plus .T_Int .T_Int⟩

theorem «if 2 < 3 then 5 + 1 else 7 - 1 : int» : Derivable (⊢ .If (.LT 2 3) (5 + 1) (7 - 1) : .Int) :=
  ⟨.T_If
    (.T_LT .T_Int .T_Int)
    (.T_Plus .T_Int .T_Int)
    (.T_Minus .T_Int .T_Int)
  ⟩

theorem «if 3 < 2 then 5 < 7 else 13 < 11 : bool» : Derivable (⊢ .If (.LT 3 2) (.LT 5 7) (.LT 13 11) : .Bool) :=
  ⟨.T_If
    (.T_LT .T_Int .T_Int)
    (.T_LT .T_Int .T_Int)
    (.T_LT .T_Int .T_Int)
  ⟩

/-!
## 型安全性
-/

/--
TypingML1による型安全性
-/
theorem type_safety : (dt : Derivation (⊢ e : τ)) → (de : Derivation (e ⇓ r)) → ∃ v : Value, r = .inr v ∧ (τ = .Int → ∃ i : Int, v = .Z i) ∧ (τ = .Bool → ∃ b : Bool, v = .B b)
  | .T_Int            , .E_Int   (i  := i)       => ⟨.Z i, rfl, fun _ => ⟨i, rfl⟩, fun h => ⟨true, Types.noConfusion h⟩⟩
  | .T_Bool           , .E_Bool  (b  := b)       => ⟨.B b, rfl, fun h => ⟨0, Types.noConfusion h⟩, fun _ => ⟨b, rfl⟩⟩
  | .T_Plus  ..       , .E_Plus  (i₃ := i) ..    => ⟨.Z i, rfl, fun _ => ⟨i, rfl⟩, fun h => ⟨true, Types.noConfusion h⟩⟩
  | .T_Minus ..       , .E_Minus (i₃ := i) ..    => ⟨.Z i, rfl, fun _ => ⟨i, rfl⟩, fun h => ⟨true, Types.noConfusion h⟩⟩
  | .T_Times ..       , .E_Times (i₃ := i) ..    => ⟨.Z i, rfl, fun _ => ⟨i, rfl⟩, fun h => ⟨true, Types.noConfusion h⟩⟩
  | .T_LT    ..       , .E_LT    (b  := b) ..    => ⟨.B b, rfl, fun h => ⟨0, Types.noConfusion h⟩, fun _ => ⟨b, rfl⟩⟩
  | .T_If    _ dt₂ _  , .E_IfT             _ de₂ => type_safety dt₂ de₂
  | .T_If    _ _   dt₃, .E_IfF             _ de₃ => type_safety dt₃ de₃

  -- 以下、deが実行時エラーの導出の場合に矛盾を導く
  | .T_Plus _ dt₂, .E_PlusIntBool _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Plus _ dt₂, .E_PlusIntErr _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion
  | .T_Plus dt₁ _, .E_PlusBool de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Plus dt₁ _, .E_PlusErr de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion

  | .T_Minus _ dt₂, .E_MinusIntBool _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Minus _ dt₂, .E_MinusIntErr _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion
  | .T_Minus dt₁ _, .E_MinusBool de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Minus dt₁ _, .E_MinusErr de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion

  | .T_Times _ dt₂, .E_TimesIntBool _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Times _ dt₂, .E_TimesIntErr _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion
  | .T_Times dt₁ _, .E_TimesBool de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_Times dt₁ _, .E_TimesErr de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion

  | .T_LT _ dt₂, .E_LTIntBool _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_LT _ dt₂, .E_LTIntErr _ de₂ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₂ de₂
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion
  | .T_LT dt₁ _, .E_LTBool de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_LT dt₁ _, .E_LTErr de₁ =>
      have ⟨_, heq, h, _⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion

  | .T_If dt₁ _ _, .E_IfCondInt de₁ =>
      have ⟨_, heq, _, h⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.inr.inj |> Value.noConfusion
  | .T_If dt₁ _ _, .E_IfCondErr de₁ =>
      have ⟨_, heq, _, h⟩ := type_safety dt₁ de₁
      have ⟨_, h⟩ := h rfl
      h ▸ heq |> Sum.noConfusion
  | .T_If _ dt₂ _, .E_IfTErr _ de₂ =>
      have ⟨_, heq, _, _⟩ := type_safety dt₂ de₂
      Sum.noConfusion heq
  | .T_If _ _ dt₃, .E_IfFErr _ de₃ =>
      have ⟨_, heq, _, _⟩ := type_safety dt₃ de₃
      Sum.noConfusion heq
