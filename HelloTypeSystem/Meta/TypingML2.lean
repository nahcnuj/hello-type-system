import HelloTypeSystem.Meta.EvalML2

namespace HelloTypeSystem.ML2
open ML2

notation Γ " ⊢ " e " : " τ => Typed Γ e τ
notation "⊨ " E " : " Γ => EnvCompat E Γ

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
  | .Int,  .Int  (i := i) => ⟨i, rfl, fun _ => ⟨_, rfl⟩, Types.noConfusion⟩
  | .Bool, .Bool (b := b) => ⟨b, rfl, Types.noConfusion, fun _ => ⟨_, rfl⟩⟩
  | .Var, .Var =>
      have  ⟨_, v, hE, _, hvc⟩ := compat
      have heq := List.head_eq_of_cons_eq hE |> congrArg Prod.snd |> congrArg Sum.inr
      ⟨v, heq, fun h => have ⟨v, hv⟩ := h ▸ hvc ; ⟨v, hv |> Expr.Lit.inj⟩, fun h => have ⟨v, hv⟩ := h ▸ hvc ; ⟨v, hv |> Expr.Lit.inj⟩⟩
  | .VarIr dt _, .VarIr dv _ =>
      have ⟨_, _, hE, compat', _⟩ := compat
      have dv := List.tail_eq_of_cons_eq hE ▸ dv
      type_safety compat' dt dv
  | .Add .., .Add (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ + i₂, rfl, fun _ => ⟨_, rfl⟩, Types.noConfusion⟩
  | .Sub .., .Sub (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ - i₂, rfl, fun _ => ⟨_, rfl⟩, Types.noConfusion⟩
  | .Mul .., .Mul (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ * i₂, rfl, fun _ => ⟨_, rfl⟩, Types.noConfusion⟩
  | .LT  .., .LTT _ _ _                    => ⟨true,    rfl, Types.noConfusion, fun _ => ⟨_, rfl⟩⟩
  | .LT  .., .LTF _ _ _                    => ⟨false,   rfl, Types.noConfusion, fun _ => ⟨_, rfl⟩⟩
  | .If _ dt _, .IfT _ dv =>
      have ⟨v, heq, hi, hb⟩ := type_safety compat dt dv
      ⟨v, Sum.inr.inj heq ▸ rfl, hi, hb⟩
  | .If _ _ dt, .IfF _ dv =>
      have ⟨v, heq, hi, hb⟩ := type_safety compat dt dv
      ⟨v, Sum.inr.inj heq ▸ rfl, hi, hb⟩
  | .Let (τ₁ := τ₁) dtb dte, .Let (v₁ := v₁) dvb dve =>
      have ⟨_, heq, hi, hb⟩ := type_safety compat dtb dvb
      have : ValueCompat v₁ τ₁ :=
        have heq := Sum.inr.inj heq
        match τ₁ with
        | .Int  => have ⟨v, h⟩ := hi rfl ; heq ▸ ⟨v, congrArg Expr.Lit h⟩
        | .Bool => have ⟨v, h⟩ := hb rfl ; heq ▸ ⟨v, congrArg Expr.Lit h⟩
      have compat' := ⟨E, v₁, rfl, compat, this⟩
      type_safety compat' dte dve

  -- 部分式について型不整合または実行時エラーの場合は矛盾することを示す
  | .Add dt _, .AddBoolL dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Add _ dt, .AddBoolR dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Add dt _, .AddErrL de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Add _ dt, .AddErrR de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Sub dt _, .SubBoolL dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Sub _ dt, .SubBoolR dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Sub dt _, .SubErrL de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Sub _ dt, .SubErrR de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Mul dt _, .MulBoolL dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Mul _ dt, .MulBoolR dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .Mul dt _, .MulErrL de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Mul _ dt, .MulErrR de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .LT dt _, .LTBoolL dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .LT _ dt, .LTBoolR dv =>
      have ⟨.B _, _, h, _⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .LT dt _, .LTErrL de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .LT _ dt, .LTErrR de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .If dt _ _, .IfInt dv =>
      have ⟨.Z _, _, _, h⟩ := type_safety compat dt dv
      have ⟨_, h⟩ := h rfl
      ML1.Value.noConfusion h
  | .If dt _ _, .IfErr de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .If _ dt _, .IfTErr _ de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .If _ _ dt, .IfFErr _ de =>
      have ⟨_, h, _⟩ := type_safety compat dt de
      Sum.noConfusion h
  | .Let dtb _, .LetBindingErr dvb =>
      have ⟨_, h, _⟩ := type_safety compat dtb dvb
      Sum.noConfusion h
  | .Let (τ₁ := τ₁) dtb dte, .LetExprErr (v₁ := v₁) dvb dve =>
      have ⟨_, heq, hi, hb⟩ := type_safety compat dtb dvb
      have : ValueCompat v₁ τ₁ :=
        have heq := Sum.inr.inj heq
        match τ₁ with
        | .Int  => have ⟨v, h⟩ := hi rfl ; heq ▸ ⟨v, congrArg Expr.Lit h⟩
        | .Bool => have ⟨v, h⟩ := hb rfl ; heq ▸ ⟨v, congrArg Expr.Lit h⟩
      have compat' := ⟨E, v₁, rfl, compat, this⟩
      have ⟨_, h, _⟩ := type_safety compat' dte dve
      Sum.noConfusion h
