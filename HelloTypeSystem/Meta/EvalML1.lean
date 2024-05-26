import HelloTypeSystem.ML1

namespace HelloTypeSystem.ML1

/-!
# 整数・真偽値式の評価
-/

/-!
## 導出システムEvalML1(Err)の評価の例

### 練習問題3.1 \[基礎概念,§3.1]
-/

theorem «3 + 5 ⇓ 8» : Derivable (3 + 5 ⇓ 8) :=
  ⟨.E_Plus .E_Int .E_Int (.B_Plus rfl)⟩

theorem «8 - 2 - 3 ⇓ 3» : Derivable (8 - 2 - 3 ⇓ 3) :=
  ⟨.E_Minus
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    .E_Int
    (.B_Minus rfl)
  ⟩

theorem «(4 + 5) * (1 - 10) ⇓ -81» : Derivable ((4 + 5) * (1 - 10) ⇓ (-81 : Int)) :=
  ⟨.E_Times
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    (.B_Times rfl)
  ⟩

theorem «if 4 < 5 then 2 + 3 else 8 * 8 ⇓ 5» : Derivable (.If (.LT 4 5) (2 + 3) (8 * 8) ⇓ 5) :=
  ⟨.E_IfT
    (.E_LT .E_Int .E_Int (.B_LTT <| by simp))
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
  ⟩

theorem «3 + if -23 < -2 * 8 then 8 else 2 + 4 ⇓ 11» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 (2 + 4)) ⇓ 11) :=
  ⟨.E_Plus
    .E_Int
    (.E_IfT
      (.E_LT
        .E_Int
        (.E_Times .E_Int .E_Int (.B_Times rfl))
        (.B_LTT <| by simp)
      )
      .E_Int
    )
    (.B_Plus rfl)
  ⟩

theorem «3 + (if -23 < -2 * 8 then 8 else 2) + 4 ⇓ 15» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 2) + 4 ⇓ 15) :=
  ⟨.E_Plus
    (.E_Plus
      .E_Int
      (.E_IfT
        (.E_LT
          .E_Int
          (.E_Times .E_Int .E_Int (.B_Times rfl))
          (.B_LTT <| by simp)
        )
        .E_Int
      )
      (.B_Plus rfl)
    )
    .E_Int
    (.B_Plus rfl)
  ⟩

/-!
### 練習問題3.3 \[基礎概念,§3.2]
-/

theorem «1 + true ⇓ error_+» : Derivable (1 + true ⇓ Error.Plus) :=
  ⟨.E_PlusIntBool .E_Int .E_Bool⟩

theorem «1 + true + 2 ⇓ error_+» : Derivable (1 + true + 2 ⇓ Error.Plus) :=
  have ⟨𝒟⟩ := «1 + true ⇓ error_+»
  ⟨.E_PlusErr 𝒟⟩

theorem «if 2 + 3 then 1 else 3 ⇓ error_if_cond» : Derivable (.If (2 + 3) 1 3 ⇓ Error.IfCond) :=
  ⟨.E_IfCondInt (.E_Plus .E_Int .E_Int (.B_Plus rfl))⟩

theorem «if 3 < 4 then 1 < true else 3 - false ⇓ error_<» : Derivable (.If (.LT 3 4) (.LT 1 true) (3 - false) ⇓ Error.LT) :=
  ⟨.E_IfTErr
    (.E_LT .E_Int .E_Int (.B_LTT (by simp)))
    (.E_LTIntBool .E_Int .E_Bool)
  ⟩

/-!
## 導出システムEvalML1(Err)のメタ定理

### 評価の一意性：定理3.2 \[基礎概念,§3.1]
-/

/--
評価の一意性（定理3.2・練習問題3.2 \[基礎概念,§3.1]）

付帯条件の一意性はLeanのEqによって自然に示せる。
例えば加算について、
- 仮定から`h₁.symm : i₃ = i₁ + i₂`
- 仮定から`h₂ : i₁' + i₂' = i₃'`
- 左辺の導出について帰納法の仮定から`hl : i₁ = i₁'`
- 右辺の導出について帰納法の仮定から`hr : i₂ = i₂'`

より
```
i₃ = i₁  + i₂  -- h₁.symm
   = i₁' + i₂  -- hl
   = i₁' + i₂' -- hr
   = i₃'       -- h₂
```
したがって`h₂ ▸ hr ▸ hl ▸ h₁.symm : i₃ = i₃'`が証明になる。
-/
theorem eval_uniq {v₁ v₂ : Value} : {e : Expr} → Derivation (e ⇓ v₁) → Derivation (e ⇓ v₂) → v₁ = v₂
  | .C (.Z _), .E_Int,  .E_Int  => rfl
  | .C (.B _), .E_Bool, .E_Bool => rfl
  | .Add .., .E_Plus d₁l d₁r (.B_Plus h₁), .E_Plus d₂l d₂r (.B_Plus h₂) =>
      have hl := eval_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .Sub .., .E_Minus d₁l d₁r (.B_Minus h₁), .E_Minus d₂l d₂r (.B_Minus h₂) =>
      have hl := eval_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .Mul .., .E_Times d₁l d₁r (.B_Times h₁), .E_Times d₂l d₂r (.B_Times h₂) =>
      have hl := eval_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .LT .., .E_LT _ _ (.B_LTT _), .E_LT _ _ (.B_LTT _) => rfl
  | .LT .., .E_LT _ _ (.B_LTF _), .E_LT _ _ (.B_LTF _) => rfl
  | .LT .., .E_LT d₁l d₁r (.B_LTT h₁), .E_LT d₂l d₂r (.B_LTF h₂) =>
      have hl := eval_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.B <| False.elim <| absurd (hr ▸ hl ▸ h₁) h₂
  | .LT .., .E_LT d₁l d₁r (.B_LTF h₁), .E_LT d₂l d₂r (.B_LTT h₂) =>
      have hl := eval_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.B <| False.elim <| absurd (hr ▸ hl ▸ h₂) h₁
  | .If .., .E_IfT _ d₁v, .E_IfT _ d₂v =>
      eval_uniq d₁v d₂v
  | .If .., .E_IfF _ d₁v, .E_IfF _ d₂v =>
      eval_uniq d₁v d₂v
  | .If .., .E_IfT d₁c _, .E_IfF d₂c _ =>
      have := eval_uniq d₁c d₂c
      by contradiction
  | .If .., .E_IfF d₁c _, .E_IfT d₂c _ =>
      have := eval_uniq d₁c d₂c
      by contradiction
