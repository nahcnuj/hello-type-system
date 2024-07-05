import HelloTypeSystem.ML2

namespace HelloTypeSystem.ML2

notation E " ⊢ " e " ⇓ " r => Evaluation E e r

/-!
# 定義、変数束縛と環境
-/

/-
## 導出システムEvalML2の評価の例

### 練習問題4.1 \[基礎概念,§4.4]
-/
example : [("y", 2), ("x", 3)] ⊢ "x" ⇓ 3 :=
  .VarIr .Var

example : [("y", 4), ("x", true)] ⊢ ("x" ? "y" + 1 : "y" - 1) ⇓ 5 :=
  .IfT
    (.VarIr .Var)
    (.Add .Var .Int)

example : [] ⊢ LET "x" = 1 + 2 IN "x" * 4 ⇓ 12 :=
  .Let
    (.Add .Int .Int)
    (.Mul .Var .Int)

example : [] ⊢ LET "x" = 3 * 3 IN LET "y" = 4 * "x" IN "x" + "y" ⇓ 45 :=
  .Let
    (.Mul .Int .Int)
    (.Let
      (.Mul .Int .Var)
      (.Add (.VarIr .Var) .Var)
    )

example : [("x", 3)] ⊢ LET "x" = "x" * 2 IN "x" + "x" ⇓ 12 :=
  .Let
    (.Mul .Var .Int)
    (.Add .Var .Var)

/-!
## 導出システムEvalML2のメタ定理

### 変数参照の評価の一意性（決定性）：補題4.2 \[基礎概念,§4.4]
-/

/--
EvalML2の変数参照の評価の一意性
-/
theorem eval_var_uniq {x : Var} {v v' : ML1.Value} : (E : Env) → (E ⊢ x ⇓ v) → (E ⊢ x ⇓ v') → v = v'
  | (x, v) :: _, .Var,       .Var        => rfl
  | (_, _) :: E, .VarIr d _, .VarIr d' _ => eval_var_uniq E d d'

/-!
### 評価の一意性（決定性）：定理4.1 \[基礎概念,§4.4]
-/

/--
EvalML2の（値の）評価の一意性
-/
theorem eval_value_uniq {E : Env} {v v' : ML1.Value} : ∀ {e : Expr}, (E ⊢ e ⇓ v) → (E ⊢ e ⇓ v') → v = v'
  | .Lit (.Z _), .Int,  .Int  => rfl
  | .Lit (.B _), .Bool, .Bool => rfl
  | .Var _, d, d' => eval_var_uniq E d d'
  | .Add .., .Add d₁ d₂, .Add d₁' d₂' =>
      have h₁ := eval_value_uniq d₁ d₁' |> ML1.Value.Z.inj
      have h₂ := eval_value_uniq d₂ d₂' |> ML1.Value.Z.inj
      congrArg ML1.Value.Z (by simp [h₁, h₂])
  | .Sub .., .Sub d₁ d₂, .Sub d₁' d₂' =>
      have h₁ := eval_value_uniq d₁ d₁' |> ML1.Value.Z.inj
      have h₂ := eval_value_uniq d₂ d₂' |> ML1.Value.Z.inj
      congrArg ML1.Value.Z (by simp [h₁, h₂])
  | .Mul .., .Mul d₁ d₂, .Mul d₁' d₂' =>
      have h₁ := eval_value_uniq d₁ d₁' |> ML1.Value.Z.inj
      have h₂ := eval_value_uniq d₂ d₂' |> ML1.Value.Z.inj
      congrArg ML1.Value.Z (by simp [h₁, h₂])
  | .LT ..,  .LTT _ _ _, .LTT _ _ _   => rfl
  | .LT ..,  .LTF _ _ _, .LTF _ _ _   => rfl
  | .If ..,  .IfT _ d,   .IfT _ d'    => eval_value_uniq d d'
  | .If ..,  .IfF _ d,   .IfF _ d'    => eval_value_uniq d d'
  | .Let .., .Let dx dv, .Let dx' dv' => eval_value_uniq dv (eval_value_uniq dx dx' ▸ dv')
  | .LT .., .LTT d₁ d₂ ht, .LTF d₁' d₂' hf =>
      have h₁ := eval_value_uniq d₁ d₁' |> ML1.Value.Z.inj
      have h₂ := eval_value_uniq d₂ d₂' |> ML1.Value.Z.inj
      absurd ht (h₁ ▸ h₂ ▸ hf)
  | .LT .., .LTF d₁ d₂ hf, .LTT d₁' d₂' ht =>
      have h₁ := eval_value_uniq d₁ d₁' |> ML1.Value.Z.inj
      have h₂ := eval_value_uniq d₂ d₂' |> ML1.Value.Z.inj
      absurd (h₁ ▸ h₂ ▸ ht) hf
  | .If .., .IfT d _, .IfF d' _ => eval_value_uniq d d' |> ML1.Value.B.inj |> Bool.noConfusion
  | .If .., .IfF d _, .IfT d' _ => eval_value_uniq d d' |> ML1.Value.B.inj |> Bool.noConfusion

/-!
### EvalML2Errの評価の（左）全域性：定理4.3 \[基礎概念,§4.4]
Leanでは関数定義に全域性が要請されるので、EvalML2Errの評価`HelloTypeSystem.ML2.Expr.eval`の定義より明らかである。
-/
