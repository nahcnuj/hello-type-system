import HelloTypeSystem.Basic
import HelloTypeSystem.Derivation.Nat

namespace HelloTypeSystem

/-!
# 算術式の評価
-/

namespace EvalNatExpr
/--
導出システムEvalNatExprの推論規則
-/
inductive Derivation : Judgement → Type where
  | P_Zero (n : PNat)
    : Derivation (.Plus .Z n n)
  | P_Succ {n₁ n₂ n}
    : Derivation (.Plus n₁ n₂ n) → Derivation (.Plus n₁.S n₂ n.S)
  | T_Zero (n : PNat)
    : Derivation (.Times .Z n .Z)
  | T_Succ {n₁ n₂ n₃ n₄ : PNat}
    : Derivation (.Times n₁ n₂ n₃) → Derivation (.Plus n₂ n₃ n₄) → Derivation (.Times n₁.S n₂ n₄)
  | E_Const (n : PNat)
    : Derivation (n ⇓ n)
  | E_Add
    : Derivation (e₁ ⇓ n₁) → Derivation (e₂ ⇓ n₂) → Derivation (.Plus n₁ n₂ n) → Derivation (e₁ + e₂ ⇓ n)
  | E_Mul
    : Derivation (e₁ ⇓ n₁) → Derivation (e₂ ⇓ n₂) → Derivation (.Times n₁ n₂ n) → Derivation (e₁ * e₂ ⇓ n)

private abbrev Derivable := @HelloTypeSystem.Derivable Derivation

/-!
## 算術式の評価の例
### 練習問題1.8 [基礎概念,§1.4]
#### (1) `Z + SSZ ⇓ SSZ`
-/

/--
$$
\dfrac{
  \dfrac{}{\TT{Z} \Evals \TT{Z}}\mathsf{E\\_Const}\qquad%
  \dfrac{}{\TT{SSZ} \Evals \TT{SSZ}}\mathsf{E\\_Const}\qquad%
  \dfrac{}{\TT{Z plus SSZ is SSZ}}\mathsf{P\\_Zero}%
}{\TT{Z + SSZ} \Evals \TT{SSZ}}\mathsf{E\\_Add}.
$$
-/
def eval_add_Z_SSZ : Derivation (PNat.Z + PNat.S (.S .Z) ⇓ .S (.S .Z)) :=
  (.E_Add
    (.E_Const .Z)
    (.E_Const (.S (.S .Z)))
    (.P_Zero (.S (.S .Z))))

/-!
#### (2) `SSZ + Z ⇓ SSZ`
-/
def eval_add_SSZ_Z : Derivation (PNat.S (.S .Z) + PNat.Z ⇓ .S (.S .Z)) :=
  (.E_Add
    (.E_Const (.S (.S .Z)))
    (.E_Const .Z)
    (.P_Zero .Z |> .P_Succ |> .P_Succ))

/-!
#### (3) `SZ + SZ + SZ ⇓ SSSZ`
-/
def eval_add_add_SZ_SZ_SZ : Derivation (PNat.S .Z + PNat.S .Z + PNat.S .Z ⇓ .S (.S (.S .Z))) :=
  (.E_Add
    (.E_Add
      (.E_Const (.S .Z))
      (.E_Const (.S .Z))
      (.P_Zero (.S .Z) |> .P_Succ))
    (.E_Const (.S .Z))
    (.P_Zero (.S .Z) |> .P_Succ |> .P_Succ))

/-!
#### (4) `SSSZ + SSZ * SZ ⇓ SSSSSZ`
-/
def eval_add_SSSZ_mul_SSZ_SZ : Derivation ((PNat.S (.S (.S .Z))) + (PNat.S (.S .Z)) * (PNat.S .Z) ⇓ .S (.S (.S (.S (.S .Z))))) :=
  (.E_Add
    (.E_Const (.S (.S (.S .Z))))
    (.E_Mul
      (.E_Const (.S (.S .Z)))
      (.E_Const (.S .Z))
      (.T_Succ
        (.T_Succ
          (.T_Zero (.S .Z))
          (.P_Zero .Z |> .P_Succ))
        (.P_Zero (.S .Z) |> .P_Succ)))
    (.P_Zero (.S (.S .Z)) |> .P_Succ |> .P_Succ |> .P_Succ))

/-!
(5),(6)には同じ`SSZ + SSZ`の評価が現れるので先に導出しておく。
-/
def eval_add_SSZ_SSZ : Derivation (PNat.S (.S .Z) + PNat.S (.S .Z) ⇓ .S (.S (.S (.S .Z)))) :=
    (.E_Add
      (.E_Const (.S (.S .Z)))
      (.E_Const (.S (.S .Z)))
      (.P_Zero (.S (.S .Z)) |> .P_Succ |> .P_Succ))

/-!
#### (5) `(SSZ + SSZ) * Z ⇓ Z`
-/
def eval_mul_add_SSZ_SSZ_Z : Derivation (((PNat.S (.S .Z)) + (PNat.S (.S .Z))) * PNat.Z ⇓ .Z) :=
  (.E_Mul
    (eval_add_SSZ_SSZ)
    (.E_Const .Z)
    (.T_Zero .Z |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z))))

/-!
#### (6) `Z * (SSZ + SSZ) ⇓ Z`
-/
def eval_mul_Z_add_SSZ_SSZ : Derivation (PNat.Z * (PNat.S (.S .Z) + PNat.S (.S .Z)) ⇓ .Z) :=
  (.E_Mul
    (.E_Const .Z)
    (eval_add_SSZ_SSZ)
    (.T_Zero (.S (.S (.S (.S .Z))))))

/-!
## EvalNatExprがNatの導出を含むこと
-/

instance : Coe (Nat.Derivation (.Plus n₁ n₂ n₃)) (Derivation (.Plus n₁ n₂ n₃)) where
  coe :=
    Nat.Derivation.induction_plus (motive := fun n₁ n₂ n₃ => Derivation (.Plus n₁ n₂ n₃))
      (Derivation.P_Zero)
      (fun _ => Derivation.P_Succ)

instance : Coe (Nat.Derivation (.Times n₁ n₂ n₃)) (Derivation (.Times n₁ n₂ n₃)) where
  coe :=
    Nat.Derivation.induction_times (motive := fun n₁ n₂ n₃ => Derivation (.Times n₁ n₂ n₃))
      (Derivation.T_Zero ·)
      (fun _ dp dt => Derivation.T_Succ dt dp)

/-!
## 算術式の評価に関するメタ定理
### 評価の（左）全域性（評価結果の存在性）：定理2.15 [基礎概念,§2.3]
$$\forall\MV{e}\in\Set{Expr}. \exists\MV{n}\in\Set{PNat}. \MV{e}\Evals\MV{n}$$
-/
theorem eval_left_total : (e : Expr) → ∃ n : PNat, Derivable (e ⇓ n) :=
  Expr.rec (motive := fun e => ∃ n : PNat, Derivable (e ⇓ n))
    (fun n => ⟨n, Derivation.E_Const n⟩)
    (fun _e₁ _e₂ ⟨n₁,⟨𝒟₁⟩⟩ ⟨n₂,⟨𝒟₂⟩⟩ =>
      have ⟨«n₁+n₂», ⟨𝒟p⟩⟩ := Nat.derive_plus n₁ n₂
      ⟨«n₁+n₂», ⟨Derivation.E_Add 𝒟₁ 𝒟₂ 𝒟p⟩⟩
    )
    (fun _e₁ _e₂ ⟨n₁,⟨𝒟₁⟩⟩ ⟨n₂,⟨𝒟₂⟩⟩ =>
      have ⟨«n₁*n₂», ⟨𝒟t⟩⟩ := Nat.derive_times n₁ n₂
      ⟨«n₁*n₂», ⟨Derivation.E_Mul 𝒟₁ 𝒟₂ 𝒟t⟩⟩
    )

theorem plus_uniq {n₁ n₂ n₃ n₄ : PNat} : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂ n₄) → n₃ = n₄
  | .P_Zero _,  .P_Zero _  => rfl
  | .P_Succ ha, .P_Succ hb => congrArg PNat.S (plus_uniq ha hb)
theorem times_uniq {n₂ n₃ n₄ : PNat} : {n₁ : PNat} → Derivation (.Times n₁ n₂ n₃) → Derivation (.Times n₁ n₂ n₄) → n₃ = n₄
  | .Z,   .T_Zero _,               .T_Zero _               => rfl
  | .S _, .T_Succ (n₃ := k) ha hb, .T_Succ (n₃ := l) hc hd =>
      -- hb : Derivation (Judgement.Plus n₂ k n₃)
      -- hd : Derivation (Judgement.Plus n₂ l n₄)
      have : k = l := times_uniq ha hc
      plus_uniq (this ▸ hb) hd

/-!
### 評価の一意性：定理2.16 [基礎概念,§2.1]
$$\forall\MV{e}\in\Set{Expr};\MV{n_1},\MV{n_2}\in\Set{PNat}. \bigl[\MV{e}\Evals\MV{n_1} \land \MV{e}\Evals\MV{n_2} \implies \MV{n_1}\equiv\MV{n_2}\bigr]$$
-/
theorem eval_uniq : {e : Expr} → Derivation (.Eval e n₁) → Derivation (.Eval e n₂) → n₁ = n₂
  | .Nat n, .E_Const _, .E_Const _ => rfl
  | .Add .., .E_Add 𝒟₁l 𝒟₁r 𝒟₁, .E_Add 𝒟₂l 𝒟₂r 𝒟₂ =>
      have heql := eval_uniq 𝒟₁l 𝒟₂l
      have heqr := eval_uniq 𝒟₁r 𝒟₂r
      plus_uniq (heql ▸ heqr ▸ 𝒟₁) 𝒟₂
  | .Mul ..,  .E_Mul 𝒟₁l 𝒟₁r 𝒟₁, .E_Mul 𝒟₂l 𝒟₂r 𝒟₂ =>
      have heql := eval_uniq 𝒟₁l 𝒟₂l
      have heqr := eval_uniq 𝒟₁r 𝒟₂r
      times_uniq (heql ▸ heqr ▸ 𝒟₁) 𝒟₂
