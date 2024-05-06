import HelloTypeSystem.Basic
import HelloTypeSystem.Derivation.Nat

namespace HelloTypeSystem.EvalNatExpr

/-!
# 算術式の評価
-/

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

def Derivation.ofNatPlus : Nat.Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂ n₃)
  | .P_Zero n => Derivation.P_Zero n
  | .P_Succ d => Derivation.P_Succ (ofNatPlus d)
instance : Coe (Nat.Derivation (.Plus n₁ n₂ n₃)) (Derivation (.Plus n₁ n₂ n₃)) where
  coe := Derivation.ofNatPlus

def Derivation.toNatPlus : Derivation (.Plus n₁ n₂ n₃) → Nat.Derivation (.Plus n₁ n₂ n₃)
  | .P_Zero n => Nat.Derivation.P_Zero n
  | .P_Succ 𝒟 => Nat.Derivation.P_Succ 𝒟.toNatPlus
instance : Coe (Derivation (.Plus n₁ n₂ n₃)) (Nat.Derivation (.Plus n₁ n₂ n₃)) where
  coe := Derivation.toNatPlus

def Derivation.ofNatTimes : Nat.Derivation (.Times n₁ n₂ n₃) → Derivation (.Times n₁ n₂ n₃)
  | .T_Zero n => Derivation.T_Zero n
  | .T_Succ dt dp => Derivation.T_Succ (ofNatTimes dt) (ofNatPlus dp)
instance : Coe (Nat.Derivation (.Times n₁ n₂ n₃)) (Derivation (.Times n₁ n₂ n₃)) where
  coe := Derivation.ofNatTimes

def Derivation.toNatTimes : Derivation (.Times n₁ n₂ n₃) → Nat.Derivation (.Times n₁ n₂ n₃)
  | .T_Zero n     => Nat.Derivation.T_Zero n
  | .T_Succ dt dp => Nat.Derivation.T_Succ dt.toNatTimes dp
instance : Coe (Derivation (.Times n₁ n₂ n₃)) (Nat.Derivation (.Times n₁ n₂ n₃)) where
  coe := Derivation.toNatTimes

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

/-!
### 評価の一意性：定理2.16 [基礎概念,§2.1]
$$\forall\MV{e}\in\Set{Expr};\MV{n_1},\MV{n_2}\in\Set{PNat}. \bigl[\MV{e}\Evals\MV{n_1} \land \MV{e}\Evals\MV{n_2} \implies \MV{n_1}\equiv\MV{n_2}\bigr]$$
-/
theorem eval_uniq : {e : Expr} → Derivation (.Eval e n₁) → Derivation (.Eval e n₂) → n₁ = n₂
  | .Nat n,  .E_Const _,        .E_Const _        => rfl
  | .Add .., .E_Add 𝒟₁l 𝒟₁r 𝒟₁, .E_Add 𝒟₂l 𝒟₂r 𝒟₂ =>
      have heql := eval_uniq 𝒟₁l 𝒟₂l
      have heqr := eval_uniq 𝒟₁r 𝒟₂r
      Nat.plus_uniq (heql ▸ heqr ▸ 𝒟₁.toNatPlus) 𝒟₂
  | .Mul ..,  .E_Mul 𝒟₁l 𝒟₁r 𝒟₁, .E_Mul 𝒟₂l 𝒟₂r 𝒟₂ =>
      have heql := eval_uniq 𝒟₁l 𝒟₂l
      have heqr := eval_uniq 𝒟₁r 𝒟₂r
      Nat.times_uniq (heql ▸ heqr ▸ 𝒟₁.toNatTimes) 𝒟₂

/-!
### 算術式の諸性質
[基礎概念,§2.1]より。
-/

/--
`+`の交換法則：定理2.17
-/
theorem eval_add_comm : Derivation (e₁ + e₂ ⇓ n) → Derivation (e₂ + e₁ ⇓ n)
  | .E_Add e₁ e₂ 𝒟 => .E_Add e₂ e₁ (Nat.plus_comm 𝒟.toNatPlus)

/--
`+`の結合則：定理2.18
-/
theorem eval_add_assoc : Derivation ((e₁ + e₂) + e₃ ⇓ n) → Derivable (e₁ + (e₂ + e₃) ⇓ n)
  | .E_Add (.E_Add e₁ e₂ 𝒟') e₃ 𝒟 =>
      have ⟨_, ⟨𝒟₁⟩, ⟨𝒟₂⟩⟩ := Nat.plus_assoc_right 𝒟'.toNatPlus 𝒟.toNatPlus
      ⟨Derivation.E_Add e₁ (.E_Add e₂ e₃ 𝒟₁) (Derivation.ofNatPlus 𝒟₂)⟩

/--
`*`の交換法則：定理2.19
-/
theorem eval_mul_comm : Derivation (e₁ * e₂ ⇓ n) → Derivable (e₂ * e₁ ⇓ n)
  | .E_Mul e₁ e₂ 𝒟 =>
      have ⟨𝒟⟩ := Nat.times_comm 𝒟.toNatTimes
      Derivation.E_Mul e₂ e₁ (Derivation.ofNatTimes 𝒟)

/--
`*`の結合則：定理2.20
-/
theorem eval_mul_assoc : Derivation ((e₁ * e₂) * e₃ ⇓ n) → Derivable (e₁ * (e₂ * e₃) ⇓ n)
  | .E_Mul (.E_Mul e₁ e₂ 𝒟') e₃ 𝒟 =>
      have ⟨_, ⟨𝒟₁⟩, ⟨𝒟₂⟩⟩:= Nat.times_assoc_right 𝒟'.toNatTimes 𝒟.toNatTimes
      Derivation.E_Mul e₁ (.E_Mul e₂ e₃ 𝒟₁) (Derivation.ofNatTimes 𝒟₂)
