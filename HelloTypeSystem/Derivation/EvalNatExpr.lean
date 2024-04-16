import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement Expr)

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

/--
$$
\dfrac{
  \dfrac{}{\TT{Z} \Evals \TT{Z}}\mathsf{E\\_Const}\qquad%
  \dfrac{}{\TT{SSZ} \Evals \TT{SSZ}}\mathsf{E\\_Const}\qquad%
  \dfrac{}{\TT{Z plus SSZ is SSZ}}\mathsf{P\\_Zero}%
}{\TT{Z + SSZ} \Evals \TT{SSZ}}\mathsf{E\\_Add}.
$$
-/
def exercise_1_8_1 : Derivation (PNat.Z + PNat.S (.S .Z) ⇓ .S (.S .Z)) :=
  (.E_Add
    (.E_Const .Z)
    (.E_Const (.S (.S .Z)))
    (.P_Zero (.S (.S .Z))))

def exercise_1_8_2 : Derivation (PNat.S (.S .Z) + PNat.Z ⇓ .S (.S .Z)) :=
  (.E_Add
    (.E_Const (.S (.S .Z)))
    (.E_Const .Z)
    (.P_Zero .Z |> .P_Succ |> .P_Succ))

def exercise_1_8_3 : Derivation (PNat.S .Z + PNat.S .Z + PNat.S .Z ⇓ .S (.S (.S .Z))) :=
  (.E_Add
    (.E_Add
      (.E_Const (.S .Z))
      (.E_Const (.S .Z))
      (.P_Zero (.S .Z) |> .P_Succ))
    (.E_Const (.S .Z))
    (.P_Zero (.S .Z) |> .P_Succ |> .P_Succ))

def exercise_1_8_4 : Derivation ((PNat.S (.S (.S .Z))) + (PNat.S (.S .Z)) * (PNat.S .Z) ⇓ .S (.S (.S (.S (.S .Z))))) :=
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

def eval_SSZ_plus_SSZ : Derivation (PNat.S (.S .Z) + PNat.S (.S .Z) ⇓ .S (.S (.S (.S .Z)))) :=
    (.E_Add
      (.E_Const (.S (.S .Z)))
      (.E_Const (.S (.S .Z)))
      (.P_Zero (.S (.S .Z)) |> .P_Succ |> .P_Succ))

def exercise_1_8_5 : Derivation (((PNat.S (.S .Z)) + (PNat.S (.S .Z))) * PNat.Z ⇓ .Z) :=
  (.E_Mul
    (eval_SSZ_plus_SSZ)
    (.E_Const .Z)
    (.T_Zero .Z |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z)) |>
      (.T_Succ · (.P_Zero .Z))))

def exercise_1_8_6 : Derivation (PNat.Z * (PNat.S (.S .Z) + PNat.S (.S .Z)) ⇓ .Z) :=
  (.E_Mul
    (.E_Const .Z)
    (eval_SSZ_plus_SSZ)
    (.T_Zero (.S (.S (.S (.S .Z))))))
