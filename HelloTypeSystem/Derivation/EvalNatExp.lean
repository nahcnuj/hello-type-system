import HelloTypeSystem.Basic
open HelloTypeSystem (PNat)

namespace EvalNatExp
/--
算術式
$$\begin{align*}
\Set{Exp} \ni \MV{e} ::={}& \MV{n} \mid \TT{$\MV{e}$ + $\MV{e}$} \mid \TT{$\MV{e}$ * $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Exp where
  | Nat (n : PNat)
  | Add (e₁ e₂ : Exp)
  | Mul (e₁ e₂ : Exp)

instance : Coe PNat Exp where
  coe := .Nat
instance : Add Exp where
  add := .Add
instance : Mul Exp where
  mul := .Mul

/--
$$\begin{align*}
\Set{PNat} \ni \MV{n} ::={}& \TT{Z} \mid \TT{S}\MV{n} \\\\
\Set{Exp} \ni \MV{e} ::={}& \MV{n} \mid \TT{$\MV{e}$ + $\MV{e}$} \mid \TT{$\MV{e}$ * $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Syntax where
  | Nat (n : PNat)
  | Exp (e : Exp)

/--
導出システムEvalNatExpが扱う判断
-/
inductive Judgement where
  /--
  "$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Plus (n₁ n₂ n₃ : PNat)
  /--
  "$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Times (n₁ n₂ n₃ : PNat)
  /--
  "$\MV{e} \Evals \MV{n}$"（$\MV{e}$ evaluates to $\MV{n}$）
  -/
  | Eval (e : Exp) (n : PNat)

notation:50 e:51 " ⇓ " n:51 => Judgement.Eval e n

/--
導出システムEvalNatExpの推論規則
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
