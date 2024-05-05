import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement Expr)

def   Z : PNat := .Z
def  SZ : PNat := Z.S
def SSZ : PNat := SZ.S

namespace HelloTypeSystem

namespace ReduceNatExpr

/--
導出システムReduceNatExprの推論規則
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
  | R_Plus
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (n₁ + n₂ ⟶ n₃)
  | R_Times
    : Derivation (.Times n₁ n₂ n₃) → Derivation (n₁ * n₂ ⟶ n₃)
  | R_PlusL
    : Derivation (e₁ ⟶ e₁') → Derivation (e₁ + e₂ ⟶ e₁' + e₂)
  | R_PlusR
    : Derivation (e₂ ⟶ e₂') → Derivation (e₁ + e₂ ⟶ e₁ + e₂')
  | R_TimesL
    : Derivation (e₁ ⟶ e₁') → Derivation (e₁ * e₂ ⟶ e₁' * e₂)
  | R_TimesR
    : Derivation (e₂ ⟶ e₂') → Derivation (e₁ * e₂ ⟶ e₁ * e₂')
  | MR_Zero
    : Derivation (e ⟶* e)
  | MR_Once
    : Derivation (e ⟶ e') → Derivation (e ⟶* e')
  | MR_Multi
    : Derivation (e ⟶* e') → Derivation (e' ⟶* e'') → Derivation (e ⟶* e'')
  | DR_Plus
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (n₁ + n₂ ⟶' n₃)
  | DR_Times
    : Derivation (.Times n₁ n₂ n₃) → Derivation (n₁ * n₂ ⟶' n₃)
  | DR_PlusL
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ + e₂ ⟶' e₁' + e₂)
  | DR_PlusR {n₁ : PNat}
    : Derivation (e₂ ⟶' e₂') → Derivation (n₁ + e₂ ⟶' n₁ + e₂')
  | DR_TimesL
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ * e₂ ⟶' e₁' * e₂)
  | DR_TimesR {n₁ : PNat}
    : Derivation (e₂ ⟶' e₂') → Derivation (n₁ * e₂ ⟶' n₁ * e₂')

/--
$$
\dfrac{%
  \dfrac{%
    \dfrac{}{%
      \TT{Z plus SSZ is SSZ}%
    }\mathsf{P\\_Zero}%
  }{%
    \TT{Z + SSZ ${\Reduces}$ SSZ}%
  }\mathsf{R\\_Plus}%
}{%
  \TT{Z + SSZ ${\MReduces}$ SSZ}%
}\mathsf{MR\\_Once}
$$
-/
def exercise_1_9_1 : Derivation (Z + SSZ ⟶* SSZ) :=
  (.MR_Once
    (.R_Plus
      (.P_Zero SSZ)))

def SZ_times_SZ : Derivation (.Times SZ SZ SZ) :=
  (.T_Zero SZ |>
    (.T_Succ · (.P_Zero Z |> .P_Succ)))

def exercise_1_9_2 : Derivation (SZ * SZ + SZ * SZ ⟶' SZ + SZ * SZ) :=
  (.DR_PlusL
    (.DR_Times
      SZ_times_SZ))

def exercise_1_9_3 : Derivation (SZ * SZ + SZ * SZ ⟶ SZ * SZ + SZ) :=
  (.R_PlusR
    (.R_Times
      SZ_times_SZ))

def exercise_1_9_4 : Derivation (SZ * SZ + SZ * SZ ⟶* SSZ) :=
  exercise_1_9_3 |> -- 練習問題1.9.3の`SZ * SZ + SZ * SZ ⟶ SZ * SZ + SZ`を
  .MR_Once |>       -- 規則MR_Onceで`⟶*`にして
  (.MR_Multi        -- 加算の左側にある乗算を簡約
    ·
    (.MR_Once
      (.R_PlusL
        (.R_Times SZ_times_SZ)))) |>
  (.MR_Multi        -- 加算を簡約
    ·
    (.MR_Once
      (.R_Plus
        (.P_Zero SZ |> .P_Succ))))

end ReduceNatExpr

namespace ReduceNatExprR

/--
導出システムReduceNatExprRの推論規則

ReduceNatExprの推論規則における決定的簡約${\DReduces}$のための規則を、加算・乗算の右側の部分式から簡約するように変更したもの。
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
  | R_Plus
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (n₁ + n₂ ⟶ n₃)
  | R_Times
    : Derivation (.Times n₁ n₂ n₃) → Derivation (n₁ * n₂ ⟶ n₃)
  | R_PlusL
    : Derivation (e₁ ⟶ e₁') → Derivation (e₁ + e₂ ⟶ e₁' + e₂)
  | R_PlusR
    : Derivation (e₂ ⟶ e₂') → Derivation (e₁ + e₂ ⟶ e₁ + e₂')
  | R_TimesL
    : Derivation (e₁ ⟶ e₁') → Derivation (e₁ * e₂ ⟶ e₁' * e₂)
  | R_TimesR
    : Derivation (e₂ ⟶ e₂') → Derivation (e₁ * e₂ ⟶ e₁ * e₂')
  | MR_Zero
    : Derivation (e ⟶* e)
  | MR_Once
    : Derivation (e ⟶ e') → Derivation (e ⟶* e')
  | MR_Multi
    : Derivation (e ⟶* e') → Derivation (e' ⟶* e'') → Derivation (e ⟶* e'')
  | DR_Plus
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (n₁ + n₂ ⟶' n₃)
  | DR_Times
    : Derivation (.Times n₁ n₂ n₃) → Derivation (n₁ * n₂ ⟶' n₃)
  | DR_PlusR'
    : Derivation (e₂ ⟶' e₂') → Derivation (e₁ + e₂ ⟶' e₁ + e₂')
  | DR_PlusL' {n₂ : PNat}
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ + n₂ ⟶' e₁' + n₂)
  | DR_TimesR'
    : Derivation (e₂ ⟶' e₂') → Derivation (e₁ * e₂ ⟶' e₁ * e₂')
  | DR_TimesL' {n₂ : PNat}
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ * n₂ ⟶' e₁' * n₂)

def SZ_times_SZ : Derivation (.Times SZ SZ SZ) :=
  (.T_Zero SZ |>
    (.T_Succ · (.P_Zero Z |> .P_Succ)))

def exercise_1_10_1 : Derivation (SZ * SZ + SZ * SZ ⟶' SZ * SZ + SZ) :=
  (.DR_PlusR'
    (.DR_Times
      SZ_times_SZ))

def exercise_1_10_2 : Derivation (SZ * SZ + SZ ⟶' SZ + SZ) :=
  (.DR_PlusL'
    (.DR_Times
      SZ_times_SZ))
