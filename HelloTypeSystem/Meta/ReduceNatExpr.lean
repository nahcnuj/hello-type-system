import HelloTypeSystem.Basic

namespace HelloTypeSystem.ReduceNatExpr

/-!
# 算術式の簡約
-/

/-!
## 算術式の簡約の例
### 練習問題1.9 [基礎概念,§1.4]
#### (1) $\TT{Z + SSZ} \MReduces \TT{SSZ}$
-/
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
def mreduce_add_Z_SSZ : Derivation (0 + 2 ⟶* 2) :=
  (.MR_Once
    (.R_Plus
      (.P_Zero 2)))

/-!
判断`SZ times SZ is SZ`をよく使うので導出しておく。
-/
def derive_times_SZ_SZ : Derivation (.Times 1 1 1) :=
  (.T_Zero 1 |>
    (.T_Succ · (.P_Zero 0 |> .P_Succ)))

/-!
#### (2) $\TT{SZ * SZ + SZ * SZ} \DReduces \TT{SZ + SZ * SZ}$
-/
def dreduce_add_mul_SZ_SZ_mul_SZ_SZ : Derivation (1 * 1 + 1 * 1 ⟶' 1 + 1 * 1) :=
  (.DR_PlusL
    (.DR_Times
      derive_times_SZ_SZ))

/-!
#### (3) $\TT{SZ * SZ + SZ * SZ} \Reduces \TT{SZ * SZ + SZ}$
-/
def reduce_add_mul_SZ_SZ_mul_SZ_SZ : Derivation (1 * 1 + 1 * 1 ⟶ 1 * 1 + 1) :=
  (.R_PlusR
    (.R_Times
      derive_times_SZ_SZ))

/-!
#### (4) $\TT{SZ * SZ + SZ * SZ} \MReduces \TT{SSZ}$
-/
def mreduce_add_mul_SZ_SZ_mul_SZ_SZ : Derivation (1 * 1 + 1 * 1 ⟶* 2) :=
  -- 右の乗算を簡約
  (.MR_Once reduce_add_mul_SZ_SZ_mul_SZ_SZ) |>
  -- 左の乗算を簡約
  (.MR_Multi
    ·
    (.MR_Once
      (.R_PlusL
        (.R_Times derive_times_SZ_SZ)))) |>
  -- 加算を簡約
  (.MR_Multi
    ·
    (.MR_Once
      (.R_Plus
        (.P_Zero 1 |> .P_Succ))))

end ReduceNatExpr

/-!
## 決定的簡約${}\DReduces{}$における簡約順序
ReduceNatExprは加算・乗算の左から簡約を進めるようになっていた。

### 練習問題1.10 [基礎概念,§1.4]
-/
namespace ReduceNatExprR
/--
導出システムReduceNatExprRの推論規則

ReduceNatExprの推論規則における決定的簡約${\DReduces}$のための規則を、加算・乗算の右側の部分式から簡約するように変更したもの。
-/
inductive Derivation : Judgement → Type where
  | P_Zero (n : PNat)
    : Derivation (.Plus 0 n n)
  | P_Succ {n₁ n₂ n}
    : Derivation (.Plus n₁ n₂ n) → Derivation (.Plus n₁.S n₂ n.S)
  | T_Zero (n : PNat)
    : Derivation (.Times 0 n 0)
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

def derive_times_SZ_SZ : Derivation (.Times 1 1 1) :=
  (.T_Zero 1 |>
    (.T_Succ · (.P_Zero 0 |> .P_Succ)))

/-!
#### (1) $\TT{SZ * SZ + SZ * SZ} \DReduces \TT{SZ * SZ + SZ}$
-/
def dreduce_add_mul_SZ_SZ_mul_SZ_SZ : Derivation (1 * 1 + 1 * 1 ⟶' 1 * 1 + 1) :=
  (.DR_PlusR'
    (.DR_Times
      derive_times_SZ_SZ))

/-!
#### (2) $\TT{SZ * SZ + SZ} \DReduces \TT{SZ + SZ}$
-/
def dreduce_add_mul_SZ_SZ_SZ : Derivation (1 * 1 + 1 ⟶' 1 + 1) :=
  (.DR_PlusL'
    (.DR_Times
      derive_times_SZ_SZ))
