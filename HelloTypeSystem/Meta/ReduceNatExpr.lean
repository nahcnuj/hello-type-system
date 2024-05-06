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

/-!
## 決定的簡約${}\DReduces{}$における簡約順序
ReduceNatExprは加算・乗算の左から簡約を進めるようになっていた。
-/
namespace ReduceNatExprR
/-!
### ReduceNatExprRによる導出の例
-/

def derive_times_SZ_SZ : Derivation (.Times 1 1 1) :=
  (.T_Zero 1 |>
    (.T_Succ · (.P_Zero 0 |> .P_Succ)))

/-!
#### 練習問題1.10 [基礎概念,§1.4]
-/
/--
(1) $\TT{SZ * SZ + SZ * SZ} \DReduces \TT{SZ * SZ + SZ}$
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

end ReduceNatExprR
