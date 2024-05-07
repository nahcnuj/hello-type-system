import HelloTypeSystem.Basic
import HelloTypeSystem.Meta.PeanoNat

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

/-!
## 導出システムReduceNatExprに関するメタ定理
-/
namespace ReduceNatExpr

/-!
### ReduceNatExprがPeanoNatの導出を含むこと
EvalNatExprと全く同様に証明できる。
-/

def Derivation.ofNatPlus : PeanoNat.Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂ n₃)
  | .P_Zero n => Derivation.P_Zero n
  | .P_Succ d => Derivation.P_Succ (ofNatPlus d)
instance : Coe (PeanoNat.Derivation (.Plus n₁ n₂ n₃)) (Derivation (.Plus n₁ n₂ n₃)) where
  coe := Derivation.ofNatPlus

def Derivation.toNatPlus : Derivation (.Plus n₁ n₂ n₃) → PeanoNat.Derivation (.Plus n₁ n₂ n₃)
  | .P_Zero n => PeanoNat.Derivation.P_Zero n
  | .P_Succ 𝒟 => PeanoNat.Derivation.P_Succ 𝒟.toNatPlus
instance : Coe (Derivation (.Plus n₁ n₂ n₃)) (PeanoNat.Derivation (.Plus n₁ n₂ n₃)) where
  coe := Derivation.toNatPlus

def Derivation.ofNatTimes : PeanoNat.Derivation (.Times n₁ n₂ n₃) → Derivation (.Times n₁ n₂ n₃)
  | .T_Zero n => Derivation.T_Zero n
  | .T_Succ dt dp => Derivation.T_Succ (ofNatTimes dt) (ofNatPlus dp)
instance : Coe (PeanoNat.Derivation (.Times n₁ n₂ n₃)) (Derivation (.Times n₁ n₂ n₃)) where
  coe := Derivation.ofNatTimes

def Derivation.toNatTimes : Derivation (.Times n₁ n₂ n₃) → PeanoNat.Derivation (.Times n₁ n₂ n₃)
  | .T_Zero n     => PeanoNat.Derivation.T_Zero n
  | .T_Succ dt dp => PeanoNat.Derivation.T_Succ dt.toNatTimes dp
instance : Coe (Derivation (.Times n₁ n₂ n₃)) (PeanoNat.Derivation (.Times n₁ n₂ n₃)) where
  coe := Derivation.toNatTimes

/-!
### 簡約の前進性：定理2.21 [基礎概念,§2.1]
-/
/--
簡約の前進性

異なるコンストラクタによる項`e₁,e₂`どうしの（自明な）不等式`e₁ ≠ e₂`は`Expr.noConfusion`で示せる。
`• ≠ •`は`• = • → False`だから`Expr.noConfusion` = `fun (heq : e₁ = e₂) => Expr.noConfusion heq`に注意。
-/
theorem reduce_progressive : (e : Expr) → (∀ {n}, e ≠ .Nat n) → ∃ e', Derivable (e ⟶ e') :=
  Expr.rec (motive := fun e => (∀ {n}, e ≠ .Nat n) → ∃ e', Derivable (e ⟶ e'))
    (fun _ hn => False.elim <| false_of_ne hn)
    (fun e₁ e₂ h1 h2 =>
      match e₁, e₂ with
      | .Nat n, .Nat m =>
          have ⟨k, ⟨𝒟⟩⟩ := PeanoNat.derive_plus n m
          fun _ => ⟨k, ⟨Derivation.R_Plus 𝒟⟩⟩
      | .Nat n, .Add _ _ =>
          have ⟨e₂', ⟨𝒟⟩⟩ := h2 Expr.noConfusion
          fun _ => ⟨n + e₂', ⟨Derivation.R_PlusR 𝒟⟩⟩
      | .Nat n, .Mul _ _ =>
          have ⟨e₂', ⟨𝒟⟩⟩ := h2 Expr.noConfusion
          fun _ => ⟨n + e₂', ⟨Derivation.R_PlusR 𝒟⟩⟩
      | .Add _ _, e₂ =>
          have ⟨e₁', ⟨𝒟⟩⟩ := h1 Expr.noConfusion
          fun _ => ⟨e₁' + e₂, ⟨Derivation.R_PlusL 𝒟⟩⟩
      | .Mul _ _, e₂ =>
          have ⟨e₁', ⟨𝒟⟩⟩ := h1 Expr.noConfusion
          fun _ => ⟨e₁' + e₂, ⟨Derivation.R_PlusL 𝒟⟩⟩
    )
    (fun e₁ e₂ h1 h2 =>
      match e₁, e₂ with
      | .Nat n, .Nat m =>
          have ⟨k, ⟨𝒟⟩⟩ := PeanoNat.derive_times n m
          fun _ => ⟨k, ⟨Derivation.R_Times 𝒟⟩⟩
      | .Nat n, .Add _ _ =>
          have ⟨e₂', ⟨𝒟⟩⟩ := h2 Expr.noConfusion
          fun _ => ⟨n * e₂', ⟨Derivation.R_TimesR 𝒟⟩⟩
      | .Nat n, .Mul _ _ =>
          have ⟨e₂', ⟨𝒟⟩⟩ := h2 Expr.noConfusion
          fun _ => ⟨n * e₂', ⟨Derivation.R_TimesR 𝒟⟩⟩
      | .Add _ _, e₂ =>
          have ⟨e₁', ⟨𝒟⟩⟩ := h1 Expr.noConfusion
          fun _ => ⟨e₁' * e₂, ⟨Derivation.R_TimesL 𝒟⟩⟩
      | .Mul _ _, e₂ =>
          have ⟨e₁', ⟨𝒟⟩⟩ := h1 Expr.noConfusion
          fun _ => ⟨e₁' * e₂, ⟨Derivation.R_TimesL 𝒟⟩⟩
    )
