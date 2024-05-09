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

/-!
### 複数回簡約に関する補題
簡約の合流性の証明に用いる複数回簡約に関する補題を証明しておく。
-/

/--
加算の左の項を複数回簡約する補題。
-/
theorem Derivation.MR_PlusL
: Derivation (e ⟶* e')
→ Derivable (e + e₂ ⟶* e' + e₂) :=
  Derivation.induction_mreduce
    (motive := fun e e' => Derivable (e + _ ⟶* e' + _))
    (⟨Derivation.MR_Zero⟩)
    (fun d => ⟨Derivation.MR_Once (Derivation.R_PlusL d)⟩)
    (fun _ _ ⟨d⟩ ⟨d'⟩ => ⟨Derivation.MR_Multi d d'⟩)

/--
加算の右の項を複数回簡約する補題。
-/
theorem Derivation.MR_PlusR
: Derivation (e ⟶* e')
→ Derivable (e₁ + e ⟶* e₁ + e') :=
  Derivation.induction_mreduce
    (motive := fun e e' => Derivable (_ + e ⟶* _ + e'))
    (⟨Derivation.MR_Zero⟩)
    (fun d => ⟨Derivation.MR_Once (Derivation.R_PlusR d)⟩)
    (fun _ _ ⟨d⟩ ⟨d'⟩ => ⟨Derivation.MR_Multi d d'⟩)

/--
乗算の左の項を複数回簡約する補題。
-/
theorem Derivation.MR_TimesL
: Derivation (e ⟶* e')
→ Derivable (e * e₂ ⟶* e' * e₂) :=
  Derivation.induction_mreduce
    (motive := fun e e' => Derivable (e * _ ⟶* e' * _))
    (⟨Derivation.MR_Zero⟩)
    (fun d => ⟨Derivation.MR_Once (Derivation.R_TimesL d)⟩)
    (fun _ _ ⟨d⟩ ⟨d'⟩ => ⟨Derivation.MR_Multi d d'⟩)

/--
乗算の右の項を複数回簡約する補題。
-/
theorem Derivation.MR_TimesR
: Derivation (e ⟶* e')
→ Derivable (e₁ * e ⟶* e₁ * e') :=
  Derivation.induction_mreduce
    (motive := fun e e' => Derivable (_ * e ⟶* _ * e'))
    (⟨Derivation.MR_Zero⟩)
    (fun d => ⟨Derivation.MR_Once (Derivation.R_TimesR d)⟩)
    (fun _ _ ⟨d⟩ ⟨d'⟩ => ⟨Derivation.MR_Multi d d'⟩)

/-!
### 簡約の合流性：定理2.22 [基礎概念,§2.1]
-/
/--
簡約の合流性
-/
theorem reduce_confluence : Derivation (e₁ ⟶ e₂) → Derivation (e₁ ⟶ e₃) → ∃ e₄, Derivable (e₂ ⟶* e₄) ∧ Derivable (e₃ ⟶* e₄)
  | .R_Plus (n₃ := n₃) d1, .R_Plus (n₃ := n₃') d2 =>
      have heq : n₃ = n₃' := PeanoNat.plus_uniq d1.toNatPlus d2.toNatPlus
      Exists.intro n₃
        ⟨⟨Derivation.MR_Zero⟩
        ,heq ▸ ⟨Derivation.MR_Zero⟩
        ⟩
  | .R_Times (n₃ := n₃) d1, .R_Times (n₃ := n₃') d2 =>
      have heq : n₃ = n₃' := PeanoNat.times_uniq d1.toNatTimes d2.toNatTimes
      Exists.intro n₃
        ⟨⟨Derivation.MR_Zero⟩
        ,heq ▸ ⟨Derivation.MR_Zero⟩
        ⟩
  | .R_PlusL (e₂ := e₂) d1, .R_PlusL (e₁' := e₁'') d2 =>
      have ⟨e, ⟨d1⟩, ⟨d2⟩⟩ := reduce_confluence d1 d2
      Exists.intro (e + e₂) ⟨d1.MR_PlusL, d2.MR_PlusL⟩
  | .R_PlusL (e₁' := e₁') d1, .R_PlusR (e₂' := e₂') d2 =>
      Exists.intro (e₁' + e₂')
        ⟨Derivation.R_PlusR (e₁ := e₁') d2 |> Derivation.MR_Once
        ,Derivation.R_PlusL (e₂ := e₂') d1 |> Derivation.MR_Once
        ⟩
  | .R_PlusR (e₂' := e₂') d1, .R_PlusL (e₁' := e₁') d2 =>
      Exists.intro (e₁' + e₂')
        ⟨Derivation.R_PlusL (e₂ := e₂') d2 |> Derivation.MR_Once
        ,Derivation.R_PlusR (e₁ := e₁') d1 |> Derivation.MR_Once
        ⟩
  | .R_PlusR (e₁ := e₁) d1, .R_PlusR (e₂' := e₂'') d2 =>
      have ⟨e, ⟨d1⟩, ⟨d2⟩⟩ := reduce_confluence d1 d2
      Exists.intro (e₁ + e) ⟨d1.MR_PlusR, d2.MR_PlusR⟩
  | .R_TimesL (e₂ := e₂) d1, .R_TimesL (e₁' := e₁'') d2 =>
      have ⟨e, ⟨d1⟩, ⟨d2⟩⟩ := reduce_confluence d1 d2
      Exists.intro (e * e₂) ⟨d1.MR_TimesL, d2.MR_TimesL⟩
  | .R_TimesL (e₁' := e₁') d1, .R_TimesR (e₂' := e₂') d2 =>
      Exists.intro (e₁' * e₂')
        ⟨Derivation.R_TimesR (e₁ := e₁') d2 |> Derivation.MR_Once
        ,Derivation.R_TimesL (e₂ := e₂') d1 |> Derivation.MR_Once
        ⟩
  | .R_TimesR (e₂' := e₂') d1, .R_TimesL (e₁' := e₁') d2 =>
      Exists.intro (e₁' * e₂')
        ⟨Derivation.R_TimesL (e₂ := e₂') d2 |> Derivation.MR_Once
        ,Derivation.R_TimesR (e₁ := e₁') d1 |> Derivation.MR_Once
        ⟩
  | .R_TimesR (e₁ := e₁) d1, .R_TimesR (e₂' := e₂'') d2 =>
      have ⟨e, ⟨d1⟩, ⟨d2⟩⟩ := reduce_confluence d1 d2
      Exists.intro (e₁ * e) ⟨d1.MR_TimesR, d2.MR_TimesR⟩
