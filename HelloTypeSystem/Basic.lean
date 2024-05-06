namespace HelloTypeSystem

/-!
# 諸定義

## ペアノ自然数PNat
-/

/--
ペアノ自然数
$$\begin{align*}
\Set{PNat} \ni \MV{n} ::={}& \TT{Z} \mid \TT{S}\MV{n} \\\\
\end{align*}$$
-/
inductive PNat
  | Z
  | S (n : PNat)

instance : OfNat PNat 0 where
  ofNat := PNat.Z

instance (n : Nat) [OfNat PNat n] : OfNat PNat (Nat.succ n) where
  ofNat := PNat.S (OfNat.ofNat n)

def PNat.toNat : PNat → Nat
  | .Z   => Nat.zero
  | .S n => Nat.succ n.toNat

instance : Coe PNat Nat where
  coe n := n.toNat

instance : ToString PNat where
  toString n := s!"{n.toNat}"

/-!
## 算術式Expr
-/

/--
算術式
$$\begin{align*}
\Set{Expr} \ni \MV{e} ::={}& \MV{n} \mid \TT{$\MV{e}$ + $\MV{e}$} \mid \TT{$\MV{e}$ * $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Expr where
  | Nat (n : PNat)
  | Add (e₁ e₂ : Expr)
  | Mul (e₁ e₂ : Expr)

instance : Coe PNat Expr where
  coe := .Nat
instance : Add Expr where
  add := .Add
instance : Mul Expr where
  mul := .Mul

instance [OfNat PNat n] : OfNat Expr n where
  ofNat := Expr.Nat (OfNat.ofNat n)

/-!
## 判断（judgement）
-/

/--
判断

この型の項は形式上は正しい判断であるが、内容的にも正しいとは限らない。
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
  "$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$"
  -/
  | LT (n₁ n₂ : PNat)
  /--
  "$\MV{e} \Evals \MV{n}$" means that $\MV{e}$ evaluates to $\MV{n}$.
  -/
  | Eval (e : Expr) (n : PNat)
  /--
  "$\MV{e} \Reduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ at a time.
  -/
  | Reduce (e : Expr) (e' : Expr)
  /--
  "$\MV{e} \MReduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ at some time.
  -/
  | MReduce (e : Expr) (e' : Expr)
  /--
  "$\MV{e} \DReduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ deterministically.
  -/
  | DReduce (e : Expr) (e' : Expr)

notation:50 e:51 " ⇓ " n:51  => Judgement.Eval e n
notation:50 e:51 " ⟶ " e':51 => Judgement.Reduce e e'
notation:50 e:51 " ⟶* " e':51 => Judgement.MReduce e e'
notation:50 e:51 " ⟶' " e':51 => Judgement.DReduce e e'

/--
与えられた判断が導出できるという命題
-/
inductive Derivable {Derivation : Judgement → Type v} (𝒥 : Judgement) : Prop where
  | intro (h : Derivation 𝒥)

/--
導出の項が構築できたときは明らかに導出できるので型強制する
-/
instance {𝒥 : Judgement} {Derivation : Judgement → Type u} : Coe (Derivation 𝒥) (Derivable (Derivation := Derivation) 𝒥) where
  coe := Derivable.intro

/-!
## 導出システム
-/

/-!
### ペアノ自然数の加算・乗算：Nat
-/
namespace Nat
/--
導出システムNatの推論規則による導出
-/
inductive Derivation : Judgement → Type where
  /--
  任意のペアノ自然数$\MV{n}$に対して、判断"$\TT{Z plus $\MV{n}$ is $\MV{n}$}$"を導いて良い。
  -/
  | P_Zero (n : PNat)
    : Derivation (.Plus .Z n n)
  /--
  任意のペアノ自然数$\MV{n_1},\MV{n_2},\MV{n_3}$に対して、判断"$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"から"$\TT{S$\MV{n_1}$ plus $\MV{n_2}$ is S$\MV{n_3}$}$"を導いて良い。
  -/
  | P_Succ {n₁ n₂ n₃ : PNat}
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S)
  /--
  "$\TT{Z times $\MV{n}$ is Z}$"
  -/
  | T_Zero (n : PNat)
    : Derivation (.Times .Z n .Z)
  /--
  "$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"かつ"$\TT{$\MV{n_2}$ plus $\MV{n_3}$ is $\MV{n_4}$}$"ならば、"$\TT{S$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_4}$}$"
  -/
  | T_Succ {n₁ n₂ n₃ n₄ : PNat}
    : Derivation (.Times n₁ n₂ n₃) → Derivation (.Plus n₂ n₃ n₄) → Derivation (.Times n₁.S n₂ n₄)

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

def Derivation.induction_plus
  {motive : PNat → PNat → PNat → Sort _} -- P(n₁,n₂,n₃)
  {n₁ n₂ n₃ : PNat}
  (hP_Zero : ∀ n : PNat, motive .Z n n)
  (hP_Succ : ∀ {n₁ n₂ n₃ : PNat}, Derivation (.Plus n₁ n₂ n₃) → motive n₁ n₂ n₃ → motive n₁.S n₂ n₃.S)
: Derivation (.Plus n₁ n₂ n₃) → motive n₁ n₂ n₃
  | .P_Zero n => hP_Zero n
  | .P_Succ d => hP_Succ d (Derivation.induction_plus hP_Zero hP_Succ d)

def Derivation.induction_times
  {motive : PNat → PNat → PNat → Sort _} -- P(n₁,n₂,n₃)
  {n₁ n₂ n₃ : PNat}
  (hT_Zero : ∀ n : PNat, motive .Z n .Z)
  (hT_Succ : ∀ {n₁ n₂ n₃ n₄: PNat}, Derivation (.Times n₁ n₂ n₃) → Derivation (.Plus n₂ n₃ n₄) → motive n₁ n₂ n₃ → motive n₁.S n₂ n₄)
: Derivation (.Times n₁ n₂ n₃) → motive n₁ n₂ n₃
  | .T_Zero n     => hT_Zero n
  | .T_Succ dt dp => hT_Succ dt dp (dt.induction_times hT_Zero hT_Succ)

end Nat

/-!
### ペアノ自然数の比較：CompareNat1--3
-/
namespace CompareNat1
/--
導出システムCompareNat1の推論規則
-/
inductive Derivation : Judgement → Type where
  | LT_Succ (n : PNat)
    : Derivation (.LT n n.S)
  | LT_Trans {n₁ n₂ n₃ : PNat}
    : Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivation (.LT n₁ n₃)

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

/--
CompareNat1における$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$の導出に関する帰納法で、
ペアノ自然数に関する2項述語$P$について$\forall\MV{n_1},\MV{n_2}. \bigl[\TT{$\MV{n_1}$ is less than $\MV{n_2}$} \implies P(\MV{n_1},\MV{n_2})\bigr]$を示す。

自動で生成される`casesOn`や`rec`などは`motive`の型が`(a : Judgement) → Derivation a → Sort u`となっていて、
ペアノ自然数に関する述語$P(\MV{n_1},\MV{n_2})$を扱うには`PNat → PNat → Sort u`な関数を作る必要があった。
-/
def Derivation.induction
  {motive : PNat → PNat → Sort _} -- P(n₁,n₂)
  {n₁ n₂ : PNat}
  (H0 : ∀ n : PNat, motive n n.S)
  (H1 : ∀ {n₁ n₂ n₃ : PNat}, Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → motive n₁ n₂ → motive n₂ n₃ → motive n₁ n₃)
: Derivation (.LT n₁ n₂) → motive n₁ n₂
  | .LT_Succ k      => H0 k
  | .LT_Trans 𝒟₁ 𝒟₂ => H1 𝒟₁ 𝒟₂ (induction H0 H1 𝒟₁) (induction H0 H1 𝒟₂)

end CompareNat1

namespace CompareNat2
/--
導出システムCompareNat2の推論規則
-/
inductive Derivation : Judgement → Type where
  | LT_Zero (n : PNat)
    : Derivation (.LT .Z n.S)
  | LT_SuccSucc {n₁ n₂ : PNat}
    : Derivation (.LT n₁ n₂) → Derivation (.LT n₁.S n₂.S)

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

/--
CompareNat2における$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$の導出に関する帰納法
-/
def Derivation.induction
  {motive : PNat → PNat → Sort _} -- P(n₁,n₂)
  {n₁ n₂ : PNat}
  (H0 : ∀ n : PNat, motive .Z n.S)
  (H1 : ∀ {n₁ n₂ : PNat}, Derivation (.LT n₁ n₂) → motive n₁ n₂ → motive n₁.S n₂.S)
: Derivation (.LT n₁ n₂) → motive n₁ n₂
  | .LT_Zero n     => H0 n
  | .LT_SuccSucc 𝒟 => H1 𝒟 (induction H0 H1 𝒟)

end CompareNat2

namespace CompareNat3
/--
導出システムCompareNat3の推論規則
-/
inductive Derivation : Judgement → Type where
  | LT_Succ (n : PNat)
    : Derivation (.LT n n.S)
  | LT_SuccR {n₁ n₂ : PNat}
    : Derivation (.LT n₁ n₂) → Derivation (.LT n₁ n₂.S)

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

/--
CompareNat3における$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$の導出に関する帰納法
-/
def Derivation.induction
  {motive : PNat → PNat → Sort _} -- P(n₁,n₂)
  {n₁ n₂ : PNat}
  (H0 : ∀ n : PNat, motive n n.S)
  (H1 : ∀ {n₁ n₂ : PNat}, Derivation (.LT n₁ n₂) → motive n₁ n₂ → motive n₁ n₂.S)
: Derivation (.LT n₁ n₂) → motive n₁ n₂
  | .LT_Succ n  => H0 n
  | .LT_SuccR 𝒟 => H1 𝒟 (induction H0 H1 𝒟)

end CompareNat3

/-!
### 算術式の評価
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

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

end EvalNatExpr

namespace ReduceNatExpr
/--
導出システムReduceNatExprの推論規則
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
  | DR_PlusL
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ + e₂ ⟶' e₁' + e₂)
  | DR_PlusR {n₁ : PNat}
    : Derivation (e₂ ⟶' e₂') → Derivation (n₁ + e₂ ⟶' n₁ + e₂')
  | DR_TimesL
    : Derivation (e₁ ⟶' e₁') → Derivation (e₁ * e₂ ⟶' e₁' * e₂)
  | DR_TimesR {n₁ : PNat}
    : Derivation (e₂ ⟶' e₂') → Derivation (n₁ * e₂ ⟶' n₁ * e₂')

end ReduceNatExpr
