import «HelloTypeSystem».Util

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

namespace PNat

/--
`plus`はペアノ自然数上の加算関数である。
-/
def plus : PNat → PNat → PNat
  | .Z,    n₂ => n₂
  | .S n₁, n₂ => .S <| plus n₁ n₂

/--
加算関数`plus`の左全域性
-/
theorem plus_left_total : ∀ {n₁ n₂ : PNat}, ∃ n₃ : PNat, plus n₁ n₂ = n₃
  | .Z,    n₂ => ⟨n₂, rfl⟩
  | .S n₁, n₂ => ⟨.S <| plus n₁ n₂, rfl⟩

/--
加算関数`plus`の一意性
-/
theorem plus_uniq : plus n₁ n₂ = n₃ → plus n₁ n₂ = n₃' → n₃ = n₃'
  | d, d' => Eq.trans d.symm d'

end PNat

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

namespace Expr

/--
`size`は算術式の大きさを与える。$\newcommand\Size{\mathord{\mathit{size}}}$
-/
def size : Expr → _root_.Nat
  | .Nat .Z     => 1
  | .Nat (.S n) => size n + 1
  | .Add e₁ e₂  => e₁.size + e₂.size + 1
  | .Mul e₁ e₂  => e₁.size + e₂.size + 1

/--
`size`の左全域性
-/
theorem size_left_total : ∀ {e : Expr}, ∃ n, e.size = n
  | .Nat .Z     => ⟨1, rfl⟩
  | .Nat (.S n) => ⟨size n + 1, by simp [size]⟩
  | .Add e₁ e₂  => ⟨e₁.size + e₂.size + 1, by simp [size]⟩
  | .Mul e₁ e₂  => ⟨e₁.size + e₂.size + 1, by simp [size]⟩

/--
`size`の一意性
-/
theorem size_uniq {e : Expr} : e.size = n → e.size = n' → n = n'
  | h, h' => Eq.trans h.symm h'

/--
`height`は算術式の高さを与える。$\newcommand\Height{\mathord{\mathit{height}}}$
-/
def height : Expr → _root_.Nat
  | .Nat .Z     => 1
  | .Nat (.S n) => height n + 1
  | .Add e₁ e₂  => max e₁.height e₂.height + 1
  | .Mul e₁ e₂  => max e₁.height e₂.height + 1

/--
`height`の左全域性
-/
theorem height_left_total : ∀ {e : Expr}, ∃ n, e.height = n
  | .Nat .Z     => ⟨1, rfl⟩
  | .Nat (.S n) => ⟨height n + 1, by simp [height]⟩
  | .Add e₁ e₂  => ⟨max e₁.height e₂.height + 1, by simp [height]⟩
  | .Mul e₁ e₂  => ⟨max e₁.height e₂.height + 1, by simp [height]⟩

/--
`height`の一意性
-/
theorem height_uniq {e : Expr} : e.height = n → e.height = n' → n = n'
  | h, h' => Eq.trans h.symm h'

/--
$$\forall\MV{e}\in\Set{Expr}. \Size(\MV{e}) \le 2^{\Height(\MV{e})} - 1.$$
-/
theorem size_le_prev_pow_2_height : (e : Expr) → e.size ≤ 2^e.height - 1
  | .Nat .Z =>
      calc
        _ ≤ 1     := Nat.le_refl 1
        _ = 2 - 1 := Nat.sub_one 2
  | .Nat (.S n) =>
      calc
        _ = size n + 1           := by simp [size]
        _ ≤ 2 ^ height n - 1 + 1 := Nat.succ_le_succ (size_le_prev_pow_2_height n)
        _ = 2 ^ height n + 1 - 1 := Nat.sub_add_comm Nat.one_le_two_pow |> .symm
        _ ≤ 2 ^ height n.S   - 1
          := (Nat.sub_le_sub_right · 1) <|
            calc  2 ^ height n + 1
              _ ≤ 2 ^ height n + 2 ^ height n := Nat.add_le_add_left Nat.one_le_two_pow _
              _ = 2 * 2 ^ height n            := Nat.add_same
              _ = 2 ^ (height n + 1)          := Nat.pow_succ' |> .symm
              _ = 2 ^ height n.S              := by simp [height]
  | .Add e₁ e₂ =>
      calc
        _ = e₁.size + e₂.size + 1 := by simp [size]
        _ ≤ 2 ^ (max e₁.height e₂.height + 1) - 2 + 1
          := (Nat.add_le_add_right · 1) <|
              calc e₁.size + e₂.size
                _ ≤ 2 ^ max e₁.height e₂.height - 1 + e₂.size
                  := (Nat.add_le_add_right · _) <|
                      calc e₁.size
                        _ ≤ 2 ^ e₁.height - 1 := size_le_prev_pow_2_height e₁
                        _ ≤ _
                          := (Nat.sub_le_sub_right · 1) <|
                              Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_left ..)
                _ ≤ 2 ^ max e₁.height e₂.height - 1 + (2 ^ max e₁.height e₂.height - 1)
                  := (Nat.add_le_add_left · _) <|
                      calc e₂.size
                        _ ≤ 2 ^ e₂.height - 1 := size_le_prev_pow_2_height e₂
                        _ ≤ _
                          := (Nat.sub_le_sub_right · 1) <|
                              Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_right ..)
                _ = 2 * 2 ^ max e₁.height e₂.height - 2
                  := calc
                        _ = 2 ^ max e₁.height e₂.height + (2 ^ max e₁.height e₂.height - 1) - 1
                          := Nat.sub_add_comm (Nat.one_le_two_pow) |> .symm
                        _ = 2 ^ max e₁.height e₂.height + 2 ^ max e₁.height e₂.height - 2
                          := congrArg (· - 1) <| Nat.add_sub_assoc Nat.one_le_two_pow _ |> .symm
                        _ = _ := congrArg (· - 2) Nat.add_same
                _ = 2 ^ (max e₁.height e₂.height + 1) - 2
                  := congrArg (· - 2) Nat.pow_succ'.symm
        _ = 2 ^ (max e₁.height e₂.height + 1) - 1
          := calc
                _ = 2 ^ (max e₁.height e₂.height + 1) + 1 - 2
                  := Nat.sub_add_comm (
                      (Nat.pow_le_pow_iff_right Nat.one_lt_two).mpr <| Nat.succ_le_succ (Nat.zero_le _)
                    ) |> .symm
                _ = _
                  := Nat.add_sub_add_right _ 1 1
        _ = _ := by simp [height]
  | .Mul e₁ e₂ =>
      calc
        _ = e₁.size + e₂.size + 1 := by simp [size]
        _ ≤ 2 ^ (max e₁.height e₂.height + 1) - 2 + 1
          := (Nat.add_le_add_right · 1) <|
              calc e₁.size + e₂.size
                _ ≤ 2 ^ max e₁.height e₂.height - 1 + e₂.size
                  := (Nat.add_le_add_right · _) <|
                      calc e₁.size
                        _ ≤ 2 ^ e₁.height - 1 := size_le_prev_pow_2_height e₁
                        _ ≤ _
                          := (Nat.sub_le_sub_right · 1) <|
                              Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_left ..)
                _ ≤ 2 ^ max e₁.height e₂.height - 1 + (2 ^ max e₁.height e₂.height - 1)
                  := (Nat.add_le_add_left · _) <|
                      calc e₂.size
                        _ ≤ 2 ^ e₂.height - 1 := size_le_prev_pow_2_height e₂
                        _ ≤ _
                          := (Nat.sub_le_sub_right · 1) <|
                              Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_right ..)
                _ = 2 * 2 ^ max e₁.height e₂.height - 2
                  := calc
                        _ = 2 ^ max e₁.height e₂.height + (2 ^ max e₁.height e₂.height - 1) - 1
                          := Nat.sub_add_comm (Nat.one_le_two_pow) |> .symm
                        _ = 2 ^ max e₁.height e₂.height + 2 ^ max e₁.height e₂.height - 2
                          := congrArg (· - 1) <| Nat.add_sub_assoc Nat.one_le_two_pow _ |> .symm
                        _ = _ := congrArg (· - 2) Nat.add_same
                _ = 2 ^ (max e₁.height e₂.height + 1) - 2
                  := congrArg (· - 2) Nat.pow_succ'.symm
        _ = 2 ^ (max e₁.height e₂.height + 1) - 1
          := calc
                _ = 2 ^ (max e₁.height e₂.height + 1) + 1 - 2
                  := Nat.sub_add_comm (
                      (Nat.pow_le_pow_iff_right Nat.one_lt_two).mpr <| Nat.succ_le_succ (Nat.zero_le _)
                    ) |> .symm
                _ = _
                  := Nat.add_sub_add_right _ 1 1
        _ = _ := by simp [height]

end Expr

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
namespace PeanoNat
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

end PeanoNat

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

abbrev Derivable := @HelloTypeSystem.Derivable Derivation

/--
複数回簡約$\MV{e_1}\MReduces\MV{e_2}$の導出に関する帰納法
-/
def Derivation.induction_mreduce
  {motive : Expr → Expr → Sort _} -- P(e₁,e₂)
  {e₁ e₂ : Expr}
  (hMR_Zero : ∀ {e : Expr}, motive e e)
  (hMR_Once : ∀ {e e' : Expr}, Derivation (e ⟶ e') → motive e e')
  (hMR_Multi
    : ∀ {e e' e'' : Expr},
      Derivation (e ⟶* e') → Derivation (e' ⟶* e'') → motive e e' → motive e' e'' → motive e e'')
: Derivation (e₁ ⟶* e₂) → motive e₁ e₂
  | .MR_Zero       => hMR_Zero
  | .MR_Once d     => hMR_Once d
  | .MR_Multi d d' => hMR_Multi d d' (induction_mreduce hMR_Zero hMR_Once hMR_Multi d) (induction_mreduce hMR_Zero hMR_Once hMR_Multi d')

end ReduceNatExpr

/-!
### 決定的簡約${}\DReduces{}$の簡約順序（練習問題1.10 [基礎概念,§1.4]）
ReduceNatExprは加算・乗算の左から簡約を進めるようになっていた。
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

end ReduceNatExprR
