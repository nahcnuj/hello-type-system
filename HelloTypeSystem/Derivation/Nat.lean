import HelloTypeSystem.Basic

namespace Nat

/--
導出システムNatの判断
-/
inductive Judgement where
  /--
  "$n_1$ plus $n_2$ is $n_3$"
  -/
  | Plus : PNat → PNat → PNat → Judgement
  /-
  "$n_1$ times $n_2$ is $n_3$"
  -/
  | Times : PNat → PNat → PNat → Judgement

/--
導出システムNatの推論規則による導出
-/
inductive Derivation : Judgement → Type where
  /--
  任意のペアノ自然数$n$に対して、判断"${\tt Z}$ plus $n$ is $n$"を導いて良い
  -/
  | P_Zero (n : PNat)
    : Derivation (.Plus .Z n n)
  /--
  任意のペアノ自然数$n_1,n_2,n_3$に対して、判断"$n_1$ plus $n_2$ is $n_3$"から"${\tt S}n_1$ plus $n_2$ is ${\tt S}n_3$"を導いて良い
  -/
  | P_Succ (n₁ n₂ n₃ : PNat)
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S)
  /--
  $∀n$, "${\tt Z}$ times $n$ is ${\tt Z}$"
  -/
  | T_Zero (n : PNat)
    : Derivation (.Times .Z n .Z)
  /--
  $∀n_1, n_2, n_3, n_4$, ("$n_1$ times $n_2$ is $n_3$"かつ"$n_2$ plus $n_3$ is $n_4$"ならば"${\tt S}n_1$ times $n_2$ is $n_4$")
  -/
  | T_Succ (n₁ n₂ n₃ n₄ : PNat)
    : Derivation (.Times n₁ n₂ n₃) → Derivation (.Plus n₂ n₃ n₄) → Derivation (.Times n₁.S n₂ n₄)

/-!
"${\tt Z}$ plus ${\tt SSSSSZ}$ is ${\tt SSSSSZ}$"は規則P_Zeroで$n = {\tt SSSSSZ}$とすれば導かれる。
-/
example : Derivation (.Plus .Z (.S (.S (.S (.S (.S (.Z)))))) (.S (.S (.S (.S (.S (.Z))))))) :=
  .P_Zero (n := .S (.S (.S (.S (.S (.Z))))))

namespace Derivation
/--
任意のペアノ自然数$n$に対して、規則P_Zeroを1回用いて判断"${\tt Z}$ plus $n$ is $n$"を導ける
-/
def Z_plus (n : PNat) : Derivation (.Plus .Z n n) :=
  .P_Zero n

def S_plus (n₁ n₂ n₃ : PNat) : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S) :=
  .P_Succ n₁ n₂ n₃

/-!
判断"${\tt SSZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSSZ}$"の導出
1. 規則P_Zeroで$n = {\tt SSSZ}$として"${\tt Z}$ plus ${\tt SSSZ}$ is ${\tt SSSZ}$"
2. 規則P_Succで$n_1 = {\tt Z}, n_2 = {\tt SSSZ}, n_3 = {\tt SSSZ}$として、前提は1.で導かれているから"${\tt SZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSZ}$"
3. 規則P_Succで$n_1 = {\tt SZ}, n_2 = {\tt SSSZ}, n_3 = {\tt SSSSZ}$として、前提は2.で導かれているから"${\tt SSZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSSZ}$"
-/
example : Derivation (.Plus (.S (.S .Z)) (.S (.S (.S .Z))) (.S (.S (.S (.S (.S .Z)))))) :=
  -- Step 1
  .P_Zero (.S (.S (.S .Z))) |>
  -- Step 2
  .P_Succ (n₁ := .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S .Z))) |>
  -- Step 3
  .P_Succ (n₁ := .S .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))

/-!
判断"${\tt SSZ}$ times ${\tt SSZ}$ is ${\tt SSSSZ}$"の導出
1. 規則T_Zeroから"${\tt Z}$ times ${\tt SSZ}$ is ${\tt Z}$"
2. 規則T_Succから"${\tt SZ}$ times ${\tt SSZ}$ is ${\tt SSZ}$"
    - ここで規則P_ZeroとP_Succから"${\tt SSZ}$ plus ${\tt Z}$ is ${\tt SSZ}$"を導出してもう一つの前提に使う
3. 規則T_Succから"${\tt SSZ}$ times ${\tt SSZ}$ is ${\tt SSSSZ}$"
    - 同様にして"${\tt SSZ}$ plus ${\tt Z}$ is ${\tt SSZ}$"をもう一つの前提に使う
-/
example : Derivation (.Times (.S (.S .Z)) (.S (.S .Z)) (.S (.S (.S (.S .Z))))) :=
  (.T_Zero (.S (.S .Z))) |>
  (.T_Succ (n₁ := .Z) (n₂ := .S (.S .Z)) (n₃ := .Z) (n₄ := .S (.S .Z))
    ·
    (.P_Zero .Z |>
      .P_Succ (n₁ := .Z) (n₂ := .Z) (n₃ := .Z) |>
      .P_Succ (n₁ := .S .Z) (n₂ := .Z) (n₃ := .S .Z))) |>
  (.T_Succ (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S .Z)) (n₄ := .S (.S (.S (.S .Z))))
    ·
    (.P_Zero (.S (.S .Z)) |>
      .P_Succ (n₁ := .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S .Z)) |>
      .P_Succ (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S .Z)))))

def plus_Z : ∀ (n : PNat), Derivation (.Plus n .Z n)
  | .Z   => .P_Zero .Z
  | .S n => .P_Succ (n₁ := n) (n₂ := .Z) (n₃ := n) (plus_Z n)

/--
練習問題1.2 (1) 判断"${\tt SSSZ}$ plus ${\tt SZ}$ is ${\tt SSSSZ}$"の導出
-/
def exercise_1_2_1 : Derivation (.Plus (.S (.S (.S .Z))) (.S .Z) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S .Z) |>
  .P_Succ (.Z) (.S .Z) (.S .Z) |>
  .P_Succ (.S .Z) (.S .Z) (.S (.S .Z)) |>
  .P_Succ (.S (.S .Z)) (.S .Z) (.S (.S (.S .Z)))

/--
練習問題1.2 (2) 判断"${\tt SZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSZ}$"の導出
-/
def exercise_1_2_2 : Derivation (.Plus (.S .Z) (.S (.S (.S .Z))) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S (.S (.S .Z))) |>
  .P_Succ (.Z) (.S (.S (.S .Z))) (.S (.S (.S .Z)))

/--
練習問題1.2 (3) 判断"${\tt SSSZ}$ times ${\tt Z}$ is ${\tt Z}$"の導出
-/
def exercise_1_2_3 : Derivation (.Times (.S (.S (.S .Z))) .Z .Z) :=
  .T_Zero .Z |>
  (.T_Succ (.Z) (.Z) (.Z) (.Z) · (.P_Zero .Z)) |>
  (.T_Succ (.S .Z) (.Z) (.Z) (.Z) · (.P_Zero .Z)) |>
  (.T_Succ (.S (.S .Z)) (.Z) (.Z) (.Z) · (.P_Zero .Z))

def steps {judge : Judgement} : Derivation judge → Nat
  | .P_Zero _           => 1
  | .P_Succ _ _ _ h     => 1 + h.steps
  | .T_Zero _           => 1
  | .T_Succ _ _ _ _ h k => 1 + h.steps + k.steps

example : steps exercise_1_2_1 = 4 := rfl
example : steps exercise_1_2_2 = 2 := rfl
example : steps exercise_1_2_3 = 7 := rfl

theorem steps_P_Zero (n : PNat)
  : steps (.P_Zero n) = 1 := rfl
theorem steps_P_Succ {n m : PNat} (h : Derivation (.Plus n m (n + m)))
  : steps (.P_Succ n m (n + m) h) = 1 + h.steps := rfl

/- TODO
theorem steps_T_Succ {n m : PNat} (ht : Derivation (.Times n m (n * m))) (hp : Derivation (.Plus m (n * m) ((.S n) * m)))
  : steps (.T_Succ n _ _ (n * m) ht hp) = 1 + ht.steps + hp.steps := rfl
-/

/--
導出システムNatにおいて、任意の$n,m∈ℕ$に対する判断"$n$ plus $m$ is $(n+m)$"は$n + 1$ステップで導出できる。
-/
theorem steps_plus {n m : PNat} : (h : Derivation (.Plus n m (n + m))) → steps h = n + 1
  | .P_Zero _ => rfl
  | .P_Succ _ _ _ ih =>
      steps_P_Succ ih ▸
      congrArg (1 + ·) (steps_plus ih) ▸
      congrArg (Nat.succ) (PNat.toNat_succ _)

/- TODO
/--
導出システムNatにおいて、任意の$n,m∈ℕ$に対する判断"$n$ times $m$ is $nm$"は$n (m+1) + 1$ステップで導出できる。
-/
theorem steps_times {n m : PNat} : (h : Derivation (.Times n m (n * m))) → steps h = n * (m + 1) + 1
  | .T_Zero _ => rfl
  | .T_Succ _ _ _ _ ih n => rfl
-/
