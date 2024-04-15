import HelloTypeSystem.Basic

namespace Nat
/--
導出システムNatの判断
-/
inductive Judgement where
  /--
  "$n_1$ plus $n_2$ is $n_3$"
  -/
  | Plus (n₁ n₂ n₃ : PNat) : Judgement
  /-
  "$n_1$ times $n_2$ is $n_3$"
  -/
  | Times (n₁ n₂ n₃ : PNat) : Judgement

/--
導出システムNatの推論規則による導出
-/
inductive Derivation : Judgement → Type where
  /--
  任意のペアノ自然数$n$に対して、判断"${\tt Z}$ plus $n$ is $n$"を導いて良い。
  -/
  | P_Zero (n : PNat)
    : Derivation (.Plus .Z n n)
  /--
  任意のペアノ自然数$n_1,n_2,n_3$に対して、判断"$n_1$ plus $n_2$ is $n_3$"から"${\tt S}n_1$ plus $n_2$ is ${\tt S}n_3$"を導いて良い。
  -/
  | P_Succ {n₁ n₂ n₃ : PNat}
    : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S)
  /--
  $∀n$, "${\tt Z}$ times $n$ is ${\tt Z}$"を導いて良い。
  -/
  | T_Zero (n : PNat)
    : Derivation (.Times .Z n .Z)
  /--
  $∀n_1, n_2, n_3, n_4$, "$n_1$ times $n_2$ is $n_3$"かつ"$n_2$ plus $n_3$ is $n_4$"ならば"${\tt S}n_1$ times $n_2$ is $n_4$"を導いて良い。
  -/
  | T_Succ {n₁ n₂ n₃ n₄ : PNat}
    : Derivation (.Times n₁ n₂ n₃) → Derivation (.Plus n₂ n₃ n₄) → Derivation (.Times n₁.S n₂ n₄)

/-!
"${\tt Z}$ plus ${\tt SSSSSZ}$ is ${\tt SSSSSZ}$"は規則P_Zeroで$n = {\tt SSSSSZ}$とすれば導ける。
-/
example : Derivation (.Plus .Z (.S (.S (.S (.S (.S (.Z)))))) (.S (.S (.S (.S (.S (.Z))))))) :=
  .P_Zero (n := .S (.S (.S (.S (.S (.Z))))))

/--
任意のペアノ自然数$n$に対して、規則P_Zeroを1回用いて判断"${\tt Z}$ plus $n$ is $n$"を導ける。
-/
def Derivation.Z_plus (n : PNat) : Derivation (.Plus .Z n n) :=
  .P_Zero n

/--
任意のペアノ自然数$n_1, n_2, n_3$に対して、判断"$n_1$ plus $n_2$ is $n_3$"の導出から規則P_Succを1回用いて"${\tt S}n_1$ plus $n_2$ is ${\tt S}n_3$"を導ける。
-/
def Derivation.S_plus {n₁ n₂ n₃ : PNat} : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S) :=
  @Derivation.P_Succ n₁ n₂ n₃

/--
判断"${\tt SSZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSSZ}$"の導出
1. 規則P_Zeroで$n = {\tt SSSZ}$として"${\tt Z}$ plus ${\tt SSSZ}$ is ${\tt SSSZ}$"
2. 規則P_Succで$n_1 = {\tt Z}, n_2 = {\tt SSSZ}, n_3 = {\tt SSSZ}$として、前提は1.で導かれているから"${\tt SZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSZ}$"
3. 規則P_Succで$n_1 = {\tt SZ}, n_2 = {\tt SSSZ}, n_3 = {\tt SSSSZ}$として、前提は2.で導かれているから"${\tt SSZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSSZ}$"
-/
def SSZ_plus_SSSZ : Derivation (.Plus (.S (.S .Z)) (.S (.S (.S .Z))) (.S (.S (.S (.S (.S .Z)))))) :=
  -- Step 1
  .P_Zero (.S (.S (.S .Z))) |>
  -- Step 2
  .P_Succ (n₁ := .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S .Z))) |>
  -- Step 3
  .P_Succ (n₁ := .S .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))

/--
判断"${\tt SSZ}$ times ${\tt SSZ}$ is ${\tt SSSSZ}$"の導出
1. 規則T_Zeroから"${\tt Z}$ times ${\tt SSZ}$ is ${\tt Z}$"
2. 規則T_Succから"${\tt SZ}$ times ${\tt SSZ}$ is ${\tt SSZ}$"
    - ここで規則P_ZeroとP_Succから"${\tt SSZ}$ plus ${\tt Z}$ is ${\tt SSZ}$"を導出してもう一つの前提に使う
3. 規則T_Succから"${\tt SSZ}$ times ${\tt SSZ}$ is ${\tt SSSSZ}$"
    - 同様にして"${\tt SSZ}$ plus ${\tt Z}$ is ${\tt SSZ}$"をもう一つの前提に使う
-/
def SSZ_times_SSZ : Derivation (.Times (.S (.S .Z)) (.S (.S .Z)) (.S (.S (.S (.S .Z))))) :=
  (.T_Zero (.S (.S .Z))) |>
  (.T_Succ (n₁ := .Z) (n₂ := .S (.S .Z)) (n₃ := .Z) (n₄ := .S (.S .Z))
    ·
    (.P_Zero .Z |> .P_Succ |> .P_Succ)) |>
  (.T_Succ (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S .Z)) (n₄ := .S (.S (.S (.S .Z))))
    ·
    (.P_Zero (.S (.S .Z)) |> .P_Succ |> .P_Succ))

/--
練習問題1.2 (1) 判断"${\tt SSSZ}$ plus ${\tt SZ}$ is ${\tt SSSSZ}$"の導出
-/
def exercise_1_2_1 : Derivation (.Plus (.S (.S (.S .Z))) (.S .Z) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S .Z) |> .P_Succ |> .P_Succ |> .P_Succ

/--
練習問題1.2 (2) 判断"${\tt SZ}$ plus ${\tt SSSZ}$ is ${\tt SSSSZ}$"の導出
-/
def exercise_1_2_2 : Derivation (.Plus (.S .Z) (.S (.S (.S .Z))) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S (.S (.S .Z))) |> .P_Succ

/--
練習問題1.2 (3) 判断"${\tt SSSZ}$ times ${\tt Z}$ is ${\tt Z}$"の導出
-/
def exercise_1_2_3 : Derivation (.Times (.S (.S (.S .Z))) .Z .Z) :=
  .T_Zero .Z |>
  (.T_Succ · (.P_Zero .Z)) |>
  (.T_Succ · (.P_Zero .Z)) |>
  (.T_Succ · (.P_Zero .Z))

/--
`steps`は判断`judge`の導出システムNatでの導出を受け取ってそのステップ数を返す。
-/
def Derivation.steps {judge : Judgement} : Derivation judge → Nat
  | .P_Zero _     => 1
  | .P_Succ h     => 1 + h.steps
  | .T_Zero _     => 1
  | .T_Succ ht hp => 1 + hp.steps + ht.steps

section
open Derivation
example : steps SSZ_plus_SSSZ = 3 := rfl
example : steps SSZ_times_SSZ = 9 := rfl
example : steps exercise_1_2_1 = 4 := rfl
example : steps exercise_1_2_2 = 2 := rfl
example : steps exercise_1_2_3 = 7 := rfl
end

namespace Derivation
theorem steps_P_Zero (n : PNat)
  : steps (.P_Zero n) = 1 := rfl
theorem steps_P_Succ {n₁ n₂ n₃ : PNat} (h : Derivation (.Plus n₁ n₂ n₃))
  : steps (.P_Succ h) = 1 + h.steps := rfl

theorem steps_T_Zero (n : PNat)
  : steps (.T_Zero n) = 1 := rfl
theorem steps_T_Succ {n₁ n₂ n₃ n₄ : PNat} (ht : Derivation (.Times n₁ n₂ n₃)) (hp : Derivation (.Plus n₂ n₃ n₄))
  : steps (.T_Succ ht hp) = 1 + hp.steps + ht.steps := rfl

/--
任意のペアノ自然数$n_1,n_2,n_3$に対して、導出システムNatによって導出される判断"$n_1$ plus $n_2$ is $n_3$"は$n_1 + 1$ステップで導出できる。
-/
theorem steps_plus {n₁ n₂ n₃ : PNat} : (h : Derivation (.Plus n₁ n₂ n₃)) → steps h = n₁ + 1
  | .P_Zero _ => rfl
  | .P_Succ (n₁ := n₁) h => show steps (P_Succ h) = n₁.S + 1 from
      calc _
        _ = 1 + steps h := steps_P_Succ h
        _ = 1 + n₁.S    := congrArg _ (steps_plus h)
        _ = n₁.S + 1    := Nat.add_comm ..

/--
任意のペアノ自然数$n_1,n_2,n_3$に対して、導出システムNatによって導出される判断"$n_1$ times $n_2$ is $n_3$"は$n_1 \times (n_2 + 2) + 1$ステップで導出できる。
$$\because \text{T_Zero} + \text{T_Succ} + n_1 \times (\text{T_Succ}の前提) = 1 + n_1 + n_1 \times (n_2 + 1)$$
-/
theorem steps_times {n₁ n₂ n₃ : PNat} : (h : Derivation (.Times n₁ n₂ n₃)) → steps h = n₁ * (n₂ + 2) + 1
  | .T_Zero n => Nat.zero_mul _ ▸ steps_T_Zero n
  | .T_Succ (n₁ := n₁) (n₃ := n₃') ht hp =>
      calc _
        _ = 1 + steps hp + steps ht      := steps_T_Succ ht hp
        _ = 1 + (n₂ + 1) + steps ht      := congrArg (_ + · + _) (steps_plus hp)
        _ = n₂ + 2 + steps ht            := congrArg (· + _) (Nat.add_left_comm ..)
        _ = n₂ + 2 + (n₁ * (n₂ + 2) + 1) := congrArg _ (steps_times ht)
        _ = n₂ + 2 + n₁ * (n₂ + 2) + 1   := (Nat.add_assoc ..).symm
        _ = n₁ * (n₂ + 2) + (n₂ + 2) + 1 := congrArg (· + 1) (Nat.add_comm ..)
        _ = (n₁ + 1) * (n₂ + 2) + 1      := congrArg (· + 1) (Nat.succ_mul ..).symm
