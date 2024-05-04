import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement)

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

/-!
"Z plus SSSSSZ is SSSSSZ"は規則P_Zeroで$\MV{n} = \TT{SSSSSZ}$とすれば導ける。
-/
example : Derivation (.Plus .Z (.S (.S (.S (.S (.S (.Z)))))) (.S (.S (.S (.S (.S (.Z))))))) :=
  .P_Zero (n := .S (.S (.S (.S (.S (.Z))))))

/--
任意のペアノ自然数$\MV{n}$に対して、規則P_Zeroを1回用いて判断"$\TT{Z plus $\MV{n}$ is $\MV{n}$}$"を導ける。
-/
def Derivation.Z_plus (n : PNat) : Derivation (.Plus .Z n n) :=
  .P_Zero n

/--
任意のペアノ自然数$\MV{n_1}, \MV{n_2}, \MV{n_3}$に対して、判断"$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"の導出から規則P_Succを1回用いて"$\TT{S$\MV{n_1}$ plus $\MV{n_2}$ is S$\MV{n_3}$}$"を導ける。
-/
def Derivation.S_plus {n₁ n₂ n₃ : PNat} : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁.S n₂ n₃.S) :=
  @Derivation.P_Succ n₁ n₂ n₃

/--
判断"SSZ plus SSSZ is SSSSSZ"の導出
1. 規則P_Zeroで$\MV{n} = \TT{SSSZ}$として"Z plus SSSZ is SSSZ"
2. 規則P_Succで$\MV{n_1} = \TT{Z}, \MV{n_2} = \TT{SSSZ}, \MV{n_3} = \TT{SSSZ}$として、前提は1.で導かれているから"SZ plus SSSZ is SSSSZ"
3. 規則P_Succで$\MV{n_1} = \TT{SZ}, \MV{n_2} = \TT{SSSZ}, \MV{n_3} = \TT{SSSSZ}$として、前提は2.で導かれているから"SSZ plus SSSZ is SSSSSZ"
-/
def SSZ_plus_SSSZ : Derivation (.Plus (.S (.S .Z)) (.S (.S (.S .Z))) (.S (.S (.S (.S (.S .Z)))))) :=
  -- Step 1
  .P_Zero (.S (.S (.S .Z))) |>
  -- Step 2
  .P_Succ (n₁ := .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S .Z))) |>
  -- Step 3
  .P_Succ (n₁ := .S .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))

/--
判断"SSZ times SSZ is SSSSZ"の導出
1. 規則T_Zeroから"Z times SSZ is Z"
2. 規則T_Succから"SZ times SSZ is SSZ"
    - ここで規則P_ZeroとP_Succから"SSZ plus Z is SSZ"を導出してもう一つの前提に使う
3. 規則T_Succから"SSZ times SSZ is SSSSZ"
    - 同様にして"SSZ plus Z is SSZ"をもう一つの前提に使う
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
練習問題1.2 (1) 判断"SSSZ plus SZ is SSSSZ"の導出
-/
def exercise_1_2_1 : Derivation (.Plus (.S (.S (.S .Z))) (.S .Z) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S .Z) |> .P_Succ |> .P_Succ |> .P_Succ

/--
練習問題1.2 (2) 判断"SZ plus SSSZ is SSSSZ"の導出
-/
def exercise_1_2_2 : Derivation (.Plus (.S .Z) (.S (.S (.S .Z))) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S (.S (.S .Z))) |> .P_Succ

/--
練習問題1.2 (3) 判断"SSSZ times Z is Z"の導出
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
任意のペアノ自然数$\MV{n_1},\MV{n_2},\MV{n_3}$に対して、導出システムNatによって導出される判断"$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"は$n_1 + 1$ステップで導出できる。
-/
theorem steps_plus {n₁ n₂ n₃ : PNat} : (h : Derivation (.Plus n₁ n₂ n₃)) → steps h = n₁ + 1
  | .P_Zero _ => rfl
  | .P_Succ (n₁ := n₁) h => show steps (P_Succ h) = n₁.S + 1 from
      calc _
        _ = 1 + steps h := steps_P_Succ h
        _ = 1 + n₁.S    := congrArg _ (steps_plus h)
        _ = n₁.S + 1    := Nat.add_comm ..

/--
任意のペアノ自然数$\MV{n_1},\MV{n_2},\MV{n_3}$に対して、導出システムNatによって導出される判断"$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"は$n_1 \times (n_2 + 2) + 1$ステップで導出できる。
$$\because (\text{T_Zero}) + (\text{T_Succ}) + n_1 \times (\text{T_Succの前提}) = 1 + n_1 + n_1 \times (n_2 + 1)$$
-/
theorem steps_times {n₁ n₂ n₃ : PNat} : (h : Derivation (.Times n₁ n₂ n₃)) → steps h = n₁ * (n₂ + 2) + 1
  | .T_Zero n => Nat.zero_mul _ ▸ steps_T_Zero n
  | .T_Succ (n₁ := n₁) ht hp =>
      calc _
        _ = 1 + steps hp + steps ht      := steps_T_Succ ht hp
        _ = 1 + (n₂ + 1) + steps ht      := congrArg (_ + · + _) (steps_plus hp)
        _ = n₂ + 2 + steps ht            := congrArg (· + _) (Nat.add_left_comm ..)
        _ = n₂ + 2 + (n₁ * (n₂ + 2) + 1) := congrArg _ (steps_times ht)
        _ = n₂ + 2 + n₁ * (n₂ + 2) + 1   := (Nat.add_assoc ..).symm
        _ = n₁ * (n₂ + 2) + (n₂ + 2) + 1 := congrArg (· + 1) (Nat.add_comm ..)
        _ = (n₁ + 1) * (n₂ + 2) + 1      := congrArg (· + 1) (Nat.succ_mul ..).symm

end Derivation

/--
与えられた判断が導出できるという命題
-/
inductive Derivable (judge : Judgement) : Prop where
  | intro (h : Derivation judge)

/--
導出の項が構築できたときは明らかに導出できるので型強制する
-/
instance : Coe (Derivation judge) (Derivable judge) where
  coe h := ⟨h⟩

namespace Derivation
/-
theorem plus_Z : ∀ n : PNat, Derivable (.Plus n .Z n) :=
  -- ペアノ自然数`n`に関する（構造）帰納法で示す
  fun n => PNat.recOn n
    -- `n ≡ Z`のとき"Z plus Z is Z"を示す
    (Derivation.P_Zero .Z)
    -- `n`で成立（`plus_Z n` ≡ "n plus Z is n"）を仮定して"Sn plus Z is Sn"を示す
    (fun n ⟨𝒟⟩ => Derivation.P_Succ (n₁ := n) 𝒟)
-/

def plus_Z : (n : PNat) → Derivation (.Plus n .Z n)
  -- `n ≡ Z`のとき"Z plus Z is Z"を示す
  | .Z => Derivation.P_Zero .Z
  -- `n`で成立（`plus_Z n` ≡ "n plus Z is n"）を仮定して"Sn plus Z is Sn"を示す
  | .S n => Derivation.P_Succ (n₁ := n) (plus_Z n)

/--
ペアノ自然数$\MV{n_1},\MV{n_2}$に対する加算の判断が
$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$と$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_4}$}$の2通り得られたとすると、
$\MV{n_3} \equiv \MV{n_4}$
-/
theorem plus_uniq {n₁ n₂ n₃ n₄ : PNat} : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂ n₄) → n₃ = n₄
  | .P_Zero _,  .P_Zero _  => rfl
  | .P_Succ ha, .P_Succ hb => congrArg PNat.S (plus_uniq ha hb)

/-
逆のn₃ = n₄だったら...を書こうと思うと引数もPropにしたくなったが、
それは自明だし、引数がPropでなければならないというわけでもなかった。

theorem thm_2_2' {n₁ n₂ n₃ n₄ : PNat} : Derivable (.Plus n₁ n₂ n₃) → Derivable (.Plus n₁ n₂ n₄) → n₃ = n₄ :=
  fun ⟨h₁⟩ ⟨h₂⟩ => thm_2_2 h₁ h₂
    -- match h₁, h₂ with
    --   | .P_Zero _,  .P_Zero _  => rfl
    --   | .P_Succ ha, .P_Succ hb => congrArg PNat.S (thm_2_2' ⟨ha⟩ ⟨hb⟩)

theorem thm_2_2'' {n₁ n₂ n₃ n₄ : PNat} : Derivable (.Plus n₁ n₂ n₃) → Derivable (.Plus n₁ n₂ n₄) → n₃ = n₄
  | ⟨h₁⟩, ⟨h₂⟩ => thm_2_2 h₁ h₂
-/

/--
$$\forall \MV{n_1}, \MV{n_2}. \exists \MV{n_3}. \TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$$
-/
theorem derive_plus : ∀ n₁ n₂ : PNat, ∃ n₃ : PNat, Derivable (.Plus n₁ n₂ n₃)
  | .Z,   k => Exists.intro k (Derivation.Z_plus k)
  | .S n, k =>
      have ⟨«n+k», ⟨h⟩⟩ := derive_plus n k
      Exists.intro «n+k».S (Derivation.P_Succ h)

def plus_S {n₁ n₂ n₃ : PNat} : Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂.S n₃.S)
  | .P_Zero n₂ => Derivation.P_Zero n₂.S
  | .P_Succ 𝒟  => Derivation.P_Succ 𝒟.plus_S

/--
加算の交換則
-/
def plus_comm {n₂ n₃ : PNat} : ∀ {n₁ : PNat}, Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₂ n₁ n₃)
  | .Z,   .P_Zero n => plus_Z n
  | .S _, .P_Succ 𝒟 => plus_S 𝒟.plus_comm
-- 等式コンパイラに頼らない書き方（PNat.recOnするやり方？）がわからない
-- n₁に依存してDerivation ...の項が決まるのが難しさ？

/--
加算の結合則$(n_1 + n_2) + n_3 \to n_1 + (n_2 + n_3)$
-/
theorem plus_assoc_right {n₂ n₃ «n₁+n₂» «n₁+n₂+n₃» : PNat} : ∀ {n₁ : PNat}, Derivation (.Plus n₁ n₂ «n₁+n₂») → Derivation (.Plus «n₁+n₂» n₃ «n₁+n₂+n₃») → ∃ «n₂+n₃» : PNat, Derivable (.Plus n₂ n₃ «n₂+n₃») ∧ Derivable (.Plus n₁ «n₂+n₃» «n₁+n₂+n₃»)
  | .Z, .P_Zero n₂, h₂ =>
      Exists.intro «n₁+n₂+n₃» ⟨h₂, Derivation.P_Zero «n₁+n₂+n₃»⟩
  | .S _, .P_Succ h₁, .P_Succ h₂ =>
      have ⟨«n₂+n₃», ⟨ha, ⟨hb⟩⟩⟩ := plus_assoc_right h₁ h₂
      Exists.intro «n₂+n₃» ⟨ha, Derivation.P_Succ hb⟩

/--
加算の結合則$ n_1 + (n_2 + n_3) \to (n_1 + n_2) + n_3$
-/
theorem plus_assoc_left : {n₁ : PNat} → Derivation (.Plus n₁ «n₂+n₃» «n₁+n₂+n₃») → Derivation (.Plus n₂ n₃ «n₂+n₃») → ∃ «n₁+n₂» : PNat, Derivable (.Plus n₁ n₂ «n₁+n₂») ∧ Derivable (.Plus «n₁+n₂» n₃ «n₁+n₂+n₃»)
  | .Z, .P_Zero «n₂+n₃», h₂ =>
      Exists.intro n₂ ⟨Derivation.P_Zero n₂, h₂⟩
  | .S _, .P_Succ h₁, h₂ =>
      have ⟨«n₁'+n₂», ⟨ha⟩, ⟨hb⟩⟩ := plus_assoc_left h₁ h₂
      Exists.intro «n₁'+n₂».S ⟨Derivation.P_Succ ha, Derivation.P_Succ hb⟩

/--
ペアノ自然数$\MV{n_1},\MV{n_2}$に対する乗算の判断が
$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$と$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_4}$}$の2通り得られたとすると、
$\MV{n_3} \equiv \MV{n_4}$
-/
theorem times_uniq {n₂ n₃ n₄ : PNat} : {n₁ : PNat} → Derivation (.Times n₁ n₂ n₃) → Derivation (.Times n₁ n₂ n₄) → n₃ = n₄
  | .Z,   .T_Zero _,               .T_Zero _               => rfl
  | .S _, .T_Succ (n₃ := k) ha hb, .T_Succ (n₃ := l) hc hd =>
      -- hb : Derivation (Judgement.Plus n₂ k n₃)
      -- hd : Derivation (Judgement.Plus n₂ l n₄)
      have : k = l := times_uniq ha hc
      plus_uniq (this ▸ hb) hd

/--
$$\forall \MV{n_1}, \MV{n_2}. \exists \MV{n_3}. \TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$$
-/
theorem derive_times : (n₁ n₂ : PNat) → ∃ n₃ : PNat, Derivable (.Times n₁ n₂ n₃)
  | .Z,   k => Exists.intro .Z (Derivation.T_Zero k)
  | .S n, k =>
      have ⟨«n*k», ⟨h⟩⟩ := derive_times n k
      match h with
        | .T_Zero _ =>
            Exists.intro k (Derivation.T_Succ (.T_Zero k) (Derivation.plus_Z k))
        | .T_Succ ht hp =>
            have ⟨«k+n*k», ⟨h⟩⟩ := derive_plus k «n*k»
            Exists.intro «k+n*k» (Derivation.T_Succ (Derivation.T_Succ ht hp) h)

def Z_times (n : PNat) : Derivation (.Times .Z n .Z) := Derivation.T_Zero n

def times_Z : (n : PNat) → Derivation (.Times n .Z .Z)
  | .Z   => Derivation.T_Zero .Z
  | .S n => Derivation.T_Succ (times_Z n) (.P_Zero .Z)

/--
$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$の導出から、
$\TT{S$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_4}$}$と
$\TT{$\MV{n_3}$ plus $\MV{n_2}$ is $\MV{n_4}$}$の導出を得る。
$(n_1 + 1) \times n_2 = n_1 \times n_2 + n_2$
-/
theorem S_times : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → ∃ «Sn₁*n₂», Derivable (.Times n₁.S n₂ «Sn₁*n₂») ∧ Derivable (.Plus «n₁*n₂» n₂ «Sn₁*n₂»)
  | .Z, .T_Zero n₂ =>
      have 𝒟p := Derivation.plus_Z n₂
      have 𝒟' := Derivation.T_Succ (.T_Zero n₂) 𝒟p
      Exists.intro n₂ ⟨𝒟', 𝒟p.plus_comm⟩
  | .S _, .T_Succ 𝒟t' 𝒟p' =>
      have ⟨«Sn₁*n₂», ⟨𝒟p⟩⟩ := derive_plus n₂ «n₁*n₂»
      have 𝒟' := Derivation.T_Succ (.T_Succ 𝒟t' 𝒟p') 𝒟p
      Exists.intro «Sn₁*n₂» ⟨𝒟', 𝒟p.plus_comm⟩

/--
$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$の導出から、
$\TT{$\MV{n_1}$ times S$\MV{n_2}$ is $\MV{n_4}$}$と
$\TT{$\MV{n_3}$ plus $\MV{n_1}$ is $\MV{n_4}$}$の導出を得る。
$n_1 \times (n_2 + 1) = n_1 \times n_2 + n_1$
-/
theorem times_S : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → ∃ «n₁*Sn₂» : PNat, Derivable (.Times n₁ n₂.S «n₁*Sn₂») ∧ Derivable (.Plus «n₁*n₂» n₁ «n₁*Sn₂»)
  | .Z, .T_Zero n =>
      Exists.intro .Z ⟨Derivation.T_Zero n.S, Derivation.P_Zero .Z⟩
  | .S n₁', .T_Succ ht hp =>
      -- `n₁'*n₂ + n₁'`
      have ⟨«n₁'*Sn₂», ⟨𝒟⟩, ⟨dp⟩⟩ := times_S (n₁ := n₁') ht
      -- `(n₁'*n₂ + n₁') + n₂`
      have ⟨«n₁'*Sn₂+n₂», ⟨𝒟p'⟩⟩ := derive_plus «n₁'*Sn₂» n₂
      -- = `n₁'*n₂ + (n₁' + n₂)`
      have ⟨_, ⟨d₁⟩, ⟨d₂⟩⟩ := plus_assoc_right dp 𝒟p'
      -- = `n₁'*n₂ + (n₂ + n₁')` = `(n₁'*n₂ + n₂) + n₁'`
      have ⟨_, ⟨d₃⟩, ⟨d₄⟩⟩ := plus_assoc_left d₂ d₁.plus_comm
      -- = `(n₁'*n₂ + n₂) + Sn₁'`
      have d := d₄.plus_S

      have heq := plus_uniq hp d₃.plus_comm
      Exists.intro (PNat.S «n₁'*Sn₂+n₂») ⟨Derivation.T_Succ 𝒟 (.P_Succ 𝒟p'.plus_comm), heq ▸ d⟩

/--
乗法の交換則
-/
theorem times_comm : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → Derivable (.Times n₂ n₁ «n₁*n₂»)
  | .Z, .T_Zero _ =>
      Derivation.times_Z n₂
  | .S _, .T_Succ 𝒟t 𝒟p => -- 𝒟t : `n₁' times n₂ is n₁'*n₂`, 𝒟p : `n₂ plus n₁'*n₂ is n₁*n₂`
      -- `n₂ times n₁' is n₁'*n₂`
      have ⟨𝒟t⟩ := times_comm 𝒟t
      -- `n₂ times n₁ is n₁*n₂`
      have ⟨_, ⟨d₁⟩, ⟨d₂⟩⟩ := times_S 𝒟t
      -- d₁ : `n₂ times n₁ is n₁*n₂`
      -- d₂ : `n₁'*n₂ plus n₂ is n₁*n₂`
      have heq := plus_uniq 𝒟p d₂.plus_comm
      heq ▸ d₁
/-
これはDerivableをDerivationに変えるとtimes_Sがこうなって死ぬ：
```
tactic 'cases' failed, nested error:
tactic 'induction' failed, recursor 'Exists.casesOn' can only eliminate into Prop

n₂ «n₁*n₂» n✝ n₃✝ : PNat
motive : (∃ «n₁*Sn₂», Derivable (Judgement.Times n₂ (PNat.S n✝) «n₁*Sn₂») ∧ Derivable (Judgement.Plus n₃✝ n₂ «n₁*Sn₂»)) →
  Sort ?u.23945
h_1 : (w : PNat) →
  (d₁ : Derivation (Judgement.Times n₂ (PNat.S n✝) w)) → (d₂ : Derivation (Judgement.Plus n₃✝ n₂ w)) → motive ⋯
x✝ : ∃ «n₁*Sn₂», Derivable (Judgement.Times n₂ (PNat.S n✝) «n₁*Sn₂») ∧ Derivable (Judgement.Plus n₃✝ n₂ «n₁*Sn₂»)
⊢ motive x✝
 after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
-/
