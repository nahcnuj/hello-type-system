import HelloTypeSystem.Basic

namespace HelloTypeSystem.PeanoNat

/-!
# 自然数の加算・乗算

## 導出システムNatによる導出の例
-/

/--
"Z plus SSSSSZ is SSSSSZ"は規則P_Zeroで$\MV{n} = \TT{SSSSSZ}$とすれば導ける。
-/
def Z_plus_SSSSSZ : Derivation (.Plus .Z (.S (.S (.S (.S (.S (.Z)))))) (.S (.S (.S (.S (.S (.Z))))))) :=
  .P_Zero (n := .S (.S (.S (.S (.S (.Z))))))

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

/-!
### 練習問題1.2 [基礎概念,§1.1]
定義の項がそのまま導出木を表すので練習問題1.4 \[基礎概念,§1.2]の解にもなっている。

#### (1) `SSSZ plus SZ is SSSSZ`
-/
def SSSZ_plus_SZ : Derivation (.Plus (.S (.S (.S .Z))) (.S .Z) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S .Z) |> .P_Succ |> .P_Succ |> .P_Succ

/-!
#### (2) `SZ plus SSSZ is SSSSZ`
-/
def SZ_plus_SSSZ : Derivation (.Plus (.S .Z) (.S (.S (.S .Z))) (.S (.S (.S (.S .Z))))) :=
  .P_Zero (.S (.S (.S .Z))) |> .P_Succ

/-!
#### (3) `SSSZ times Z is Z`
-/
def SSSZ_times_Z : Derivation (.Times (.S (.S (.S .Z))) .Z .Z) :=
  .T_Zero .Z |>
  (.T_Succ · (.P_Zero .Z)) |>
  (.T_Succ · (.P_Zero .Z)) |>
  (.T_Succ · (.P_Zero .Z))

/-!
## 導出のステップ数

### 練習問題1.3 [基礎概念,§1.1]
-/
/--
`steps`は判断𝒥の導出システムNatでの導出𝒟を受け取ってそのステップ数を返す。
-/
def Derivation.steps {judge : Judgement} : Derivation judge → Nat
  | .P_Zero _     => 1
  | .P_Succ h     => 1 + h.steps
  | .T_Zero _     => 1
  | .T_Succ ht hp => 1 + hp.steps + ht.steps

example : SSZ_plus_SSSZ.steps = 3 := rfl
example : SSZ_times_SSZ.steps = 9 := rfl
example : SSSZ_plus_SZ.steps = 4 := rfl
example : SZ_plus_SSSZ.steps = 2 := rfl
example : SSSZ_times_Z.steps = 7 := rfl

namespace Derivation
/--
任意のペアノ自然数$\MV{n_1},\MV{n_2},\MV{n_3}$に対して、導出システムNatによって導出される判断"$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"は$n_1 + 1$ステップで導出できる。
-/
theorem steps_plus {n₁ n₂ n₃ : PNat} : (h : Derivation (.Plus n₁ n₂ n₃)) → h.steps = n₁ + 1
  | .P_Zero _            => rfl
  | .P_Succ (n₁ := n₁) h => show Derivation.steps (.P_Succ h) = n₁.S + 1 from
      calc _
        _ = 1 + h.steps := rfl
        _ = 1 + n₁.S    := congrArg _ (steps_plus h)
        _ = n₁.S + 1    := Nat.add_comm ..

/--
任意のペアノ自然数$\MV{n_1},\MV{n_2},\MV{n_3}$に対して、導出システムNatによって導出される判断"$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"は$n_1 \times (n_2 + 2) + 1$ステップで導出できる。
$$\because (\text{T_Zero}) + (\text{T_Succ}) + n_1 \times (\text{T_Succの前提}) = 1 + n_1 + n_1 \times (n_2 + 1).$$
-/
theorem steps_times {n₁ n₂ n₃ : PNat} : (h : Derivation (.Times n₁ n₂ n₃)) → h.steps = n₁ * (n₂ + 2) + 1
  | .T_Zero n                => Nat.zero_mul _ ▸ rfl
  | .T_Succ (n₁ := n₁) ht hp =>
      calc _
        _ = 1 + hp.steps + ht.steps      := rfl
        _ = 1 + (n₂ + 1) + ht.steps      := congrArg (_ + · + _) (steps_plus hp)
        _ = n₂ + 2 + ht.steps            := congrArg (· + _) (Nat.add_left_comm ..)
        _ = n₂ + 2 + (n₁ * (n₂ + 2) + 1) := congrArg _ (steps_times ht)
        _ = n₂ + 2 + n₁ * (n₂ + 2) + 1   := (Nat.add_assoc ..).symm
        _ = n₁ * (n₂ + 2) + (n₂ + 2) + 1 := congrArg (· + 1) (Nat.add_comm ..)
        _ = (n₁ + 1) * (n₂ + 2) + 1      := congrArg (· + 1) (Nat.succ_mul ..).symm
end Derivation

/-!
## 導出システムNatに関するメタ定理

### 定理2.1 [基礎概念,§2.3]
-/

def Z_plus (n : PNat) : Derivation (.Plus .Z n n) :=
  .P_Zero n

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

/-!
### 定理2.2 [基礎概念,§2.3]
-/

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

/-!
### 練習問題2.2
-/
def plus_S {n₂ n₃ : PNat} : {n₁ : PNat} → Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₁ n₂.S n₃.S)
  | .Z,   .P_Zero n₂ => Derivation.P_Zero n₂.S
  | .S _, .P_Succ 𝒟  => Derivation.P_Succ (plus_S 𝒟)

/-!
### 定理2.4 [基礎概念,§2.3]
-/

/--
加算の交換則
-/
def plus_comm {n₂ n₃ : PNat} : ∀ {n₁ : PNat}, Derivation (.Plus n₁ n₂ n₃) → Derivation (.Plus n₂ n₁ n₃)
  | .Z,   .P_Zero n => plus_Z n
  | .S _, .P_Succ 𝒟 => plus_S <| plus_comm 𝒟
-- 等式コンパイラに頼らない書き方（PNat.recOnするやり方？）がわからない
-- n₁に依存してDerivation ...の項が決まるのが難しさ？

/-!
### 練習問題2.3 [基礎概念,§2.3]
各定理の主張は§2.1にある。

#### 定理2.3
-/
/--
$$\forall \MV{n_1}, \MV{n_2}. \exists \MV{n_3}. \TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$$
-/
theorem derive_plus : ∀ n₁ n₂ : PNat, ∃ n₃ : PNat, Derivable (.Plus n₁ n₂ n₃)
  | .Z,   k => Exists.intro k (Derivation.P_Zero k)
  | .S n, k =>
      have ⟨«n+k», ⟨h⟩⟩ := derive_plus n k
      Exists.intro «n+k».S (Derivation.P_Succ h)

/-!
#### 定理2.5
-/
/--
加算の結合則：$(n_1 + n_2) + n_3 \to n_1 + (n_2 + n_3)$
-/
theorem plus_assoc_right {n₂ n₃ «n₁+n₂» «n₁+n₂+n₃» : PNat} : ∀ {n₁ : PNat}, Derivation (.Plus n₁ n₂ «n₁+n₂») → Derivation (.Plus «n₁+n₂» n₃ «n₁+n₂+n₃») → ∃ «n₂+n₃» : PNat, Derivable (.Plus n₂ n₃ «n₂+n₃») ∧ Derivable (.Plus n₁ «n₂+n₃» «n₁+n₂+n₃»)
  | .Z, .P_Zero n₂, h₂ =>
      Exists.intro «n₁+n₂+n₃» ⟨h₂, Derivation.P_Zero «n₁+n₂+n₃»⟩
  | .S _, .P_Succ h₁, .P_Succ h₂ =>
      have ⟨«n₂+n₃», ⟨ha, ⟨hb⟩⟩⟩ := plus_assoc_right h₁ h₂
      Exists.intro «n₂+n₃» ⟨ha, Derivation.P_Succ hb⟩

/--
加算の結合則：$n_1 + (n_2 + n_3) \to (n_1 + n_2) + n_3$
-/
theorem plus_assoc_left : {n₁ : PNat} → Derivation (.Plus n₁ «n₂+n₃» «n₁+n₂+n₃») → Derivation (.Plus n₂ n₃ «n₂+n₃») → ∃ «n₁+n₂» : PNat, Derivable (.Plus n₁ n₂ «n₁+n₂») ∧ Derivable (.Plus «n₁+n₂» n₃ «n₁+n₂+n₃»)
  | .Z, .P_Zero «n₂+n₃», h₂ =>
      Exists.intro n₂ ⟨Derivation.P_Zero n₂, h₂⟩
  | .S _, .P_Succ h₁, h₂ =>
      have ⟨«n₁'+n₂», ⟨ha⟩, ⟨hb⟩⟩ := plus_assoc_left h₁ h₂
      Exists.intro «n₁'+n₂».S ⟨Derivation.P_Succ ha, Derivation.P_Succ hb⟩

/-!
#### 定理2.6
-/
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

/-!
#### 定理2.7
-/
/--
$$\forall \MV{n_1}, \MV{n_2}. \exists \MV{n_3}. \TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$$
-/
theorem derive_times : (n₁ n₂ : PNat) → ∃ n₃ : PNat, Derivable (.Times n₁ n₂ n₃)
  | .Z,   k => Exists.intro .Z (Derivation.T_Zero k)
  | .S n, k =>
      have ⟨«n*k», ⟨h⟩⟩ := derive_times n k
      match h with
        | .T_Zero _ =>
            Exists.intro k (Derivation.T_Succ (.T_Zero k) (plus_Z k))
        | .T_Succ ht hp =>
            have ⟨«k+n*k», ⟨h⟩⟩ := derive_plus k «n*k»
            Exists.intro «k+n*k» (Derivation.T_Succ (Derivation.T_Succ ht hp) h)

/-!
#### 定理2.8
-/

def Z_times (n : PNat) : Derivation (.Times .Z n .Z) := Derivation.T_Zero n

def times_Z : (n : PNat) → Derivation (.Times n .Z .Z)
  | .Z   => Derivation.T_Zero .Z
  | .S n => Derivation.T_Succ (times_Z n) (.P_Zero .Z)

/--
$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$の導出から、
$\TT{$\MV{n_1}$ times S$\MV{n_2}$ is $\MV{n_4}$}$と
$\TT{$\MV{n_3}$ plus $\MV{n_1}$ is $\MV{n_4}$}$の導出を得る。
$n_1 \times (n_2 + 1) = n_1 \times n_2 + n_1$
-/
theorem times_S : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → ∃ «n₁*Sn₂» : PNat, Derivable (.Times n₁ n₂.S «n₁*Sn₂») ∧ Derivable (.Plus «n₁*n₂» n₁ «n₁*Sn₂»)
  | .Z, .T_Zero n₂ =>
      Exists.intro .Z ⟨Derivation.T_Zero n₂.S, Derivation.P_Zero .Z⟩
  | .S n₁', .T_Succ ht hp =>
      -- `n₁'*n₂ + n₁'`
      have ⟨«n₁'*Sn₂», ⟨𝒟⟩, ⟨dp⟩⟩ := times_S (n₁ := n₁') ht
      -- `(n₁'*n₂ + n₁') + n₂`
      have ⟨«n₁'*Sn₂+n₂», ⟨𝒟p'⟩⟩ := derive_plus «n₁'*Sn₂» n₂
      -- = `n₁'*n₂ + (n₁' + n₂)`
      have ⟨_, ⟨d₁⟩, ⟨d₂⟩⟩ := plus_assoc_right dp 𝒟p'
      -- = `n₁'*n₂ + (n₂ + n₁')` = `(n₁'*n₂ + n₂) + n₁'`
      have ⟨_, ⟨d₃⟩, ⟨d₄⟩⟩ := plus_assoc_left d₂ (plus_comm d₁)
      -- = `(n₁'*n₂ + n₂) + Sn₁'`
      have d := plus_S d₄

      have heq := plus_uniq hp (plus_comm d₃)
      Exists.intro (PNat.S «n₁'*Sn₂+n₂») ⟨Derivation.T_Succ 𝒟 (.P_Succ <| plus_comm 𝒟p'), heq ▸ d⟩

/-!
#### 定理2.9
-/
/--
乗法の交換則
-/
theorem times_comm : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → Derivable (.Times n₂ n₁ «n₁*n₂»)
  | .Z, .T_Zero _ =>
      times_Z n₂
  | .S _, .T_Succ 𝒟t 𝒟p => -- 𝒟t : `n₁' times n₂ is n₁'*n₂`, 𝒟p : `n₂ plus n₁'*n₂ is n₁*n₂`
      -- `n₂ times n₁' is n₁'*n₂`
      have ⟨𝒟t⟩ := times_comm 𝒟t
      -- `n₂ times n₁ is n₁*n₂`
      have ⟨_, ⟨d₁⟩, ⟨d₂⟩⟩ := times_S 𝒟t
      -- d₁ : `n₂ times n₁ is n₁*n₂`
      -- d₂ : `n₁'*n₂ plus n₂ is n₁*n₂`
      have heq := plus_uniq 𝒟p (plus_comm d₂)
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

/-!
#### 定理2.10
証明に必要な補題を幾つか証明したあとに本定理`times_assoc_right`を証明する。

参考：
- [MATHEMATICS\.PDF, 数の構成 自然数から複素数まで](https://mathematics-pdf.com/pdf/construction_of_numbers.pdf)
-/

def of_plus_S {n₂ : PNat} : {n₁ : PNat} → Derivation (.Plus n₁ n₂.S «n₁+n₂+1») → ∃ «n₁+n₂» : PNat, Derivable (.Plus n₁ n₂ «n₁+n₂»)
  | .Z, _ =>
      Exists.intro n₂ (Derivation.P_Zero n₂)
  | .S n₁', _ =>
      have ⟨«n₁'+n₂», ⟨dp⟩⟩ := derive_plus n₁' n₂
      Exists.intro «n₁'+n₂».S (dp.P_Succ)

/--
分配法則：$n_1 \times (n_2 + n_3) \to n_1 \times n_2 + n_1 \times n_3$
-/
theorem left_distrib : {n₃ : PNat} → Derivation (.Plus n₂ n₃ «n₂+n₃») → Derivation (.Times n₁ «n₂+n₃» «n₁*(n₂+n₃)»)
                       → ∃ «n₁*n₂» «n₁*n₃» : PNat, Derivable (.Times n₁ n₂ «n₁*n₂») ∧ Derivable (.Times n₁ n₃ «n₁*n₃») ∧ Derivable (.Plus «n₁*n₂» «n₁*n₃» «n₁*(n₂+n₃)»)
  | .Z, dp, dt =>
      have heq : «n₂+n₃» = n₂ := plus_uniq dp (plus_Z n₂)
      have ⟨«n₁*n₂», ⟨dt'⟩⟩ := derive_times n₁ n₂
      have heq : «n₁*n₂» = «n₁*(n₂+n₃)» := times_uniq dt' (heq ▸ dt)
      Exists.intro «n₁*n₂» <| Exists.intro .Z ⟨dt', times_Z n₁, ⟨heq ▸ plus_Z «n₁*(n₂+n₃)»⟩⟩
  | .S _, dp, dt =>
      have ⟨«n₂+n₃'», ⟨dp'⟩⟩ := of_plus_S dp
      have ⟨«n₁*(n₂+n₃')», ⟨dt'⟩⟩ := derive_times n₁ «n₂+n₃'»
      have ⟨«n₁*n₂», _, ⟨dt12⟩, ⟨dt13'⟩, ⟨dd⟩⟩ := left_distrib dp' dt'
      have ⟨dt13'⟩ := times_comm dt13'
      have ⟨_, ⟨ds⟩⟩ := derive_plus «n₁*(n₂+n₃')» n₁
      have ⟨«n₁*n₃'+n₁», ⟨dt13⟩, ⟨ds'⟩⟩ := plus_assoc_right dd ds
      have ⟨dt13⟩ := Derivation.T_Succ dt13' (plus_comm dt13) |> times_comm
      have heq : «n₂+n₃» = «n₂+n₃'».S := plus_uniq dp (plus_S dp')
      have ⟨dt'⟩ := times_comm dt'
      have ⟨dt'⟩ := heq.symm ▸ Derivation.T_Succ dt' (plus_comm ds) |> times_comm
      have ds' := times_uniq dt dt' ▸ ds'
      Exists.intro «n₁*n₂» (Exists.intro «n₁*n₃'+n₁» ⟨dt12, dt13, ds'⟩)

/--
分配法則：$(n_1 + n_2) \times n_3 \to n_1 \times n_3 + n_2 \times n_3$
-/
theorem right_distrib : Derivation (.Plus n₁ n₂ «n₁+n₂») → Derivation (.Times «n₁+n₂» n₃ «(n₁+n₂)*n₃»)
                        → ∃ «n₁*n₃» «n₂*n₃» : PNat, Derivable (.Times n₁ n₃ «n₁*n₃») ∧ Derivable (.Times n₂ n₃ «n₂*n₃») ∧ Derivable (.Plus «n₁*n₃» «n₂*n₃» «(n₁+n₂)*n₃»)
  | d₁, d₂ =>
      have ⟨d₂⟩ := times_comm d₂
      have ⟨«n₃*n₁», «n₃*n₂», ⟨d31⟩, ⟨d32⟩, dp⟩ := left_distrib d₁ d₂
      have ⟨d13⟩ := times_comm d31
      have ⟨d23⟩ := times_comm d32
      Exists.intro «n₃*n₁» <| Exists.intro «n₃*n₂» ⟨d13, d23, dp⟩

/--
乗算の結合則：$(n_1 \times n_2) \times n_3 \to n_1 \times (n_2 \times n_3)$
-/
theorem times_assoc_right : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → Derivation (.Times «n₁*n₂» n₃ «n₁*n₂*n₃»)
                            → ∃ «n₂*n₃» : PNat, Derivable (.Times n₂ n₃ «n₂*n₃») ∧ Derivable (.Times n₁ «n₂*n₃» «n₁*n₂*n₃»)
  | .Z, .T_Zero _, d₂ =>
      have heq : «n₁*n₂*n₃» = .Z := times_uniq d₂ (Derivation.T_Zero n₃)
      have ⟨«n₂*n₃», d23⟩ := derive_times n₂ n₃
      Exists.intro «n₂*n₃» ⟨d23, heq.symm ▸ Derivation.T_Zero «n₂*n₃»⟩
  | .S _, .T_Succ d₁t d₁p, d₂ =>
      have ⟨«n₂*n₃», _, ⟨dl⟩,⟨dr⟩,⟨dp⟩⟩ := right_distrib d₁p d₂
      have ⟨_, ⟨drl⟩, ⟨drr⟩⟩ := times_assoc_right d₁t dr
      have drr := times_uniq drl dl ▸ drr
      Exists.intro «n₂*n₃» ⟨dl, Derivation.T_Succ drr dp⟩

/-!
以下は証明を組む試行錯誤の中で生まれた定理である。
-/

/--
$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$の導出から、
$\TT{S$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_4}$}$と
$\TT{$\MV{n_3}$ plus $\MV{n_2}$ is $\MV{n_4}$}$の導出を得る。
$(n_1 + 1) \times n_2 = n_1 \times n_2 + n_2$
-/
theorem S_times : {n₁ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → ∃ «Sn₁*n₂», Derivable (.Times n₁.S n₂ «Sn₁*n₂») ∧ Derivable (.Plus «n₁*n₂» n₂ «Sn₁*n₂»)
  | .Z, .T_Zero n₂ =>
      have 𝒟p := plus_Z n₂
      have 𝒟' := Derivation.T_Succ (.T_Zero n₂) 𝒟p
      Exists.intro n₂ ⟨𝒟', plus_comm 𝒟p⟩
  | .S _, .T_Succ 𝒟t' 𝒟p' =>
      have ⟨«Sn₁*n₂», ⟨𝒟p⟩⟩ := derive_plus n₂ «n₁*n₂»
      have 𝒟' := Derivation.T_Succ (.T_Succ 𝒟t' 𝒟p') 𝒟p
      Exists.intro «Sn₁*n₂» ⟨𝒟', plus_comm 𝒟p⟩

theorem S_plus_of_plus_S : {n₁ : PNat} → Derivation (.Plus n₁ n₂.S n₃) → Derivable (.Plus n₁.S n₂ n₃)
  | .Z, d =>
      have := Derivation.P_Zero n₂ |> plus_S
      have heq : n₃ = n₂.S := plus_uniq d this
      heq ▸ Derivation.P_Succ (.P_Zero n₂)
  | .S _, d =>
      have ⟨«n₁+n₂», ⟨d'⟩⟩ := of_plus_S d -- Prop (Derivable)からDerivationを取り出したかったら、Prop (Derivable)にしないといけない？
      have heq : n₃ = «n₁+n₂».S := plus_uniq d (plus_S d')
      heq ▸ Derivation.P_Succ d'

theorem of_times_S : {n₁ : PNat} → Derivation (.Times n₁ n₂.S «n₁*Sn₂») → ∃ «n₁*n₂» : PNat, Derivable (.Times n₁ n₂ «n₁*n₂») ∧ Derivable (.Plus «n₁*n₂» n₁ «n₁*Sn₂»)
  | .Z, d =>
      have heq := times_uniq d (Derivation.T_Zero _)
      Exists.intro .Z ⟨Derivation.T_Zero n₂, heq.symm ▸ Derivation.P_Zero .Z⟩
  | .S _, .T_Succ dt dp =>
      have ⟨_, ⟨dt'⟩, ⟨dp'⟩⟩ := of_times_S dt
      have ⟨«n₁*n₂+1», ⟨d1⟩, ⟨d2⟩⟩ := plus_assoc_right (plus_comm dp') (plus_comm dp)
      have ⟨«n₁*n₂», ⟨dr⟩⟩ := of_plus_S d1
      have heq : «n₁*n₂+1» = «n₁*n₂».S := plus_uniq d1 (plus_S dr)
      have ⟨dl⟩ := S_plus_of_plus_S (heq ▸ d2)
      Exists.intro «n₁*n₂» ⟨Derivation.T_Succ dt' (plus_comm dr), (plus_comm dl)⟩

/--
分配法則の逆：$n_1 \times n_2 + n_1 \times n_3 \to n_1 \times (n_2 + n_3)$
-/
theorem left_distrib_inv : {n₃ : PNat} → Derivation (.Times n₁ n₂ «n₁*n₂») → Derivation (.Times n₁ n₃ «n₁*n₃») → Derivation (.Plus n₂ n₃ «n₂+n₃»)
                          → ∃ «n₁*(n₂+n₃)» : PNat, Derivable (.Times n₁ «n₂+n₃» «n₁*(n₂+n₃)»)
  | .Z, dl, _, dp =>
      have heq : «n₂+n₃» = n₂ := plus_uniq dp (plus_Z n₂)
      Exists.intro «n₁*n₂» (heq ▸ dl)
  | .S _, dl, dr, dp =>
      have ⟨_, ⟨dr1⟩, _⟩ := of_times_S dr
      have ⟨«n₂+n₃'», ⟨dp'⟩⟩ := of_plus_S dp
      have ⟨_, ⟨d⟩⟩ := left_distrib_inv dl dr1 dp'
      have heq : «n₂+n₃» = «n₂+n₃'».S := plus_uniq dp (plus_S dp')
      have ⟨«n₁*(n₂+n₃)», 𝒟, _⟩ := times_S d
      Exists.intro «n₁*(n₂+n₃)» (heq ▸ 𝒟)
