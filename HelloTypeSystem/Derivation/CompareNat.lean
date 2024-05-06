import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement)

namespace HelloTypeSystem

/-!
# 自然数の大小比較
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

private abbrev Derivable := @HelloTypeSystem.Derivable Derivation

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

private abbrev Derivable := @HelloTypeSystem.Derivable Derivation

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

private abbrev Derivable := @HelloTypeSystem.Derivable Derivation

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
## CompareNat1–3による導出の例
### 練習問題1.5 [基礎概念,§1.3]
#### (1) `Z is less than SSZ`
-/
def CompareNat1.Z_lt_SSZ : Derivation (.LT .Z (.S (.S .Z))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S .Z))
    (.LT_Succ (.Z))
    (.LT_Succ (.S .Z))

def CompareNat2.Z_lt_SSZ : Derivation (.LT .Z PNat.Z.S.S) :=
  .LT_Zero PNat.Z.S

def CompareNat3.Z_lt_SSZ : Derivation (.LT .Z PNat.Z.S.S) :=
  .LT_SuccR (n₁ := .Z) (n₂ := PNat.Z.S)
    (.LT_Succ .Z)

/-!
#### (2) `SSZ is less than SSSSZ`
-/
def CompareNat1.SSZ_lt_SSSSZ : Derivation (.LT (.S (.S .Z)) (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .S (.S .Z)) (n₂ := (.S (.S (.S .Z)))) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Succ (.S (.S .Z)))
    (.LT_Succ (.S (.S (.S .Z))))

def CompareNat2.SSZ_lt_SSSSZ : Derivation (.LT PNat.Z.S.S PNat.Z.S.S.S.S) :=
  .LT_SuccSucc (n₁ := PNat.Z.S) (n₂ := PNat.Z.S.S.S)
    (.LT_SuccSucc (n₁ := .Z) (n₂ := PNat.Z.S.S)
      (.LT_Zero PNat.Z.S)
    )

def CompareNat3.SSZ_lt_SSSSZ : Derivation (.LT PNat.Z.S.S PNat.Z.S.S.S.S) :=
  .LT_SuccR (n₁ := PNat.Z.S.S) (n₂ := PNat.Z.S.S.S)
    (.LT_Succ PNat.Z.S.S)

/-!
### 練習問題1.6 [基礎概念,§1.3]

導出システムCompareNat1は判断"$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$"に対して、
規則LT_Transにおける中間の項（`n₂`）の取り方によって異なる導出を与える。
-/

namespace CompareNat1
/-!
例えば判断"Z is less than SSSSZ"に対して、
規則LT_Transにおける$\MV{n_2}$の選び方によって異なる導出木が得られる：
- $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SSSZ}$
- $\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSSZ}$
- $\MV{n_2} = \TT{SSSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$
-/

/-- 規則LT_Transで$\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SSSZ}$として導出する。 -/
example : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Succ .Z)
    (.LT_Trans (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
      (.LT_Succ (.S .Z))
      (.LT_Trans (n₁ := .S (.S .Z)) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))
        (.LT_Succ (.S (.S .Z)))
        (.LT_Succ (.S (.S (.S .Z))))
      )
    )

/-- 規則LT_Transで$\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSSZ}$として導出する。 -/
example : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Trans (n₁ := .Z) (n₃ := .S (.S .Z))
      (.LT_Succ .Z)
      (.LT_Succ (.S .Z))
    )
    (.LT_Trans (n₁ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
      (.LT_Succ (.S (.S .Z)))
      (.LT_Succ (.S (.S (.S .Z))))
    )

/-- 規則LT_Transで$\MV{n_2} = \TT{SSSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$として導出する。 -/
example : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S (.S .Z)))
      (.LT_Succ .Z)
      (.LT_Trans (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S .Z)))
        (.LT_Succ (.S .Z))
        (.LT_Succ (.S (.S .Z)))
      )
    )
    (.LT_Succ (.S (.S (.S .Z))))
end CompareNat1

/-!
一方、導出システムCompareNat2とCompareNat3は、前提に選択の余地がないから導出木の曖昧さは生じない。
-/

/-
TODO: 曖昧でないことは「2つあったら一致する」やつで示せる？
TODO: \[基礎理論,§1.3.2]の曖昧性の定義に従って証明できるか？
-/

/-!
## CompareNat1–3に関するメタ定理
-/
/-!
### 定理2.11 [基礎概念,§2.1]
-/

def CompareNat1.Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | .Z   => .LT_Succ .Z
  | .S n => .LT_Trans (Z_lt_S n) (.LT_Succ n.S)

/-
theorem CompareNat1.Z_lt_S' : (n : PNat) → Derivable (.LT .Z n.S)
  | .Z   => Derivation.LT_Succ .Z
  | .S n =>
      have ⟨𝒟⟩ := Z_lt_S' n
      Derivation.LT_Trans 𝒟 (.LT_Succ n.S)
-/

def CompareNat2.Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | n => .LT_Zero n

def CompareNat3.Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | .Z   => .LT_Succ .Z
  | .S n => .LT_SuccR (Z_lt_S n)

/-!
### 定理2.36 [基礎概念,§2.5]
-/

/--
$\forall\MV{n_1},\MV{n_2}. \bigl[\TT{S$\MV{n_1}$ is less than $\MV{n_2}$} \implies \exists\MV{n_3}. \MV{n_2} \equiv \TT{S$\MV{n_3}$}\bigr]$

$P(\MV{n_1},\MV{n_2})$は以下のように考える：
$$\begin{align*}
& \bigl[\exists\MV{n'_1}. \MV{n_1} \equiv \TT{S$\MV{n'_1}$}] \\\\
& {} \implies \bigl[ \TT{S$\MV{n'_1}$ is less than $\MV{n_2}$} \implies \exists\MV{n'_2}. \MV{n_2}\equiv\TT{S$\MV{n'_2}$} \bigr].
\end{align*}$$
`motive n₁ n₂`は
$$(\bullet,\TT{$\MV{n_2}$}) \mapsto \exists\MV{n'_2}. \MV{n_2}\equiv\TT{S$\MV{n'_2}$}$$
となるように定義する。
-/
theorem CompareNat1.exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
 -- (fun {n₁ n₂ n₃} lt12 lt23 ⟨n₂', h₂'⟩ ⟨n₃', h₃'⟩ =>
    (fun _ _ _ ⟨n₃',h₃'⟩ => Exists.intro n₃' h₃')

theorem CompareNat2.exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
    (fun _ ⟨n₂', h₂'⟩ => Exists.intro n₂'.S (h₂' ▸ rfl))

theorem CompareNat3.exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
    (fun _ ⟨n₂',h₂'⟩ => Exists.intro n₂'.S (h₂' ▸ rfl))

/-!
### 定理2.12 [基礎概念,§2.1]
-/

/--
$P(\MV{n_1},\MV{n_2})$を以下で定義する：
$$\begin{align*}
& \bigl[\exists\MV{n'_1},\MV{n'_2}. \MV{n_1} \equiv \TT{S$\MV{n'_1}$} \land \MV{n_2} \equiv \TT{S$\MV{n'_2}$}\bigr] \\\\
& {} \implies \bigl[ \TT{S$\MV{n'_1}$ is less than S$\MV{n'_2}$} \implies \TT{$\MV{n'_1}$ is less than $\MV{n'_2}$} \bigr].
\end{align*}$$
`motive n₁ n₂`は
$$(\TT{S$\MV{n'_1}$},\TT{S$\MV{n'_2}$}) \mapsto \TT{$\MV{n'_1}$ is less than $\MV{n'_2}$}$$
となるように定義する。
どちらかあるいは両方が`Z`である場合はDon't careで`True`としておく。
（参考：[https://zenn.dev/tnyo43/scraps/afaa5fd8db3992#comment-41aa843ee675d1](https://zenn.dev/tnyo43/scraps/afaa5fd8db3992#comment-41aa843ee675d1)）

`LT_Trans`の場合分け：
- `n₁ = Sn₁'`かつ`n₂ = Sn₂'`かつ`n₃ = Sn₃'` ⇒ 仮定の導出からLT_Trans
- `n₁ = Z`または`n₃ = Z` ⇒ 直ちに`True.intro`
- 上記以外で`n₂ = Z` ⇒ 仮定と導出規則を駆使

最後のパターンで仮定に`Sn₁' is less than Z`のような意味的に偽な判断が出てくるが、
あくまで仮定として`n₁' is less than n₃'`の形を目指す。
-/
theorem CompareNat1.lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
  Derivation.induction
    (motive := fun n₁ n₂ =>
      match n₁,n₂ with
      | .S n₁', .S n₂' => Derivable (.LT n₁' n₂')
      | _,     _       => True -- don't care
    )
    (fun n =>
      match n with
      | .S n => Derivation.LT_Succ n
      | .Z   => True.intro
    )
    (fun {n₁ n₂ n₃} d1 _ h1 h2 =>
      match n₁,n₂,n₃,h1,h2 with
      | .S _,   .S _, .S _,  ⟨d₁⟩, ⟨d₂⟩ => Derivation.LT_Trans d₁ d₂
      | .S n₁', .Z,   .S .Z, _,    _    =>
          Derivation.LT_Trans -- "n₁' < Z"
            (Derivation.LT_Succ n₁') -- n₁' < Sn₁'
            (d1)                     --       Sn₁' < Z
      | .S n₁', .Z, .S (.S n₃'), _, _ =>
          Derivation.LT_Trans -- "n₁' < Sn₃'"
            (Derivation.LT_Succ n₁') --  n₁' < Sn₁'
            (Derivation.LT_Trans     --        Sn₁' < Sn₃'
              d1           -- Sn₁' < Z
              (Z_lt_S n₃') --        Z < Sn₃'
            )
      | .S _, _, .Z, _, _ => True.intro
      | .Z,   _, _,  _, _ => True.intro
    )

theorem CompareNat2.lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
  Derivation.induction
    (motive := fun n₁ n₂ =>
      match n₁,n₂ with
      | .S n₁', .S n₂' => Derivable (.LT n₁' n₂')
      | _,     _       => True -- don't care
    )
    (fun _ => True.intro)
    (fun {n₁ n₂} h1 h2 =>
      match n₁,n₂,h1,h2 with
      | .S _, .S _, _,  ⟨d2⟩ => Derivation.LT_SuccSucc d2
      | .Z,   _,    d1, _    => d1
    )

theorem CompareNat3.lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
  Derivation.induction
    (motive := fun n₁ n₂ =>
      match n₁,n₂ with
      | .S n₁', .S n₂' => Derivable (.LT n₁' n₂')
      | _,     _       => True -- don't care
    )
    (fun n =>
      match n with
      | .Z    => True.intro
      | .S n' => Derivation.LT_Succ n'
    )
    (fun {n₁ n₂} h1 h2 =>
      match n₁,n₂,h1,h2 with
      | .S _, .S _, _, ⟨d2⟩ => Derivation.LT_SuccR d2
      | .Z,   _,    _, _    => True.intro
    )

/-!
### 定理2.13：推移律 [基礎概念,§2.1]
-/

theorem CompareNat1.lt_trans : {n₁ n₂ n₃ : PNat} → Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃) :=
  fun {_ _ n₃} =>
    Derivation.induction (motive := fun n₁ n₂ => Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃))
      (fun n d => Derivation.LT_Trans (Derivation.LT_Succ n) d)
      (fun d1 d2 _ _ d => Derivation.LT_Trans (Derivation.LT_Trans d1 d2) d)

theorem CompareNat2.lt_trans : {n₁ n₂ n₃ : PNat} → Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃) :=
  fun {_ _ n₃} =>
    Derivation.induction (motive := fun n₁ n₂ => Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃))
      (fun _ d23 =>
        match n₃ with
        | .Z     => nomatch d23 -- `Sn is less than Z`
        | .S n₃' => Derivation.LT_Zero n₃'
      )
      (fun d12 _ d23 =>
        match n₃ with
        | .Z   => nomatch d23 -- `Sn₂ is less than Z`
        | .S _ =>
            have ⟨d⟩ := lt_of_S_lt_S d23
            have ⟨d⟩ := lt_trans d12 d
            Derivation.LT_SuccSucc d
      )
/-!
判断`n₁ is less than n₂`の導出に関する帰納法で示す。
$$P(\MV{n_1},\MV{n_2}) := \TT{$\MV{n_2}$ is less than $\MV{n_3}$} \implies \TT{$\MV{n_1}$ is less than $\MV{n_3}$}.$$
$\MV{n_3} \equiv \TT{Z}$のときは前提の判断が導出できない（`nomatch`）ので、
以下$\MV{n_3} \equiv \TT{S$\MV{n'_3}$}$とおく。
`n₁ is less than n₂`の導出によって場合分け：
- `LT_Zero`
  - $\forall\MV{n}. P(\TT{Z},\TT{S$\MV{n}$})$
  - $\TT{S$\MV{n}$ is less than S$\MV{n'_3}$} \implies \TT{Z is less than S$\MV{n'_3}$}$
  - $$
    \dfrac{}{
      \TT{Z is less than S$\MV{n'_3}$}
    }\mathsf{LT\\_Zero}
    $$
- `LT_SuccSucc`
  - $\forall\MV{n_1},\MV{n_2}. \bigl[\text{“$\MV{n_1}<\MV{n_2}$”} \land P(\MV{n_1},\MV{n_2}) \implies P(\TT{S$\MV{n_1}$},\TT{S$\MV{n_2}$})\bigr]$
  - $\TT{S$\MV{n_2}$ is less than S$\MV{n'_3}$} \implies \TT{S$\MV{n_1}$ is less than S$\MV{n'_3}$}$
  - $\mathcal{D}_{12} \in \TT{$\MV{n_1}$ is less than $\MV{n_2}$}$ ∵帰納法の仮定
  - $\mathcal{D}_{23'} \in \TT{$\MV{n_2}$ is less than $\MV{n'_3}$}$ ∵仮定に`lt_of_S_lt_S`を適用
  - $\mathcal{D} \in \TT{$\MV{n\_1}$ is less than $\MV{n'\_3}$}$ ∵`lt_trans` to $\mathcal{D}\_{12}$ and $\mathcal{D}\_{23'}$
  - $$
    \dfrac{
      \mathcal{D} \equiv \dfrac{\vdots}{\TT{$\MV{n_1}$ is less than $\MV{n'_3}$}}
    }{
      \TT{S$\MV{n_1}$ is less than S$\MV{n'_3}$}
    }\mathsf{LT\\_SuccSucc}
    $$
-/

theorem CompareNat3.lt_trans : {n₁ n₂ n₃ : PNat} → Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃) :=
  fun {_ _ n₃} =>
    Derivation.induction (motive := fun n₁ n₂ => Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃))
      (fun _ d23 =>
        match n₃ with
        | .Z   => nomatch d23
        | .S _ =>
            have ⟨𝒟⟩ := lt_of_S_lt_S d23
            Derivation.LT_SuccR 𝒟
      )
      (fun _ h d23 =>
        match n₃ with
        | .Z   => nomatch d23
        | .S _ =>
            have ⟨𝒟₂₃⟩ := lt_of_S_lt_S d23
            h <| 𝒟₂₃.LT_SuccR
      )

/-!
### 定理2.14 [基礎概念,§2.1]
1 ⇒ 2, 2 ⇒ 3, 3 ⇒ 1を示す。
-/
theorem CN2_of_CN1 : CompareNat1.Derivable (.LT n₁ n₂) → CompareNat2.Derivable (.LT n₁ n₂) :=
  fun ⟨d⟩ => d.induction (motive := fun n₁ n₂ => CompareNat2.Derivable (.LT n₁ n₂))
    (PNat.rec
      (CompareNat2.Derivation.LT_Zero .Z)
      (fun _ ⟨d⟩ => CompareNat2.Derivation.LT_SuccSucc d)
    )
    (fun _ _ ⟨d12⟩ ⟨d23⟩ => CompareNat2.lt_trans d12 d23)

theorem CN3_of_CN2 : CompareNat2.Derivable (.LT n₁ n₂) → CompareNat3.Derivable (.LT n₁ n₂) :=
  fun ⟨𝒟₂⟩ => 𝒟₂.induction (motive := fun n₁ n₂ => CompareNat3.Derivable (.LT n₁ n₂))
    (PNat.rec
      (CompareNat3.Derivation.LT_Succ .Z)
      (fun _ ⟨d⟩ => CompareNat3.Derivation.LT_SuccR d)
    )
    (fun {_ n₂} _ ⟨𝒟₃⟩ =>
      match n₂ with
      | .Z   => nomatch 𝒟₃
      | .S _ => 𝒟₃.induction (motive := fun n₁ n₂ => CompareNat3.Derivable (.LT n₁.S n₂.S))
          (fun n => CompareNat3.Derivation.LT_Succ n.S)
          (fun _ ⟨D⟩ => CompareNat3.Derivation.LT_SuccR D)
    )

theorem CN1_of_CN3 : CompareNat3.Derivable (.LT n₁ n₂) → CompareNat1.Derivable (.LT n₁ n₂) :=
  fun ⟨𝒟₃⟩ => 𝒟₃.induction (motive := fun n₁ n₂ => CompareNat1.Derivable (.LT n₁ n₂))
    (CompareNat1.Derivation.LT_Succ ·)
    (fun {_ n₂} _ ⟨𝒟₁⟩ => CompareNat1.Derivation.LT_Trans 𝒟₁ (.LT_Succ n₂))

/-!
同値な命題として定義して練習問題2.9 [基礎概念,§2.5]の解答とする。
-/
theorem CN1_iff_CN2 : CompareNat1.Derivable (.LT n₁ n₂) ↔ CompareNat2.Derivable (.LT n₁ n₂) :=
  ⟨CN2_of_CN1, CN1_of_CN3 ∘ CN3_of_CN2⟩

theorem CN2_iff_CN3 : CompareNat2.Derivable (.LT n₁ n₂) ↔ CompareNat3.Derivable (.LT n₁ n₂) :=
  ⟨CN3_of_CN2, CN2_of_CN1 ∘ CN1_of_CN3⟩

theorem CN3_iff_CN1 : CompareNat3.Derivable (.LT n₁ n₂) ↔ CompareNat1.Derivable (.LT n₁ n₂) :=
  ⟨CN1_of_CN3, CN3_of_CN2 ∘ CN2_of_CN1⟩
