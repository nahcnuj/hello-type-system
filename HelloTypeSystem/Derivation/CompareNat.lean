import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement)

/-! $\newcommand\Set[1]{\mathbf{#1}}$ $\newcommand\MV[1]{\boldsymbol{#1}}$ $\newcommand\TT[1]{\texttt{#1}}$ $\newcommand\Evals{\mathrel{\Downarrow}}$ $\newcommand\Reduces{\mathrel{\longrightarrow}}$ $\newcommand\MReduces{\mathrel{\longrightarrow^{\\!*}}}$ $\newcommand\DReduces{\mathrel{\longrightarrow_{\\!d}}}$ -/
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
判断"Z is less than SSZ"のCompareNat1による導出
-/
def Z_lt_SSZ : Derivation (.LT .Z (.S (.S .Z))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S .Z))
    (.LT_Succ (.Z))
    (.LT_Succ (.S .Z))

/--
判断"SSZ is less than SSSSZ"のCompareNat1による導出
-/
def SSZ_lt_SSSSZ : Derivation (.LT (.S (.S .Z)) (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .S (.S .Z)) (n₂ := (.S (.S (.S .Z)))) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Succ (.S (.S .Z)))
    (.LT_Succ (.S (.S (.S .Z))))

/-!
導出システムCompareNat1は判断"$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$"に対して、
規則LT_Transにおける中間の項（`n₂`）の取り方によって異なる導出を与える。
-/

/--
判断"Z is less than SSSSZ"のCompareNat1による導出

規則LT_Transで$\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SSSZ}$として導出する。
-/
def Z_lt_SSSSZ : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Succ .Z)
    (.LT_Trans (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
      (.LT_Succ (.S .Z))
      (.LT_Trans (n₁ := .S (.S .Z)) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))
        (.LT_Succ (.S (.S .Z)))
        (.LT_Succ (.S (.S (.S .Z))))
      )
    )

/--
判断"Z is less than SSSSZ"のCompareNat1による導出

規則LT_Transで$\MV{n_2} = \TT{SSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSSZ}$として導出する。
-/
def Z_lt_SSSSZ' : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Trans (n₁ := .Z) (n₃ := .S (.S .Z))
      (.LT_Succ .Z)
      (.LT_Succ (.S .Z))
    )
    (.LT_Trans (n₁ := .S (.S .Z)) (n₃ := .S (.S (.S (.S .Z))))
      (.LT_Succ (.S (.S .Z)))
      (.LT_Succ (.S (.S (.S .Z))))
    )

/--
判断"Z is less than SSSSZ"のCompareNat1による導出

規則LT_Transで$\MV{n_2} = \TT{SSSZ}$, $\MV{n_2} = \TT{SZ}$, $\MV{n_2} = \TT{SSZ}$として導出する。
-/
def Z_lt_SSSSZ'' : Derivation (.LT .Z (.S (.S (.S (.S .Z))))) :=
  .LT_Trans (n₁ := .Z) (n₂ := .S (.S (.S .Z))) (n₃ := .S (.S (.S (.S .Z))))
    (.LT_Trans (n₁ := .Z) (n₂ := .S .Z) (n₃ := .S (.S (.S .Z)))
      (.LT_Succ .Z)
      (.LT_Trans (n₁ := .S .Z) (n₂ := .S (.S .Z)) (n₃ := .S (.S (.S .Z)))
        (.LT_Succ (.S .Z))
        (.LT_Succ (.S (.S .Z)))
      )
    )
    (.LT_Succ (.S (.S (.S .Z))))

def Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | .Z   => .LT_Succ .Z
  | .S n => .LT_Trans (Z_lt_S n) (.LT_Succ n.S)

/-
theorem Z_lt_S' : (n : PNat) → Derivable (.LT .Z n.S)
  | .Z   => Derivation.LT_Succ .Z
  | .S n =>
      have ⟨𝒟⟩ := Z_lt_S' n
      Derivation.LT_Trans 𝒟 (.LT_Succ n.S)
-/

/--
CompareNat1における$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$の導出に関する帰納法で、
ペアノ自然数に関する2項述語$P$について$\forall\MV{n_1},\MV{n_2}. \bigl[\TT{$\MV{n_1}$ is less than $\MV{n_2}$} \implies P(\MV{n_1},\MV{n_2})\bigr]$を示す。
-/
def Derivation.induction
  {motive : PNat → PNat → Sort _} -- P(n₁,n₂)
  {n₁ n₂ : PNat}
  (H0 : ∀ n : PNat, motive n n.S)
  (H1 : ∀ {n₁ n₂ n₃ : PNat}, Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → motive n₁ n₂ → motive n₂ n₃ → motive n₁ n₃)
: Derivation (.LT n₁ n₂) → motive n₁ n₂
  | .LT_Succ k      => H0 k
  | .LT_Trans 𝒟₁ 𝒟₂ => H1 𝒟₁ 𝒟₂ (induction H0 H1 𝒟₁) (induction H0 H1 𝒟₂)

/-!
自動で生成される`casesOn`や`rec`などは`motive`の型が`(a : Judgement) → Derivation a → Sort u`となっていて、
ペアノ自然数に関する述語$P(\MV{n_1},\MV{n_2})$を扱うには`PNat → PNat → Sort u`な関数を作る必要があった。
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
theorem exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
 -- (fun {n₁ n₂ n₃} lt12 lt23 ⟨n₂', h₂'⟩ ⟨n₃', h₃'⟩ =>
    (fun _ _ _ ⟨n₃',h₃'⟩ => Exists.intro n₃' h₃')

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
theorem lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
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

theorem lt_trans : {n₁ n₂ n₃ : PNat} → Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃) :=
  fun {_ _ n₃} =>
    Derivation.induction (motive := fun n₁ n₂ => Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃))
      (fun n d => Derivation.LT_Trans (Derivation.LT_Succ n) d)
      (fun d1 d2 _ _ d => Derivation.LT_Trans (Derivation.LT_Trans d1 d2) d)

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

/--
判断"Z is less than SSZ"のCompareNat2による導出
-/
def Z_lt_SSZ : Derivation (.LT .Z PNat.Z.S.S) :=
  .LT_Zero PNat.Z.S

/--
判断"SSZ is less than SSSSZ"のCompareNat2による導出
-/
def SSZ_lt_SSSSZ : Derivation (.LT PNat.Z.S.S PNat.Z.S.S.S.S) :=
  .LT_SuccSucc (n₁ := PNat.Z.S) (n₂ := PNat.Z.S.S.S)
    (.LT_SuccSucc (n₁ := .Z) (n₂ := PNat.Z.S.S)
      (.LT_Zero PNat.Z.S)
    )

/-!
導出システムCompareNat2による導出では、前提に選択の余地がないから導出木の曖昧さは生じない。
-/

def Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | n => .LT_Zero n

theorem exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
    (fun _ ⟨n₂', h₂'⟩ => Exists.intro n₂'.S (h₂' ▸ rfl))

theorem lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
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

theorem lt_trans : {n₁ n₂ n₃ : PNat} → Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃) :=
  fun {_ _ n₃} =>
    Derivation.induction (motive := fun n₁ n₂ => Derivation (.LT n₂ n₃) → Derivable (.LT n₁ n₃))
      (fun _ d =>
        match n₃ with
        | .Z     => nomatch d -- `Sn is less than Z`
        | .S n₃' => Derivation.LT_Zero n₃'
      )
      (fun d12 _ d =>
        match n₃ with
        | .Z   => nomatch d -- `Sn₂ is less than Z`
        | .S _ =>
            have ⟨d⟩ := lt_of_S_lt_S d
            have ⟨d⟩ := lt_trans d12 d
            Derivation.LT_SuccSucc d
      )
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

/--
判断"Z is less than SSZ"のCompareNat3による導出
-/
def Z_lt_SSZ : Derivation (.LT .Z PNat.Z.S.S) :=
  .LT_SuccR (n₁ := .Z) (n₂ := PNat.Z.S)
    (.LT_Succ .Z)

/--
判断"SSZ is less than SSSSZ"のCompareNat3による導出
-/
def SSZ_lt_SSSSZ : Derivation (.LT PNat.Z.S.S PNat.Z.S.S.S.S) :=
  .LT_SuccR (n₁ := PNat.Z.S.S) (n₂ := PNat.Z.S.S.S)
    (.LT_Succ PNat.Z.S.S)

/-!
導出システムCompareNat3による導出では、前提に選択の余地がないから導出木の曖昧さは生じない。
-/

def Z_lt_S : (n : PNat) → Derivation (.LT .Z n.S)
  | .Z   => .LT_Succ .Z
  | .S n => .LT_SuccR (Z_lt_S n)

theorem exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
    (fun _ ⟨n₂',h₂'⟩ => Exists.intro n₂'.S (h₂' ▸ rfl))

theorem lt_of_S_lt_S {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂.S) → Derivable (.LT n₁ n₂) :=
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

end CompareNat3
