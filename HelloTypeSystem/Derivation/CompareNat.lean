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

private abbrev Derivable := (@HelloTypeSystem.Derivable · Derivation)

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

`motive n₁ n₂`が$P(\MV{n_1},\MV{n_2})$に対応する。
-/
def Derivation.induction
  {motive : PNat → PNat → Sort _} -- P(n₁,n₂)
  {n₁ n₂ : PNat}
  (H0 : ∀ n : PNat, motive n n.S)
  (H1 : ∀ {n₁ n₂ n₃ : PNat}, Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → motive n₁ n₂ → motive n₂ n₃ → motive n₁ n₃)
  (d : Derivation (.LT n₁ n₂))
: motive n₁ n₂ :=
  match d with
    | .LT_Succ k => H0 k
    | .LT_Trans d12 d23 =>
          H1 d12 d23 (induction H0 H1 d12) (induction H0 H1 d23)
/-!
自動で生成される`casesOn`や`rec`などは`motive`の型が`(a : Judgement) → Derivation a → Sort u`となっていて、
ペアノ自然数に関する述語$P(\MV{n_1},\MV{n_2})$を扱うには`PNat → PNat → Sort u`な関数を作る必要があった。
-/

/--
$\forall\MV{n_1},\MV{n_2}. \bigl[\TT{S$\MV{n_1}$ is less than $\MV{n_2}$} \implies \exists\MV{n_3}. \MV{n_2} \equiv \TT{S$\MV{n_3}$}\bigr]$
-/
theorem exists_succ_of_succ_lt {n₁ n₂ : PNat} : Derivation (.LT n₁.S n₂) → ∃ n₃ : PNat, n₂ = n₃.S :=
  Derivation.induction (motive := fun _ n₂ => ∃ n₃ : PNat, n₂ = n₃.S)
    (fun n => Exists.intro n rfl)
 -- (fun {n₁ n₂ n₃} lt12 lt23 ⟨n₂', h₂'⟩ ⟨n₃', h₃'⟩ =>
    (fun _ _ _ ⟨n₃',h₃'⟩ => Exists.intro n₃' h₃')

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

private abbrev Derivable := (@HelloTypeSystem.Derivable · Derivation)

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

private abbrev Derivable := (@HelloTypeSystem.Derivable · Derivation)

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

end CompareNat3
