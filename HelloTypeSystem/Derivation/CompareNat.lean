import HelloTypeSystem.Basic
open HelloTypeSystem (PNat Judgement)

namespace CompareNat1
/--
導出システムCompareNat1の推論規則
-/
inductive Derivation : Judgement → Type where
  | LT_Succ (n : PNat)
    : Derivation (.LT n n.S)
  | LT_Trans {n₁ n₂ n₃ : PNat}
    : Derivation (.LT n₁ n₂) → Derivation (.LT n₂ n₃) → Derivation (.LT n₁ n₃)

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
end CompareNat3
