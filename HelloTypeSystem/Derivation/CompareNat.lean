import HelloTypeSystem.Basic

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
導出システムCompareNat1は判断"$n_1$ is less than $n_2$"に対して、
規則LT_Transにおける中間の項（`n₂`）の取り方によって異なる導出を与える。
-/

/--
判断"Z is less than SSSSZ"のCompareNat1による導出

規則LT_Transで$n_2 = {\tt SZ}$, $n_2 = {\tt SSZ}$, $n_2 = {\tt SSSZ}$として導出する。
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

規則LT_Transで$n_2 = {\tt SSZ}$, $n_2 = {\tt SZ}$, $n_2 = {\tt SSSZ}$として導出する。
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

規則LT_Transで$n_2 = {\tt SSSZ}$, $n_2 = {\tt SZ}$, $n_2 = {\tt SSZ}$として導出する。
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
