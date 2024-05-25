import HelloTypeSystem.ML1

namespace HelloTypeSystem.ML1

/-!
# 整数・真偽値式の評価
-/

/-!
## 導出システムEvalML1の評価の例

練習問題3.1 \[基礎概念,§3.1]
-/

theorem «3 + 5 ⇓ 8» : Derivable (3 + 5 ⇓ 8) :=
  ⟨.E_Plus .E_Int .E_Int (.B_Plus rfl)⟩

theorem «8 - 2 - 3 ⇓ 3» : Derivable (8 - 2 - 3 ⇓ 3) :=
  ⟨.E_Minus
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    .E_Int
    (.B_Minus rfl)
  ⟩

theorem «(4 + 5) * (1 - 10) ⇓ -81» : Derivable ((4 + 5) * (1 - 10) ⇓ (-81 : Int)) :=
  ⟨.E_Times
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    (.B_Times rfl)
  ⟩

theorem «if 4 < 5 then 2 + 3 else 8 * 8 ⇓ 5» : Derivable (.If (.LT 4 5) (2 + 3) (8 * 8) ⇓ 5) :=
  ⟨.E_IfT
    (.E_LT .E_Int .E_Int (.B_LTT <| by simp))
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
  ⟩

theorem «3 + if -23 < -2 * 8 then 8 else 2 + 4 ⇓ 11» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 (2 + 4)) ⇓ 11) :=
  ⟨.E_Plus
    .E_Int
    (.E_IfT
      (.E_LT
        .E_Int
        (.E_Times .E_Int .E_Int (.B_Times rfl))
        (.B_LTT <| by simp)
      )
      .E_Int
    )
    (.B_Plus rfl)
  ⟩

theorem «3 + (if -23 < -2 * 8 then 8 else 2) + 4 ⇓ 15» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 2) + 4 ⇓ 15) :=
  ⟨.E_Plus
    (.E_Plus
      .E_Int
      (.E_IfT
        (.E_LT
          .E_Int
          (.E_Times .E_Int .E_Int (.B_Times rfl))
          (.B_LTT <| by simp)
        )
        .E_Int
      )
      (.B_Plus rfl)
    )
    .E_Int
    (.B_Plus rfl)
  ⟩
