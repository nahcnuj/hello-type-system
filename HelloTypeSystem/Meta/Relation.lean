import HelloTypeSystem.Basic
import HelloTypeSystem.Meta.EvalNatExpr
import HelloTypeSystem.Meta.ReduceNatExpr

namespace HelloTypeSystem

/-!
# 導出システム同士の関係

## 評価の導出システムEvalNatExprと簡約の導出システムReduceNatExprの等価性（定理2.27, 2.28 \[基礎概念, §2.1]）
-/
/--
定理2.27 \[基礎概念,§2.1]
-/
theorem mreduce_of_eval : EvalNatExpr.Derivation (e ⇓ n) → ReduceNatExpr.Derivable (e ⟶* n)
  | .E_Const n =>
      @ReduceNatExpr.Derivation.MR_Zero n
  | .E_Add dl dr dp =>
      have ⟨dl⟩ := mreduce_of_eval dl
      have ⟨dr⟩ := mreduce_of_eval dr
      have ⟨dl⟩ := dl.MR_PlusL
      have ⟨dr⟩ := dr.MR_PlusR
      have dp := ReduceNatExpr.Derivation.ofNatPlus dp.toNatPlus
      ReduceNatExpr.Derivation.MR_Multi dl dr |> (ReduceNatExpr.Derivation.MR_Multi · dp.R_Plus.MR_Once)
  | .E_Mul dl dr dt =>
      have ⟨dl⟩ := mreduce_of_eval dl
      have ⟨dr⟩ := mreduce_of_eval dr
      have ⟨dl⟩ := dl.MR_TimesL
      have ⟨dr⟩ := dr.MR_TimesR
      have dt := ReduceNatExpr.Derivation.ofNatTimes dt.toNatTimes
      ReduceNatExpr.Derivation.MR_Multi dl dr |> (ReduceNatExpr.Derivation.MR_Multi · dt.R_Times.MR_Once)
