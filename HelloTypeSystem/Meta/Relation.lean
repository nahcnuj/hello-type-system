import HelloTypeSystem.Basic
import HelloTypeSystem.Meta.EvalNatExpr
import HelloTypeSystem.Meta.ReduceNatExpr

namespace HelloTypeSystem

/-!
# 導出システム同士の関係
-/

/-!
## 評価の導出システムEvalNatExprと簡約の導出システムReduceNatExprの等価性（定理2.27, 2.28 \[基礎概念, §2.1]）
-/
/--
定理2.27 \[基礎概念,§2.1]
-/
theorem mreduce_of_eval : EvalNatExpr.Derivation (e ⇓ n) → ReduceNatExpr.Derivable (e ⟶* n)
  | .E_Const n =>
      ⟨.MR_Zero⟩
  | .E_Add dl dr dp =>
      have ⟨dl⟩ := mreduce_of_eval dl
      have ⟨dr⟩ := mreduce_of_eval dr
      have ⟨dl⟩ := dl.MR_PlusL
      have ⟨dr⟩ := dr.MR_PlusR
      ⟨.MR_Multi
        (.MR_Multi dl dr)
        (.MR_Once <| .R_Plus dp)
      ⟩
  | .E_Mul dl dr dt =>
      have ⟨dl⟩ := mreduce_of_eval dl
      have ⟨dr⟩ := mreduce_of_eval dr
      have ⟨dl⟩ := dl.MR_TimesL
      have ⟨dr⟩ := dr.MR_TimesR
      ⟨.MR_Multi
        (.MR_Multi dl dr)
        (.MR_Once <| .R_Times dt)
      ⟩
