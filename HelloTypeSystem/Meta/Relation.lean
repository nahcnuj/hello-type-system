import HelloTypeSystem.Basic
import HelloTypeSystem.Meta.EvalNatExpr
import HelloTypeSystem.Meta.ReduceNatExpr

namespace HelloTypeSystem

/-!
# 導出システム同士の関係

## 評価と簡約の等価性
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

def EvalNatExpr.Derivation.prepend_reduce (d : EvalNatExpr.Derivation (e' ⇓ n)) : ReduceNatExpr.Derivation (e ⟶ e') → EvalNatExpr.Derivation (e ⇓ n)
  | .R_Plus (n₃ := «n₁+n₂») d' =>
      have heq : n = «n₁+n₂» := EvalNatExpr.eval_uniq d (.E_Const «n₁+n₂»)
      heq ▸ .E_Add (.E_Const _) (.E_Const _) d'
  | .R_Times (n₃ := «n₁*n₂») d' =>
      have heq : n = «n₁*n₂» := EvalNatExpr.eval_uniq d (.E_Const «n₁*n₂»)
      heq ▸ .E_Mul (.E_Const _) (.E_Const _) d'
  | .R_PlusL d' =>
      match d with
      | .E_Add d₁' d₂ dp => .E_Add (d₁'.prepend_reduce d') d₂ dp
  | .R_PlusR d' =>
      match d with
      | .E_Add d₁ d₂' dp => .E_Add d₁ (d₂'.prepend_reduce d') dp
  | .R_TimesL d' =>
      match d with
      | .E_Mul d₁' d₂ dt => .E_Mul (d₁'.prepend_reduce d') d₂ dt
  | .R_TimesR d' =>
      match d with
      | .E_Mul d₁ d₂' dt => .E_Mul d₁ (d₂'.prepend_reduce d') dt

-- theorem x : ReduceNatExpr.Derivation (e ⟶* e') → EvalNatExpr.Derivation (e' ⇓ n) → EvalNatExpr.Derivable (e ⇓ n)
--   | .MR_Zero, d => d
--   | .MR_Once d, _ =>
--       match d with
--       | .R_Plus _ => sorry

/--
定理2.28 \[基礎概念,§2.1]
-/
theorem eval_of_mreduce {n : PNat} : ReduceNatExpr.Derivation (e ⟶* n) → EvalNatExpr.Derivable (e ⇓ n)
  | .MR_Zero (e := .Nat n) =>
      @EvalNatExpr.Derivation.E_Const n
  | .MR_Once d =>
      match d with
      | .R_Plus (n₁ := n₁) (n₂ := n₂) d =>
          EvalNatExpr.Derivation.E_Add (.E_Const n₁) (.E_Const n₂) (EvalNatExpr.Derivation.ofNatPlus d.toNatPlus)
      | .R_Times (n₁ := n₁) (n₂ := n₂) d =>
          EvalNatExpr.Derivation.E_Mul (.E_Const n₁) (.E_Const n₂) (EvalNatExpr.Derivation.ofNatTimes d.toNatTimes)
  | .MR_Multi (e := e) (e' := e') d₁ d₂ =>
      have := eval_of_mreduce d₂
      sorry
