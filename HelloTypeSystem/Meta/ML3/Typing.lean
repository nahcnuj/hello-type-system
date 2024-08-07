import HelloTypeSystem.ML3

namespace HelloTypeSystem.ML3
open ML3

/-!
# ML3に対する型付け
-/

/-
## TypingML3における型判断の導出例

### 練習問題8.1
-/

example : Typed [("y", .Int), ⟨"x", .Bool⟩] (.If "x" ("y" + 1) ("y" - 1)) .Int :=
  (.If
    (.VarIr .Var)
    (.Add .Var .Int)
    (.Sub .Var .Int)
  )

example : Typed [] (.Let "x" (.LT 3 2) (.Let "y" 5 (.If "x" "y" 2))) .Int :=
  -- let x = (3 : Int) < (2 : Int) : Bool in
  (.Let
    (.LT .Int .Int)
    -- let y = 5 : Int in
    (.Let
      (.Int)
      (.If (.VarIr .Var) (.Var) (.Int))
    )
  )

example : Typed [] (.Fn "x" ("x" + 1)) (.Fn .Int .Int) :=
  (.Fn (.Add .Var .Int))

example : Typed [] (.Fn "f" ((.App "f" 0) + (.App "f" 1))) (.Fn (.Fn .Int .Int) .Int) :=
  (.Fn
    (.Add
      (.App .Var .Int)
      (.App .Var .Int)
    )
  )

example : Typed [] (.Let "k" (.Fn "x" (.Fn "y" "x")) (.App (.App "k" 3) true)) .Int :=
  (.Let
    (.Fn (.Fn (.VarIr .Var)))
    (.App
      (.App .Var .Int)
      (.Bool)
    )
  )

example : Typed []
  (
    (.Let "compose"
      /- := -/
      (.Fn "f"
        (.Fn "g"
          (.Fn "x"
            (.App "f" (.App "g" "x"))
          )
        )
      )
      /- in -/
      (.Let "p" (.Fn "x" ("x" * "x"))
        /- in -/
        (.Let "q" (.Fn "x" ("x" + 4))
          /- in -/
          (.App (.App "compose" "p") "q") -- compose p q
        )
      )
    )
  )
  (.Fn .Int .Int)
:=
  (.Let
    (.Fn
      (.Fn
        (.Fn
          (.App
            (.VarIr (.VarIr .Var))
            (.App (.VarIr .Var) .Var)
          )
        )
      )
    )
    (.Let
      (.Fn (.Mul .Var .Var))
      (.Let
        (.Fn (.Add .Var .Int))
        (.App
          (.App (.VarIr (.VarIr .Var)) (.VarIr .Var))
          (.Var)
        )
      )
    )
  )

/-!
## 型安全性
-/

/--
TypingML3による型安全性
-/
theorem type_safety (compat : (EnvCompat E Γ)) : Typed Γ e τ → Evaluation E e r → ∃ v : Value, r = .inr v ∧ ValueCompat v τ
  | .Int,         .Int                          => ⟨_, rfl, ValueCompat.Z_Int ▸ True.intro⟩
  | .Bool,        .Bool                         => ⟨_, rfl, ValueCompat.B_Bool ▸ True.intro⟩
  | .Var,         .Var                          => ⟨_, rfl, (EnvCompat.cons_cons ▸ compat).right.right⟩
  | .VarIr dt _,  .VarIr dr _                   => type_safety (EnvCompat.cons_cons ▸ compat).right.left dt dr
  | .Add ..,      .Add (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ + i₂, rfl, ValueCompat.Z_Int ▸ True.intro⟩
  | .Sub ..,      .Sub (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ - i₂, rfl, ValueCompat.Z_Int ▸ True.intro⟩
  | .Mul ..,      .Mul (i₁ := i₁) (i₂ := i₂) .. => ⟨i₁ * i₂, rfl, ValueCompat.Z_Int ▸ True.intro⟩
  | .LT ..,       .LTT _ _ _                    => ⟨true,    rfl, ValueCompat.B_Bool ▸ True.intro⟩
  | .LT ..,       .LTF _ _ _                    => ⟨false,   rfl, ValueCompat.B_Bool ▸ True.intro⟩
  | .If _ dt _,   .IfT _ dr                     => type_safety compat dt dr
  | .If _ _  dt,  .IfF _ dr                     => type_safety compat dt dr
  | .Let dtb dte, .Let drb dre =>
      have ⟨_, heq, h⟩ := type_safety compat dtb drb
      have compat' := EnvCompat.cons_cons ▸ ⟨rfl, compat, Sum.inr.inj heq ▸ h⟩
      type_safety compat' dte dre
  | .Fn d,    .Fn        => ⟨_, rfl, ValueCompat.Cls_Fn ▸ ⟨Γ, compat, d⟩⟩
  | .App dt₁ dt₂, .App (E' := _E₀) dr₁ dr₂ dr₃ =>
      /-
        ```
             dr₁ ∈        E ⊢ e₁ ⇓ Cls(E₀, x, e₀) = (E₀)[fun x → e₀],
             dr₂ ∈        E ⊢ e₂ ⇓ v₂,
             dr₃ ∈ E₀, x=v₂ ⊢ e₀ ⇓ v
        dr ≡ --------------------------------------------------------,
                          E ⊢ e₁ e₂ ⇓ v
             dt₁ ∈ Γ ⊢ e₁ : τ₂ → τ,
             dt₂ ∈ Γ ⊢ e₂ : τ₂
        dt ≡ ----------------------
                   Γ ⊢ e₁ e₂ : τ
        ```
        `⊢ v : τ`を示したい。
        `v`について与えられているのは判断`E₀, x=v₂ ⊢ e₀ ⇓ v`の導出`dr₃`である。
        これに対応する型判断`Γ₀, x:τ₂ ⊢ e₀ : τ`と、`x`の値についての整合性`⊨ v₂ : τ₂`が得られれば、帰納法の仮定を適用して`⊢ v : τ`を示せる。
      -/
      -- 1. `dr₃`に対応する型判断`Γ₀, x:τ₂ ⊢ e₀ : τ`を導出する
      have ⟨_Γ₀, compat₀, dt₃⟩ :=
        -- `⊨ E : Γ`, `Γ ⊢ e₁ : τ₂ → τ`, `E ⊢ e₁ ⇓ Cls(E₀, x, e₀)`から帰納法の仮定によって`⊨ Cls(E₀, x, e₀) : τ₂ → τ`
        have ⟨_, heq, h⟩ := type_safety compat dt₁ dr₁
        -- 定義から`∃Γ₀, ⊨ E₀ : Γ₀ ∧ Γ₀, x:τ₂ ⊢ e₀ : τ`
        ValueCompat.Cls_Fn ▸ Sum.inr.inj heq ▸ h
      -- 2. 整合性`⊨ v₂ : τ₂`を示す：`⊨ E : Γ`, `Γ ⊢ e₂ : τ₂`, `E ⊢ e₂ ⇓ v₂`から帰納法の仮定
      have ⟨_, heq₂, hvc⟩ := type_safety compat dt₂ dr₂
      -- 3. `⊨ E₀, x=v₂ : Γ₀, x:τ₂`を示す ∵ `⊨ E₀ : Γ₀`, `⊨ v₂ : τ₂`
      have compat' := EnvCompat.cons_cons ▸ ⟨rfl, compat₀, Sum.inr.inj heq₂ ▸ hvc⟩
      -- 4. `⊢ v : τ`を示す：`⊨ E₀, x=v₂ : Γ₀, x:τ₂`, `E₀, x=v₂ ⊢ e₀ ⇓ v`, `Γ₀, x:τ₂ ⊢ e₀ : τ`から帰納法の仮定
      type_safety compat' dt₃ dr₃

  -- 部分式について型不整合または実行時エラーの場合は矛盾することを示す
  | .Var, .VarIr _ hne => absurd (EnvCompat.cons_cons ▸ compat).left hne
  | .VarIr _ hne, .Var => absurd (EnvCompat.cons_cons ▸ compat).left.symm hne
  | .Add dt _, .AddBoolL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Add _ dt, .AddBoolR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Add dt _, .AddClsL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Add _ dt, .AddClsR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Add dt _, .AddErrL dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Add _ dt, .AddErrR dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Sub dt _, .SubBoolL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Sub _ dt, .SubBoolR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Sub dt _, .SubClsL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Sub _ dt, .SubClsR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Sub dt _, .SubErrL dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Sub _ dt, .SubErrR dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Mul dt _, .MulBoolL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Mul _ dt, .MulBoolR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .Mul dt _, .MulClsL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Mul _ dt, .MulClsR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .Mul dt _, .MulErrL dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Mul _ dt, .MulErrR dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .LT dt _, .LTBoolL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .LT _ dt, .LTBoolR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Int ▸ Sum.inr.inj heq ▸ h
  | .LT dt _, .LTClsL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .LT _ dt, .LTClsR dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Int ▸ Sum.inr.inj heq ▸ h
  | .LT dt _, .LTErrL dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .LT _ dt, .LTErrR dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .If dt _ _, .IfInt dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Z_Bool ▸ Sum.inr.inj heq ▸ h
  | .If dt _ _, .IfCls dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Cls_Bool ▸ Sum.inr.inj heq ▸ h
  | .If dt _ _, .IfErr dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .If _ dt _, .IfTErr _ dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .If _ _ dt, .IfFErr _ dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Let dt _, .LetBindingErr dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .Let dt₁ dt₂, .LetExprErr dr₁ dr₂ =>
      have ⟨_, heq, h⟩ := type_safety compat dt₁ dr₁
      have compat' := EnvCompat.cons_cons ▸ ⟨rfl, compat, Sum.inr.inj heq ▸ h⟩
      have ⟨_, h, _⟩ := type_safety compat' dt₂ dr₂
      Sum.noConfusion h
  | .App dt _, .AppIntL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.Z_Cls ▸ Sum.inr.inj heq ▸ h
  | .App dt _, .AppBoolL dr =>
      have ⟨_, heq, h⟩ := type_safety compat dt dr
      False.elim <| ValueCompat.B_Cls ▸ Sum.inr.inj heq ▸ h
  | .App dt _, .AppErrL dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .App _ dt, .AppErrR _ dr =>
      have ⟨_, h, _⟩ := type_safety compat dt dr
      Sum.noConfusion h
  | .App dt₁ dt₂, .AppErrA dr₁ dr₂ dr₃ =>
      -- .App の場合の導出と同じ
      have ⟨_Γ₀, compat₀, dt₃⟩ :=
        have ⟨_, heq, h⟩ := type_safety compat dt₁ dr₁
        ValueCompat.Cls_Fn ▸ Sum.inr.inj heq ▸ h
      have ⟨_, heq₂, hvc⟩ := type_safety compat dt₂ dr₂
      have compat' := EnvCompat.cons_cons ▸ ⟨rfl, compat₀, Sum.inr.inj heq₂ ▸ hvc⟩
      type_safety compat' dt₃ dr₃

namespace Example
/-!
## 方程式の抽出

$\MV{e} := \TT{fun x → x 3 4}$（`e4`）に対して
$$
\mathop{\mathit{Extract}}(\varnothing, \MV{e})
= (
  \{
    \MV{\alpha_0} = \TT{int}\to\MV{\alpha_1},\,
    \MV{\alpha_1} = \TT{int}\to\MV{\alpha_2}
  \},\,
  \MV{\alpha_0} \to \MV{\alpha_2}
)
$$
となることを確認する。
-/

def e := Expr.Fn "x" (((Expr.Var "x").App 3).App 4)
def E : SimultaneousEquation :=
  ⟨[], [
    -- α1 = int → α2
    (.Var "α1", .Fn .Int (.Var "α2")),
    -- α0 = int → α1
    (.Var "α0", .Fn .Int (.Var "α1"))
  ]⟩

theorem «Extract([x : α0], x 3)» (h : ((Expr.Var "x").App 3).fv ⊆ TypeEnv.dom [("x", Types.Var "α0")])
: (Expr.App "x" 3).extract [("x", .Var "α0")] h ["α0"]
  = (
      ⟨[], [(.Var "α0", .Fn .Int (.Var "α1"))]⟩,
      .Var "α1",
      ["α1", "α0"]
    )
:=
  Expr.extract.App
    (Expr.extract.Var (fun _ h => TypeEnv.dom.cons ▸ Expr.fv.Var ▸ Or.inr h))
    (Expr.extract.Z (Expr.fv.Int ▸ TypeEnv.dom.cons ▸ fun _ => Or.inl))

theorem «Extract([x : α0], x 3 4)» (h : (((Expr.Var "x").App 3).App 4).fv ⊆ TypeEnv.dom [("x", Types.Var "α0")])
: (Expr.App (.App (.Var "x") 3) 4).extract [("x", .Var "α0")] h ["α0"]
  = (
      ⟨[], [(.Var "α1", .Fn .Int (.Var "α2"))] ++ [(.Var "α0", .Fn .Int (.Var "α1"))]⟩,
      .Var "α2",
      ["α2", "α1", "α0"]
    )
:=
  Expr.extract.App
    («Extract([x : α0], x 3)»
      (Expr.fv.App ▸ Expr.fv.Var ▸ Expr.fv.Int ▸ TypeEnv.dom.cons ▸ TypeEnv.dom.nil ▸ fun _ h => h.elim Or.inr Or.inl)
    )
    (Expr.extract.Z
      (Expr.fv.Int ▸ TypeEnv.dom.cons ▸ fun _ => Or.inl)
    )

theorem «Extract(∅, fun x → x 3 4)» (h : e.fv ⊆ TypeEnv.dom [])
: e.extract [] h [] = (E, .Fn (.Var "α0") (.Var "α2"), ["α2", "α1", "α0"])
:=
  Expr.extract.Fn
    («Extract([x : α0], x 3 4)»
      (Expr.fv.App ▸ TypeEnv.dom.cons ▸ TypeEnv.dom.nil ▸ fun _ h =>
        h.elim
          (Expr.fv.App ▸ fun h => h.elim
            (Expr.fv.Var ▸ Or.inr)
            (Expr.fv.Int ▸ Or.inl)
          )
          (Expr.fv.Int ▸ Or.inl)
      )
    )

/-!
## 一階の単一化

方程式
$E := \{ \MV{\alpha_0} = \TT{int}\to\MV{\alpha_1},\, \MV{\alpha_1} = \TT{int}\to\MV{\alpha_2} \}$
の解（型代入）が任意の型$\MV{\tau}$に対して
$S_{\MV{\tau}} := [{\TT{int}\to\TT{int}\to\MV{\tau}}/{\MV{\alpha_0}},\,{\TT{int}\to\MV{\tau}}/{\MV{\alpha_1}},\,{\MV{\tau}}/{\MV{\alpha_2}}]$
となることを確認する。
-/

-- example : TypeSubst.solved [("α2", .Int), ("α1", .Fn .Int .Int), ("α0", .Fn .Int (.Fn .Int .Int))] E :=
--   ⟨rfl, rfl, True.intro⟩
-- example : TypeSubst.solved [("α2", .Bool), ("α1", .Fn .Int .Bool), ("α0", .Fn .Int (.Fn .Int .Bool))] E :=
--   ⟨rfl, rfl, True.intro⟩
-- example : TypeSubst.solved [("α2", .Fn .Int .Int), ("α1", .Fn .Int (.Fn .Int .Int)), ("α0", .Fn .Int (.Fn .Int (.Fn .Int .Int)))] E :=
--   ⟨rfl, rfl, True.intro⟩

-- theorem «[α0 = int → α1, α1 = int → α2]».solution (τ : Types) : TypeSubst.solved [("α2", τ), ("α1", .Fn .Int τ), ("α0", .Fn .Int (.Fn .Int τ))] E :=
--   ⟨rfl, rfl, True.intro⟩

/--
$S := [\TT{int}→\TT{int}\to\MV{\alpha_2}/\MV{\alpha_0},\,\TT{int}\to\MV{\alpha_2}/\MV{\alpha_1}]$
-/
def S : TypeSubst := [("α1", Types.Fn .Int (.Var "α2")), ("α0", .Fn .Int (.Fn .Int (.Var "α2")))]

/--
$E$の最汎単一化子は$S$である。

$E$の一般解$S' := [{\TT{int}\to\TT{int}\to\MV{\tau}}/{\MV{\alpha_0}},\,{\TT{int}\to\MV{\tau}}/{\MV{\alpha_1}},\,{\MV{\tau}}/{\MV{\alpha_2}}]$について$S'' := [\MV{\tau}/\MV{\alpha_2}]$とすれば
$$S' = S'' \circ S$$
が成り立つ。
-/
theorem «[α0 = int → α1, α1 = int → α2]».mgu {τ : Types} : (υ : Types) → [("α2", τ), ("α1", Types.Fn .Int τ), ("α0", .Fn .Int (.Fn .Int τ))] υ = ([("α2", τ)] ∘ S) υ
  | .Var α =>
      if ha : "α0" = α
      then by simp [Types.subst, List.findSome?, ha.symm]
      else
        if hb : "α1" = α
        then by simp [Types.subst, List.findSome?, hb.symm]
        else by simp [Types.subst, List.findSome?, ha, hb]
  | .Int      => rfl
  | .Bool     => rfl
  | .Fn υ₁ υ₂ => by simp [Types.subst, «[α0 = int → α1, α1 = int → α2]».mgu υ₁, «[α0 = int → α1, α1 = int → α2]».mgu υ₂]

/-
theorem H' (S' : TypeSubst) (h : S'.solved E) : (τ : Types) → S' τ = ([("α2", Types.Var "α2")] ∘ S) τ
  | .Var α =>
      have ⟨h1, h0, _⟩ := h
      if ha : "α0" = α
      then by
        have : ¬ "α1" = α := fun h => nomatch h ▸ ha
        simp [Types.subst, List.findSome?, ha, if_neg this]
        -- have ⟨x, t⟩ := S'.head (fun hempty =>
        --   have ⟨h1, _⟩ := hempty ▸ h
        --   by simp [Types.subst] at h1
        --   )
        split
        . next υ heq =>
            match υ with
            | .Var _ => sorry
            have ⟨⟨x, t⟩, mem, h⟩ := List.exists_of_findSome?_eq_some heq
            have := List.elem_eq_true_of_mem mem
            if heq : (x, t).fst = α
            then
              have := if_pos heq ▸ h |> Option.some.inj
              sorry
            else sorry
        . sorry -- by simp [ha, h0, h1, Types.subst, List.findSome?] -- ha ▸ h0 ▸ by simp [Types.subst, List.findSome?]
      else
        if hb : "α1" = α
        then by simp [Types.subst, List.findSome?, hb.symm]
        else by simp [Types.subst, List.findSome?, ha, hb]
  | .Int      => rfl
  | .Bool     => rfl
  | .Fn τ₁ τ₂ => by simp [Types.subst, H' S' h τ₁, H' S' h τ₂]
-/

/-
/--
$S$は$E$の最汎単一化子である。
-/
theorem S_is_mgu : S.most_general E :=
  And.intro
    (⟨rfl, rfl, True.intro⟩)
    sorry-- (fun S' h => Exists.intro [("α2", .Var "α2")] (funext (H' S' h)))
-/

example : SimultaneousEquation.unify ⟨[], []⟩ = Sum.inr [] := SimultaneousEquation.unify_nil
example : SimultaneousEquation.unify ⟨[], [(.Var "'b", .Int)]⟩ = Sum.inr [("'b", .Int)] :=
  SimultaneousEquation.unify.Var (Types.noConfusion) (Types.fv.Int ▸ by simp) SimultaneousEquation.unify_nil
example : SimultaneousEquation.unify ⟨[], [(.Var "'b", .Int), (.Var "'a", .Fn .Int (.Var "'b"))]⟩ = Sum.inr [("'b", .Int), ("'a", .Fn .Int .Int)] :=
  (SimultaneousEquation.unify.Var
    (Types.noConfusion)
    (Types.fv.Int ▸ by simp)
    (SimultaneousEquation.unify.Var
      (Types.noConfusion)
      (Types.fv.Fn ▸ Types.fv.Int ▸ by simp)
      SimultaneousEquation.unify_nil
    )
  )

/-
#eval E.unify
/-
Sum.inr [("α1", HelloTypeSystem.ML3.Types.Fn (HelloTypeSystem.ML3.Types.Int) (HelloTypeSystem.ML3.Types.Var "α2")),
 ("α0",
  HelloTypeSystem.ML3.Types.Fn
    (HelloTypeSystem.ML3.Types.Int)
    (HelloTypeSystem.ML3.Types.Fn (HelloTypeSystem.ML3.Types.Int) (HelloTypeSystem.ML3.Types.Var "α2")))]
-/
-/

example : E.unify = Sum.inr [("α1", .Fn .Int (.Var "α2")), ("α0", .Fn (.Int) (.Fn .Int (.Var "α2")))] :=
  (SimultaneousEquation.unify.Var (S := [("α0", .Fn .Int (.Fn .Int (.Var "α2")))])
    (Types.noConfusion)
    (Types.fv.Fn ▸ Types.fv.Int ▸ Types.fv.Var ▸ List.append_nil _ ▸ fun S => nomatch S)
    (SimultaneousEquation.unify.Var (S := [])
      (Types.noConfusion)
      (Types.fv.Fn ▸ Types.fv.Int ▸ Types.fv.Var ▸ List.append_nil _ ▸ fun S => nomatch S)
      (SimultaneousEquation.unify_nil)
    )
  )

end Example

/-!
## 型代入補題

補題9.3 \[基礎概念,§9.5]
-/

/--
型代入補題（補題9.3 \[基礎概念,§9.5]）
-/
theorem typed_subst_of_typed : {e : Expr} → Typed Γ e τ → Typed (Γ.subst S) e (τ.subst S)
  | .Z _,    .Int          => .Int
  | .B _,    .Bool         => .Bool
  | .Var _,  .Var          => .Var
  | .Var _,  .VarIr d _    => .VarIr (typed_subst_of_typed d)
  | .Add .., .Add d₁ d₂    => .Add (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
  | .Sub .., .Sub d₁ d₂    => .Sub (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
  | .Mul .., .Mul d₁ d₂    => .Mul (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
  | .LT  .., .LT  d₁ d₂    => .LT  (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
  | .If  .., .If  d₁ d₂ d₃ => .If  (typed_subst_of_typed d₁) (typed_subst_of_typed d₂) (typed_subst_of_typed d₃)
  | .Let .., .Let d₁ d₂    => .Let (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
  | .Fn  .., .Fn  d        => .Fn  (typed_subst_of_typed d)
  | .App .., .App d₁ d₂    => .App (typed_subst_of_typed d₁) (typed_subst_of_typed d₂)
