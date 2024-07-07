import HelloTypeSystem.ML3

namespace HelloTypeSystem.ML3

/-!
# EvalML3のメタ定理
-/

/-
## EvalML3における判断の導出例

### 練習問題5.1
-/

example : Evaluation Env.nil (.Let "sq" (.Fn "x" ("x" * "x")) ((.App "sq" 3) + (.App "sq" 4))) 25 :=
  (.Let .Fn
    (.Add
      (.App .Var .Int
        (.Mul (.Var) (.Var))
      )
      (.App .Var .Int
        (.Mul (.Var) (.Var))
      )
    )
  )

example : Evaluation Env.nil (.Let "sm" (.Fn "f" ((.App "f" 3) + (.App "f" 4))) (.App "sm" (.Fn "x" ("x" * "x")))) 25 :=
  (.Let .Fn
    (.App .Var .Fn
      (.Add
        (.App .Var .Int
          (.Mul (.Var) (.Var))
        )
        (.App .Var .Int
          (.Mul (.Var) (.Var))
        )
      )
    )
  )

example : Evaluation Env.nil
  (
    (.Let "twice" (.Fn "f" (.Fn "x" (.App "f" (.App "f" "x"))))
      /- in -/
      (.App (.App "twice" (.Fn "x" ("x" * "x"))) 2)
    )
  )
  16
:=
  (.Let .Fn
    (.App
      (.App .Var .Fn .Fn)
      (.Int)
      (.App
        (.VarIr .Var)
        (.App
          (.VarIr .Var)
          (.Var)
          (.Mul .Var .Var)
        )
        (.Mul .Var .Var)
      )
    )
  )

example : Evaluation Env.nil
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
          (.App (.App (.App "compose" "p") "q") 4) -- compose p q 4
        )
      )
    )
  )
  64
:=
  -- let compose = fun ... in
  (.Let .Fn
    -- let p = fun ... in
    (.Let .Fn
      -- let q = fun ... in
      (.Let .Fn
        -- compose p q 4
        (.App
          -- compose p q
          (.App
            -- compose p
            (.App
              (.VarIr (.VarIr .Var)) -- compose
              (.VarIr .Var)          -- p
              (.Fn) -- compose p
            )
            (.Var) -- q
            (.Fn) -- (compose p) q
          )
          (.Int) -- 4
          -- f (g x)
          (.App
            (.VarIr (.VarIr .Var))
            -- g x = q x = x + 4
            (.App (.VarIr .Var) (.Var) (.Add .Var .Int))
            (.Mul .Var .Var) -- x * x = p x = f x
          )
        )
      )
    )
  )

/-!
## EvalML3の評価の一意性
-/

/--
EvalML3の評価の一意性（\[基礎概念,§5.7] 定理5.2）
-/
theorem eval_value_uniq {e : Expr} {E : Env} {v : Value} (d : Evaluation E e v) : {v' : Value} → Evaluation E e v' → v = v' :=
  d.induction
    (motive := fun E e v => ∀ {v' : Value}, Evaluation E e v' → v = v')
    (fun .Int  => rfl)
    (fun .Bool => rfl)
    (fun .Var  => rfl)
    (fun _ d _ (.VarIr d') => d d')
    (fun d₁ d₂ h _ (.Add d₁' d₂' h') =>
      have h₁ := d₁ d₁' |> Value.Z.inj
      have h₂ := d₂ d₂' |> Value.Z.inj
      congrArg Value.Z (h ▸ h₂ ▸ h₁ ▸ h')
    )
    (fun d₁ d₂ h _ (.Sub d₁' d₂' h') =>
      have h₁ := d₁ d₁' |> Value.Z.inj
      have h₂ := d₂ d₂' |> Value.Z.inj
      congrArg Value.Z (h ▸ h₂ ▸ h₁ ▸ h')
    )
    (fun d₁ d₂ h _ (.Mul d₁' d₂' h') =>
      have h₁ := d₁ d₁' |> Value.Z.inj
      have h₂ := d₂ d₂' |> Value.Z.inj
      congrArg Value.Z (h ▸ h₂ ▸ h₁ ▸ h')
    )
    (fun d₁ d₂ h _ d' =>
      match d' with
      | .LTT _ _ _      => rfl
      | .LTF d₁' d₂' h' =>
          have h₁ := d₁ d₁' |> Value.Z.inj
          have h₂ := d₂ d₂' |> Value.Z.inj
          absurd h (h₂ ▸ h₁ ▸ h')
    )
    (fun d₁ d₂ h _ d' =>
      match d' with
      | .LTF _ _ _      => rfl
      | .LTT d₁' d₂' h' =>
          have h₁ := d₁ d₁' |> Value.Z.inj
          have h₂ := d₂ d₂' |> Value.Z.inj
          absurd (h₂ ▸ h₁ ▸ h') h
    )
    (fun d₁ d₂ _ d' =>
      match d' with
      | .IfT _   d₂' => d₂ d₂'
      | .IfF d₁' _   => d₁ d₁' |> Value.B.inj |> Bool.noConfusion
    )
    (fun d₁ d₂ _ d' =>
      match d' with
      | .IfF _   d₂' => d₂ d₂'
      | .IfT d₁' _   => d₁ d₁' |> Value.B.inj |> Bool.noConfusion
    )
    (fun d₁ d₂ _ (.Let d₁' d₂') => d₂ (d₁ d₁' ▸ d₂'))
    (fun .Fn => rfl)
    (fun d₁ d₂ d₀ _ (.App d₁' d₂' d₀') =>
      have ⟨h₁, h₂, h₃⟩ := d₁ d₁' |> Value.Cls.inj
      d₀ <| h₃ ▸ h₂ ▸ h₁ ▸ d₂ d₂' ▸ d₀'
    )
