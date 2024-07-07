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
