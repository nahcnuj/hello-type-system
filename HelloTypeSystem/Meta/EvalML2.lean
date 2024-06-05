import HelloTypeSystem.ML2

namespace HelloTypeSystem.ML2

notation e₁ " ? " e₂ " : " e₃ => Expr.If e₁ e₂ e₃
notation "LET " x:max " = " e₁ " IN " e₂ => Expr.Let x e₁ e₂
notation E " ⊢ " e " ⇓ " v => Evaluation E e v

/-!
# 定義、変数束縛と環境
-/

/-
## 導出システムEvalML2の評価の例

### 練習問題4.1 \[基礎概念,§4.1]
-/
example : [("y", 2), ("x", 3)] ⊢ "x" ⇓ 3 :=
  .VarIr .Var

example : [("y", 4), ("x", true)] ⊢ ("x" ? "y" + 1 : "y" - 1) ⇓ 5 :=
  .IfT
    (.VarIr .Var)
    (.Add .Var .Int)

example : [] ⊢ LET "x" = 1 + 2 IN "x" * 4 ⇓ 12 :=
  .Let
    (.Add .Int .Int)
    (.Mul .Var .Int)

example : [] ⊢ LET "x" = 3 * 3 IN LET "y" = 4 * "x" IN "x" + "y" ⇓ 45 :=
  .Let
    (.Mul .Int .Int)
    (.Let
      (.Mul .Int .Var)
      (.Add (.VarIr .Var) .Var)
    )

example : [("x", 3)] ⊢ LET "x" = "x" * 2 IN "x" + "x" ⇓ 12 :=
  .Let
    (.Mul .Var .Int)
    (.Add .Var .Var)
