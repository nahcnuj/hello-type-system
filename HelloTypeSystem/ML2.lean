import HelloTypeSystem.ML1

namespace HelloTypeSystem

/-!
# 定義、変数束縛と環境 ML2
\[基礎概念,4章]
-/
namespace ML2
open HelloTypeSystem.ML1 (Value Error Result)

/--
変数名

$$\Set{Var} \ni \MV{x}$$
-/
abbrev Var := String

/--
ML2における式
$$\begin{align*}
\Set{Operator} \ni \MV{op} &{}::= \TT{+} \mid \TT{-} \mid \TT{\*} \mid \TT{<} \\\\
\Set{Expr} \ni \MV{e} &{}::= \MV{v} \mid \MV{x} \mid \TT{$\MV{e}$ $\MV{op}$ $\MV{e}$} \mid \TT{if $\MV{e}$ then $\MV{e}$ else $\MV{e}$} \mid \TT{let $\MV{x}$ = $\MV{e}$ in $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Expr
  | Lit (v : Value)
  | Var (x : Var)
  | Add (e₁ e₂ : Expr)
  | Sub (e₁ e₂ : Expr)
  | Mul (e₁ e₂ : Expr)
  | LT (e₁ e₂ : Expr)
  | If (e₁ e₂ e₃ : Expr)
  | Let (x : Var) (v : Expr) (e : Expr)
instance : OfNat Expr n where
  ofNat := Expr.Lit <| Value.Z <| Int.ofNat <| n
instance : Coe Value Expr where
  coe := Expr.Lit
instance : Coe Var Expr where
  coe := Expr.Var
instance : Add Expr where
  add := Expr.Add
instance : Sub Expr where
  sub := Expr.Sub
instance : Mul Expr where
  mul := Expr.Mul
notation e₁ " < " e₂ => Expr.LT e₁ e₂
notation e₁ " ? " e₂ " : " e₃ => Expr.If e₁ e₂ e₃
notation "LET " x:max " = " e₁ " IN " e₂ => Expr.Let x e₁ e₂

/--
環境
$$\Set{Env} \ni \MV{\mathcal{E}} ::= \varnothing \mid {\MV{\mathcal{E}},\\,\TT{$\MV{x}$=$\MV{v}$}}$$
$\MV{\mathcal{E}},\\,\TT{$\MV{x}$=$\MV{v}$}$はLeanの`List (Var × Value)`で`(x, v) :: E`とする（consの都合で逆向きになっている）。
-/
abbrev Env := List (Var × Value)

/--
ML2式の評価規則
"$\MV{\mathcal{E}} \vdash \MV{e} \Evals \MV{r}$" means that the result of an expression $\MV{e}$ is $\MV{r}$ in the environment $\MV{\mathcal{E}}$.
-/
inductive Evaluation : Env → Expr → Result → Type
  | Int {i : Int}
    : Evaluation E i i
  | Bool {b : Bool}
    : Evaluation E b b
  | Var {x : Var} {v : Value}
    : Evaluation ((x, v) :: E) x v
  | VarIr {x y : Var} {w : Value} {v : Value} (d : Evaluation E x v) (hne : y ≠ x := by trivial)
    : Evaluation ((y, w) :: E) x v
  | Add {i₁ i₂ i₃: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : i₁ + i₂ = i₃ := by trivial)
    : Evaluation E (e₁ + e₂) i₃
  | Sub {i₁ i₂ i₃: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : i₁ - i₂ = i₃ := by trivial)
    : Evaluation E (e₁ - e₂) i₃
  | Mul {i₁ i₂ i₃: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : i₁ * i₂ = i₃ := by trivial)
    : Evaluation E (e₁ * e₂) i₃
  | LTT {i₁ i₂ i₃: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : i₁ < i₂ := by trivial)
    : Evaluation E (e₁ < e₂) true
  | LTF {i₁ i₂ i₃: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : ¬ i₁ < i₂ := by trivial)
    : Evaluation E (e₁ < e₂) false
  | IfT {v₂ : Value} (dc : Evaluation E e₁ true) (dt : Evaluation E e₂ v₂)
    : Evaluation E (e₁ ? e₂ : e₃) v₂
  | IfF {v₃ : Value} (dc : Evaluation E e₁ false) (df : Evaluation E e₃ v₃)
    : Evaluation E (e₁ ? e₂ : e₃) v₃
  | Let {v₁ v₂ : Value} (d₁ : Evaluation E e₁ v₁) (d₂ : Evaluation ((x, v₁) :: E) e₂ v₂)
    : Evaluation E (LET x = e₁ IN e₂) v₂
