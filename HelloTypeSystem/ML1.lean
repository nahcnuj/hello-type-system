import HelloTypeSystem.Basic

namespace HelloTypeSystem

/-!
# 整数・真偽値式の評価 ML1
\[基礎概念,§3.1]
-/
namespace ML1

/--
ML1における値の集合
$$\begin{align*}
\mathbb{Z} \ni \MV{i} & \\\\
\\{\TT{true},\TT{false}\\} \ni \MV{b} & \\\\
\Set{Value} \ni \MV{v} &{}::= \MV{i} \mid \MV{b} \\\\
\end{align*}$$
-/
inductive Value
  | Z (i : Int)
  | B (b : Bool)
  deriving DecidableEq

instance : OfNat Value n where
  ofNat := .Z n

instance : Coe Int Value where
  coe := .Z
instance : Coe Bool Value where
  coe := .B

/--
ML1における式の集合
$$\begin{align*}
\Set{Operator} \ni \MV{op} &{}::= \TT{+} \mid \TT{-} \mid \TT{\*} \mid \TT{<} \\\\
\Set{Expr} \ni \MV{e} &{}::= \MV{v} \mid \TT{$\MV{e}$ $\MV{op}$ $\MV{e}$} \mid \TT{if $\MV{e}$ then $\MV{e}$ else $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Expr
  | C (v : Value)
  | Add (lhs : Expr) (rhs : Expr)
  | Sub (lhs : Expr) (rhs : Expr)
  | Mul (lhs : Expr) (rhs : Expr)
  | LT (lhs : Expr) (rhs : Expr)
  | If (cond : Expr) (t : Expr) (f : Expr)

instance : OfNat Expr n where
  ofNat := .C (.Z n)

instance : Coe Value Expr where
  coe := .C
instance : Add Expr where
  add := .Add
instance : Sub Expr where
  sub := .Sub
instance : Mul Expr where
  mul := .Mul

/--
導出システムEvalML1における判断
-/
inductive Judgement where
  /--
  "$\TT{$\MV{i_1}$ plus $\MV{i_2}$ is $\MV{i_3}$}$"
  -/
  | Plus (i₁ i₂ : Int) {i₃ : Int} (h : i₁ + i₂ = i₃)
  /--
  "$\TT{$\MV{n_1}$ minus $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Minus (i₁ i₂ : Int) {i₃ : Int} (h : i₁ - i₂ = i₃)
  /--
  "$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Times (i₁ i₂ : Int) {i₃ : Int} (h : i₁ * i₂ = i₃)
  /--
  "$\TT{$\MV{i_1}$ less than $\MV{i_2}$ is $\MV{b}$}$"
  -/
  | LT (i₁ i₂ : Int) (b : Bool)
  /--
  "$\MV{e} \Evals \MV{v}$" means that the value of an expression $\MV{e}$ is $\MV{v}$.
  -/
  | Eval (e : Expr) (v : Value)

notation:50 e:51 " ⇓ " n:51  => Judgement.Eval e n

/--
導出システムEvalML1の導出規則

付帯条件はLeanのPropで表現している。
-/
inductive Derivation : Judgement → Type where
  | B_Plus {i₁ i₂ i₃ : Int} (h : i₁ + i₂ = i₃)
    : Derivation (.Plus i₁ i₂ h)
  | B_Minus {i₁ i₂ i₃ : Int} (h : i₁ - i₂ = i₃)
    : Derivation (.Minus i₁ i₂ h)
  | B_Times {i₁ i₂ i₃ : Int} (h : i₁ * i₂ = i₃)
    : Derivation (.Times i₁ i₂ h)
  | B_LTT {i₁ i₂ : Int} (h : i₁ < i₂)
    : Derivation (.LT i₁ i₂ true)
  | B_LTF {i₁ i₂ : Int} (h : ¬ i₁ < i₂)
    : Derivation (.LT i₁ i₂ false)
  | E_Int {i : Int}
    : Derivation (i ⇓ i)
  | E_Bool {b : Bool}
    : Derivation (b ⇓ b)
  | E_IfT {e₁ e₂ e₃: Expr} {v : Value} (c : Derivation (e₁ ⇓ true)) (t : Derivation (e₂ ⇓ v))
    : Derivation (.If e₁ e₂ e₃ ⇓ v)
  | E_IfF {e₁ e₂ e₃: Expr} {v : Value} (c : Derivation (e₁ ⇓ false)) (f : Derivation (e₃ ⇓ v))
    : Derivation (.If e₁ e₂ e₃ ⇓ v)
  | E_Plus {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ + i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (p : Derivation (.Plus i₁ i₂ h))
    : Derivation (e₁ + e₂ ⇓ i₃)
  | E_Minus {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ - i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (m : Derivation (.Minus i₁ i₂ h))
    : Derivation (e₁ - e₂ ⇓ i₃)
  | E_Times {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ * i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (t : Derivation (.Times i₁ i₂ h))
    : Derivation (e₁ * e₂ ⇓ i₃)
  | E_LT {e₁ e₂ : Expr} {i₁ i₂ : Int} {b : Bool} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (lt : Derivation (.LT i₁ i₂ b))
    : Derivation (.LT e₁ e₂ ⇓ b)

/--
与えられた判断が導出できるという命題
-/
inductive Derivable (𝒥 : Judgement) : Prop where
  | intro (h : Derivation 𝒥)

/--
導出の項が構築できたときは明らかに導出できるので型強制する
-/
instance {𝒥 : Judgement} : Coe (Derivation 𝒥) (Derivable 𝒥) where
  coe := Derivable.intro

end ML1

/-!
ML1の式を、\[意味論入門]の簡易命令型言語IMPのように算術式と真偽式に分けて定義してみる。
-/
namespace ML1'

/--
ML1′における算術式の集合
$$\begin{align*}
\mathbb{Z} \ni \MV{i} & \\\\
\Set{AExpr} \ni \MV{a} &{}::= \MV{i} \mid \TT{$\MV{a}$ + $\MV{a}$} \mid \TT{$\MV{a}$ - $\MV{a}$} \mid \TT{$\MV{a}$ * $\MV{a}$} \\\\
\end{align*}$$
-/
inductive AExpr
  | C (i : Int)
  | Add (lhs : AExpr) (rhs : AExpr)
  | Sub (lhs : AExpr) (rhs : AExpr)
  | Mul (lhs : AExpr) (rhs : AExpr)

/--
ML1′における真偽式の集合
$$\begin{align*}
\Set{BExpr} \ni \MV{b} &{}::= \TT{true} \mid \TT{false} \mid \TT{$\MV{a}$ < $\MV{a}$} \\\\
\end{align*}$$
-/
inductive BExpr
  | C (b : Bool)
  | LT (lhs : AExpr) (rhs : AExpr)

/--
ML1′における式の集合
$$\begin{align*}
\Set{Expr} \ni \MV{e} &{}::= \MV{a} \mid \MV{b} \mid \TT{if $\MV{b}$ then $\MV{e}$ else $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Expr
  | A (a : AExpr)
  | B (b : BExpr)
  | If (cond : BExpr) (t : Expr) (f : Expr)

namespace ML1'
