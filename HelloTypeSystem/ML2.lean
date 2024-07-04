import HelloTypeSystem.Util
import HelloTypeSystem.ML1

namespace HelloTypeSystem

/-!
# 定義、変数束縛と環境 ML2
\[基礎概念,4章]
-/
namespace ML2
open HelloTypeSystem.ML1 (Value)

abbrev Error := Unit
private def error : Error := ()

abbrev Result := Error ⊕ Value

instance : OfNat Result n where
  ofNat := .inr (.Z n)
instance : Coe Value Result where
  coe := .inr
instance : Coe Error Result where
  coe := .inl

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
notation e₁ " ? " e₂ " : " e₃ => Expr.If e₁ e₂ e₃
notation "LET " x:max " = " e₁ " IN " e₂ => Expr.Let x e₁ e₂

/--
式に含まれる自由変数の集合
-/
def Expr.fv : Expr → Set ML2.Var
  | .Lit _        => ∅
  | .Var x        => { x }
  | .Add e₁ e₂    => e₁.fv ∪ e₂.fv
  | .Sub e₁ e₂    => e₁.fv ∪ e₂.fv
  | .Mul e₁ e₂    => e₁.fv ∪ e₂.fv
  | .LT  e₁ e₂    => e₁.fv ∪ e₂.fv
  | .If  e₁ e₂ e₃ => e₁.fv ∪ e₂.fv ∪ e₃.fv
  | .Let x e₁ e₂  => e₁.fv ∪ (e₂.fv \ { x })

/--
環境
$$\Set{Env} \ni \MV{\mathcal{E}} ::= \varnothing \mid {\MV{\mathcal{E}},\\,\TT{$\MV{x}$=$\MV{v}$}}$$
$\MV{\mathcal{E}},\\,\TT{$\MV{x}$=$\MV{v}$}$はLeanの`List (Var × Value)`で`(x, v) :: E`とする（consの都合で逆向きになっている）。
-/
abbrev Env := List (Var × Value)

/--
環境中で束縛されている変数の集合
-/
def Env.dom : Env → Set ML2.Var
  | []            => ∅
  | (x, _) :: env => Env.dom env ∪ { x }

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
  | LTT {i₁ i₂: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : i₁ < i₂ := by trivial)
    : Evaluation E (.LT e₁ e₂) true
  | LTF {i₁ i₂: Int} (d₁ : Evaluation E e₁ i₁) (d₂ : Evaluation E e₂ i₂) (h : ¬ i₁ < i₂ := by trivial)
    : Evaluation E (.LT e₁ e₂) false
  | IfT {v₂ : Value} (dc : Evaluation E e₁ true) (dt : Evaluation E e₂ v₂)
    : Evaluation E (e₁ ? e₂ : e₃) v₂
  | IfF {v₃ : Value} (dc : Evaluation E e₁ false) (df : Evaluation E e₃ v₃)
    : Evaluation E (e₁ ? e₂ : e₃) v₃
  | Let {v₁ v₂ : Value} (d₁ : Evaluation E e₁ v₁) (d₂ : Evaluation ((x, v₁) :: E) e₂ v₂)
    : Evaluation E (LET x = e₁ IN e₂) v₂

  | AddBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e + _) error
  | AddBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ + e) error
  | AddErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e + _) ε
  | AddErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ + e) ε

  | SubBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e - _) error
  | SubBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ - e) error
  | SubErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e - _) ε
  | SubErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ - e) ε

  | MulBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e * _) error
  | MulBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ * e) error
  | MulErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e * _) ε
  | MulErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ * e) ε

  | LTBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (.LT e _) error
  | LTBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (.LT _ e) error
  | LTErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (.LT e _) ε
  | LTErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (.LT _ e) ε

  | IfInt (d : Evaluation E e (.inr (.Z i)))
    : Evaluation E (.If e _ _) error
  | IfErr (d : Evaluation E e (.inl ε))
    : Evaluation E (.If e _ _) ε
  | IfTErr {ε₂ : Error} (dc : Evaluation E e₁ true) (dt : Evaluation E e₂ ε₂)
    : Evaluation E (e₁ ? e₂ : e₃) ε₂
  | IfFErr {ε₃ : Error} (dc : Evaluation E e₁ false) (df : Evaluation E e₃ ε₃)
    : Evaluation E (e₁ ? e₂ : e₃) ε₃

  | LetBindingErr {ε₁ : Error} (d₁ : Evaluation E e₁ ε₁)
    : Evaluation E (LET x = e₁ IN _) ε₁
  | LetExprErr {v₁ : Value} {ε₂ : Error} (d₁ : Evaluation E e₁ v₁) (d₂ : Evaluation ((x, v₁) :: E) e₂ ε₂)
    : Evaluation E (LET x = e₁ IN e₂) ε₂

private def Expr.eval_aux (expr : Expr) (env : Env) (bounded : expr.fv ⊆ env.dom) : (r : Result) × (Evaluation env expr r) :=
  match expr with
  | Lit v =>
      match v with
      | .Z i => ⟨i, .Int⟩
      | .B b => ⟨b, .Bool⟩
  | Var x =>
      match env with
      | [] => absurd (bounded x rfl) id
      | ⟨y, v⟩ :: (env' : Env) =>
          if h : y = x then
            ⟨v, h ▸ .Var⟩
          else
            let bounded' : (Var x).fv ⊆ env'.dom :=
              fun a h' => Or.resolve_right (bounded a h') (
                fun h'' : a ∈ { y } => absurd (singleton_mem_uniq <| h' ▸ h'') h
              )
            let ⟨.inr v, d⟩ := Expr.eval_aux (Var x) env' bounded'
            ⟨v, .VarIr d⟩
  | Add e₁ e₂ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h => bounded x (Or.inl h))
      let ⟨r₂, d₂⟩ := e₂.eval_aux env (fun x h => bounded x (Or.inr h))
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ + i₂, .Add d₁ d₂⟩
      | .inr (.B b₁), _            => ⟨error,   .AddBoolL d₁⟩
      | .inl ε₁,      _            => ⟨ε₁,      .AddErrL d₁⟩
      | _,            .inr (.B b₂) => ⟨error,   .AddBoolR d₂⟩
      | _,            .inl ε₂      => ⟨ε₂,      .AddErrR d₂⟩
  | Sub e₁ e₂ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h => bounded x (Or.inl h))
      let ⟨r₂, d₂⟩ := e₂.eval_aux env (fun x h => bounded x (Or.inr h))
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ - i₂, .Sub d₁ d₂⟩
      | .inr (.B b₁), _            => ⟨error,   .SubBoolL d₁⟩
      | .inl ε₁,      _            => ⟨ε₁,      .SubErrL d₁⟩
      | _,            .inr (.B b₂) => ⟨error,   .SubBoolR d₂⟩
      | _,            .inl ε₂      => ⟨ε₂,      .SubErrR d₂⟩
  | Mul e₁ e₂ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h => bounded x (Or.inl h))
      let ⟨r₂, d₂⟩ := e₂.eval_aux env (fun x h => bounded x (Or.inr h))
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ * i₂, .Mul d₁ d₂⟩
      | .inr (.B b₁), _            => ⟨error,   .MulBoolL d₁⟩
      | .inl ε₁,      _            => ⟨ε₁,      .MulErrL d₁⟩
      | _,            .inr (.B b₂) => ⟨error,   .MulBoolR d₂⟩
      | _,            .inl ε₂      => ⟨ε₂,      .MulErrR d₂⟩
  | LT e₁ e₂ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h => bounded x (Or.inl h))
      let ⟨r₂, d₂⟩ := e₂.eval_aux env (fun x h => bounded x (Or.inr h))
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) =>
          if h : i₁ < i₂ then
            ⟨true, .LTT d₁ d₂ h⟩
          else
            ⟨false, .LTF d₁ d₂ h⟩
      | .inr (.B b₁), _            => ⟨error, .LTBoolL d₁⟩
      | .inl ε₁,      _            => ⟨ε₁,    .LTErrL d₁⟩
      | _,            .inr (.B b₂) => ⟨error, .LTBoolR d₂⟩
      | _,            .inl ε₂      => ⟨ε₂,    .LTErrR d₂⟩
  | If e₁ e₂ e₃ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h => bounded x (Or.inl (Or.inl h)))
      match r₁ with
      | .inr (.B true) =>
          let ⟨r₂, d₂⟩ := e₂.eval_aux env (fun x h => bounded x (Or.inl (Or.inr h)))
          match r₂ with
          | .inr v => ⟨v, .IfT d₁ d₂⟩
          | .inl ε => ⟨ε, .IfTErr d₁ d₂⟩
      | .inr (.B false) =>
          let ⟨r₃, d₃⟩ := e₃.eval_aux env (fun x h => bounded x (Or.inr h))
          match r₃ with
          | .inr v => ⟨v, .IfF d₁ d₃⟩
          | .inl ε => ⟨ε, .IfFErr d₁ d₃⟩
      | .inr (.Z _) => ⟨error, .IfInt d₁⟩
      | .inl ε => ⟨ε, .IfErr d₁⟩
  | Let x e₁ e₂ =>
      let ⟨r₁, d₁⟩ := e₁.eval_aux env (fun x h₁ => bounded x (Or.inl h₁))
      match r₁ with
      | .inr v =>
          have : e₂.fv ⊆ Env.dom ((x, v) :: env) :=
            fun y h₂ =>
              if _ : x = y then
                Or.inr (by trivial)
              else
                have : y ∈ e₂.fv \ {x} := And.intro h₂ (fun _ => by contradiction)
                Or.inl (bounded y (Or.inr this))
          let ⟨r₂, d₂⟩ := e₂.eval_aux ((x, v) :: env) this
          match r₂ with
          | .inr v => ⟨v, .Let d₁ d₂⟩
          | .inl ε => ⟨ε, .LetExprErr d₁ d₂⟩
      | .inl ε => ⟨ε, .LetBindingErr d₁⟩

/--
`eval`はML2式`e`を評価してその結果を返します。
-/
def Expr.eval (e : Expr) (empty : e.fv = ∅) : Result := (e.eval_aux [] fun _ h => (empty ▸ h : _ ∈ ∅)).fst
