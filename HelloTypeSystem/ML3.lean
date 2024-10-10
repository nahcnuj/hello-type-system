import HelloTypeSystem.Util
import HelloTypeSystem.ML1
import HelloTypeSystem.ML2

namespace HelloTypeSystem

/-!
# 関数と再帰 ML3
\[基礎概念,5章]
-/
namespace ML3

/-!
$$\begin{align*}
\mathbb{Z} \ni \MV{i} \phantom{{}::={}}& \\\\
\\{\TT{true},\TT{false}\\} \ni \MV{b} \phantom{{}::={}}& \\\\
\Set{Value} \ni \MV{v} ::={}& \MV{i} \mid \MV{b} \mid \Cls(\MV{\mathcal{E}}, \MV{x}, \MV{e}) \mid \Fix(\MV{x}, \MV{\mathcal{E}}, \MV{x}, \MV{e}) \\\\
\Set{Env} \ni \MV{\mathcal{E}} ::={}& \varnothing \mid {\MV{\mathcal{E}},\\,\TT{$\MV{x}$=$\MV{v}$}} \\\\
\Set{Prim} \ni \MV{op} ::={}& \TT{+} \mid \TT{-} \mid \TT{\*} \mid \TT{<} \\\\
\Set{Expr} \ni \MV{e} ::={}&
        \MV{i} \mid \MV{b} \mid \MV{x} \mid \TT{$\MV{e}$ $\MV{op}$ $\MV{e}$} \mid \TT{if $\MV{e}$ then $\MV{e}$ else $\MV{e}$} \\\\
{}\mid{}&\TT{let $\MV{x}$ = $\MV{e}$ in $\MV{e}$} %\mid \TT{let rec $\MV{x}$ = fun $\MV{x}$ → $\MV{e}$ in $\MV{e}$}
\\\\
{}\mid{}&\TT{fun $\MV{x}$ → $\MV{e}$} \mid \TT{$\MV{e}$ $\MV{e}$} \\\\
\end{align*}$$
-/

abbrev VarName := ML2.Var

mutual
  /--
  ML3における値の集合
  -/
  inductive Value
    | Z   (i : Int)
    | B   (b : Bool)
    | Cls (E : Env) (x : VarName) (e : Expr)
--  | Fix (E : Env) (f : VarName) (x : VarName) (e : Expr)

  /--
  環境
  -/
  inductive Env
    | nil
    | cons (entry : VarName × Value) (tail : Env)

  /--
  ML3式
  -/
  inductive Expr
    | Z      (i : Int)
    | B      (b : Bool)
    | Var    (x : VarName)
    | Add    (e₁ e₂ : Expr)
    | Sub    (e₁ e₂ : Expr)
    | Mul    (e₁ e₂ : Expr)
    | LT     (e₁ e₂ : Expr)
    | If     (e₁ e₂ e₃ : Expr)
    | Let    (x : VarName) (v : Expr) (e : Expr)
    | Fn     (x : VarName) (e : Expr)
    | App    (e₁ e₂ : Expr)
--  | LetRec (f : VarName) (x : VarName) (e : Expr) (e' : Expr)
end

instance : OfNat Value n where
  ofNat := .Z n
instance : Coe Int Value where
  coe := .Z
instance : Coe Bool Value where
  coe := .B

private def Env.toList : Env → List (VarName × Value)
  | nil       => .nil
  | cons e es => .cons e es.toList
instance : Coe Env (List (VarName × Value)) where
  coe := Env.toList
private def Env.ofList : List (VarName × Value) → Env
  | .nil       => .nil
  | .cons e es => .cons e (Env.ofList es)
instance : Coe (List (VarName × Value)) Env where
  coe := Env.ofList

/--
環境中で束縛されている変数の集合
-/
@[reducible]
def Env.dom : Env → Set VarName
  | nil             => ∅
  | cons (x, _) env => Env.dom env ∪ { x }
theorem Env.dom.cons : (Env.cons (x, v) env').dom = env'.dom ∪ { x } := by simp [Env.dom]

instance : OfNat Expr n where
  ofNat := Expr.Z <| Int.ofNat <| n
instance : Coe Int Expr where
  coe := .Z
instance : Coe Bool Expr where
  coe := Expr.B
instance : Coe VarName Expr where
  coe := Expr.Var
instance : Add Expr where
  add := Expr.Add
instance : Sub Expr where
  sub := Expr.Sub
instance : Mul Expr where
  mul := Expr.Mul

def Expr.size : Expr → Nat
  | .Z _     => 1
  | .B _     => 1
  | .Var _   => 1
  | .Add e₁ e₂  => e₁.size + e₂.size + 1
  | .Sub e₁ e₂  => e₁.size + e₂.size + 1
  | .Mul e₁ e₂  => e₁.size + e₂.size + 1
  | .LT e₁ e₂  => e₁.size + e₂.size + 1
  | .If e₁ e₂ e₃ => e₁.size + e₂.size + e₃.size + 1
  | .Let _ e₁ e₂ => e₁.size + e₂.size + 1
  | .Fn _ e => e.size + 1
  | .App e₁ e₂ => e₁.size + e₂.size + 1
-- instance : SizeOf Expr where
--   sizeOf := Expr.size

/--
式に含まれる自由変数の集合
-/
def Expr.fv : Expr → Set VarName
  | .Z _          => ∅
  | .B _          => ∅
  | .Var x        => { x }
  | .Add e₁ e₂    => e₁.fv ∪ e₂.fv
  | .Sub e₁ e₂    => e₁.fv ∪ e₂.fv
  | .Mul e₁ e₂    => e₁.fv ∪ e₂.fv
  | .LT  e₁ e₂    => e₁.fv ∪ e₂.fv
  | .If  e₁ e₂ e₃ => e₁.fv ∪ e₂.fv ∪ e₃.fv
  | .Let x e₁ e₂  => e₁.fv ∪ (e₂.fv \ { x })
  | .Fn  x e      => e.fv \ { x }
  | .App e₁ e₂    => e₁.fv ∪ e₂.fv

/-
In Lean 4.9, “Functions defined by well-founded recursion are now irreducible by default.”
according to https://lean-lang.org/blog/2024-7-1-lean-490/
-/
theorem Expr.fv.Int : (Expr.Z i).fv = ∅ := by simp [Expr.fv]
theorem Expr.fv.Var : (Expr.Var x).fv = { x } := by simp [Expr.fv]
theorem Expr.fv.Add : (Expr.Add e₁ e₂).fv = e₁.fv ∪ e₂.fv := by simp [Expr.fv]
theorem Expr.fv.Sub : (Expr.Sub e₁ e₂).fv = e₁.fv ∪ e₂.fv := by simp [Expr.fv]
theorem Expr.fv.Mul : (Expr.Mul e₁ e₂).fv = e₁.fv ∪ e₂.fv := by simp [Expr.fv]
theorem Expr.fv.LT  : (Expr.LT  e₁ e₂).fv = e₁.fv ∪ e₂.fv := by simp [Expr.fv]
theorem Expr.fv.If  : (Expr.If  e₁ e₂ e₃).fv = e₁.fv ∪ e₂.fv ∪ e₃.fv := by simp [Expr.fv]
theorem Expr.fv.Let : (Expr.Let x e₁ e₂).fv = e₁.fv ∪ (e₂.fv \ { x }) := by simp [Expr.fv]
theorem Expr.fv.Fn  : (Expr.Fn  x e).fv = e.fv \ { x } := by simp [Expr.fv]
theorem Expr.fv.App : (Expr.App e₁ e₂).fv = e₁.fv ∪ e₂.fv := by simp [Expr.fv]

abbrev Error := ML2.Error
private def error : Error := ()

abbrev Result := Error ⊕ Value

instance : OfNat Result n where
  ofNat := .inr (.Z n)
instance : Coe Value Result where
  coe := .inr
instance : Coe Error Result where
  coe := .inl

/--
ML3式の評価 $\MV{\mathcal{E}} \vdash \MV{e} \Evals \MV{r}$ の導出規則
-/
inductive Evaluation : Env → Expr → Result → Type
  | Int {i : Int}
    : Evaluation E i i
  | Bool {b : Bool}
    : Evaluation E b b
  | Var {E : Env} {x : VarName} {v : Value}
    : Evaluation (E.cons (x, v)) x v
  | VarIr {x y : VarName} {v w : Value} (d : Evaluation E x v) (hne : y ≠ x := by trivial)
    : Evaluation (E.cons (y, w)) x v
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
  | IfT (dc : Evaluation E e₁ (.inr true)) (dt : Evaluation E e₂ (.inr v₂))
    : Evaluation E (.If e₁ e₂ e₃) v₂
  | IfF (dc : Evaluation E e₁ (.inr false)) (df : Evaluation E e₃ (.inr v₃))
    : Evaluation E (.If e₁ e₂ e₃) v₃
  | Let (d₁ : Evaluation E e₁ (.inr v₁)) (d₂ : Evaluation (E.cons (x, v₁)) e₂ (.inr v₂))
    : Evaluation E (.Let x e₁ e₂) v₂
  | Fn {E : Env} {x : VarName} {e : Expr}
    : Evaluation E (.Fn x e) (Value.Cls E x e)
  | App (d₁ : Evaluation E e₁ (.inr (.Cls E' x e₀))) (d₂ : Evaluation E e₂ (.inr v₂)) (d : Evaluation (E'.cons (x, v₂)) e₀ (.inr v))
    : Evaluation E (.App e₁ e₂) v

  | AddBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e + _) error
  | AddBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ + e) error
  | AddClsL (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (e + _) error
  | AddClsR (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (_ + e) error
  | AddErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e + _) ε
  | AddErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ + e) ε

  | SubBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e - _) error
  | SubBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ - e) error
  | SubClsL (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (e - _) error
  | SubClsR (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (_ - e) error
  | SubErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e - _) ε
  | SubErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ - e) ε

  | MulBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (e * _) error
  | MulBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (_ * e) error
  | MulClsL (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (e * _) error
  | MulClsR (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (_ * e) error
  | MulErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (e * _) ε
  | MulErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (_ * e) ε

  | LTBoolL (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (.LT e _) error
  | LTBoolR (d : Evaluation E e (.inr (.B b)))
    : Evaluation E (.LT _ e) error
  | LTClsL (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (.LT e _) error
  | LTClsR (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (.LT _ e) error
  | LTErrL (d : Evaluation E e (.inl ε))
    : Evaluation E (.LT e _) ε
  | LTErrR (d : Evaluation E e (.inl ε))
    : Evaluation E (.LT _ e) ε

  | IfInt (d : Evaluation E e (.inr (.Z i)))
    : Evaluation E (.If e ..) error
  | IfCls (d : Evaluation E e (.inr (.Cls E' x e₀)))
    : Evaluation E (.If e ..) error
  | IfErr (d : Evaluation E e (.inl ε))
    : Evaluation E (.If e ..) ε
  | IfTErr {ε₂ : Error} (dc : Evaluation E e₁ (.inr true)) (dt : Evaluation E e₂ (.inl ε₂))
    : Evaluation E (.If e₁ e₂ _) ε₂
  | IfFErr {ε₃ : Error} (dc : Evaluation E e₁ (.inr false)) (df : Evaluation E e₃ (.inl ε₃))
    : Evaluation E (.If e₁ _ e₃) ε₃

  | LetBindingErr {ε₁ : Error} (d₁ : Evaluation E e₁ (.inl ε₁))
    : Evaluation E (.Let x e₁ _) ε₁
  | LetExprErr {ε₂ : Error} (d₁ : Evaluation E e₁ (.inr v₁)) (d₂ : Evaluation (Env.cons (x, v₁) E) e₂ (.inl ε₂))
    : Evaluation E (.Let x e₁ e₂) ε₂

  | AppIntL (d₁ : Evaluation E e₁ (.inr (.Z i)))
    : Evaluation E (.App e₁ _) error
  | AppBoolL (d₁ : Evaluation E e₁ (.inr (.B b)))
    : Evaluation E (.App e₁ _) error
  | AppErrL (d₁ : Evaluation E e₁ (.inl ε₁))
    : Evaluation E (.App e₁ _) ε₁
  | AppErrR (d₁ : Evaluation E e₁ (.inr (.Cls E' x e₀))) (d₂ : Evaluation E e₂ (.inl ε₂))
    : Evaluation E (.App e₁ e₂) ε₂
  | AppErrA (d₁ : Evaluation E e₁ (.inr (.Cls E' x e₀))) (d₂ : Evaluation E e₂ (.inr v₂)) (d : Evaluation (E'.cons (x, v₂)) e₀ (.inl ε))
    : Evaluation E (.App e₁ e₂) ε

/-
↓こんなに書いて（ML2からのコピペも多いが）から、教科書に式の構造に関する帰納法が使えないと書かれていることに気がついた...
（↓で詰んでいるように）Appの前提`e₀`がexprの部分式になっていないので再帰できないんですねぇ…。

axiom eval_det {env : Env} {expr : Expr} : Inhabited ((r : Result) × Evaluation env expr r)
noncomputable instance : Inhabited ((r : Result) × Evaluation env expr r) := eval_det

private partial def Expr.eval_aux (expr : Expr) (env : Env) (bounded : expr.fv ⊆ env.dom) : (r : Result) × Evaluation env expr r :=
  match expr with
  | Z i => ⟨i, .Int⟩
  | B b => ⟨b, .Bool⟩
  | Var x =>
      match env with
      | .nil =>
          absurd (bounded x (Expr.fv.Var ▸ rfl)) id
      | .cons ⟨y, v⟩ (env' : Env) =>
          if h : x = y then
            ⟨v, h ▸ .Var⟩
          else
            have bounded' : (Var x).fv ⊆ env'.dom :=
              fun a h' =>
                have : a ∈ env'.dom ∨ a ∈ {y} := (Env.dom.cons ▸ bounded) a h'
                Or.elim this
                  id
                  (fun h'' : a ∈ {y} =>
                    have hx := Singleton.mem_iff_eq_elem.mp (Expr.fv.Var ▸ h')
                    have hy := Singleton.mem_iff_eq_elem.mp h''
                    absurd (hy ▸ hx) h
                  )
            let ⟨.inr v, d⟩ := Expr.eval_aux (Var x) env' bounded'
            ⟨v, .VarIr d fun heq => absurd heq.symm h⟩
  | Add e₁ e₂ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (e₁.Add e₂).fv := Expr.fv.Add ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      let ⟨r₂, d₂⟩ :=
        have : e₂.fv ⊆ (e₁.Add e₂).fv := Expr.fv.Add ▸ Union.subset_intro_right
        eval_aux e₂ env (Subset.trans this bounded)
      match r₁, r₂ with
      | .inr (.Z i₁),   .inr (.Z i₂)   => ⟨i₁ + i₂, .Add d₁ d₂⟩
      | .inr (.B b₁),   _              => ⟨error,   .AddBoolL d₁⟩
      | .inr (.Cls ..), _              => ⟨error,   .AddClsL d₁⟩
      | .inl ε₁,        _              => ⟨ε₁,      .AddErrL d₁⟩
      | _,              .inr (.B b₂)   => ⟨error,   .AddBoolR d₂⟩
      | _,              .inr (.Cls ..) => ⟨error,   .AddClsR d₂⟩
      | _,              .inl ε₂        => ⟨ε₂,      .AddErrR d₂⟩
  | Sub e₁ e₂ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (e₁.Sub e₂).fv := Expr.fv.Sub ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      let ⟨r₂, d₂⟩ :=
        have : e₂.fv ⊆ (e₁.Sub e₂).fv := Expr.fv.Sub ▸ Union.subset_intro_right
        eval_aux e₂ env (Subset.trans this bounded)
      match r₁, r₂ with
      | .inr (.Z i₁),   .inr (.Z i₂)   => ⟨i₁ - i₂, .Sub d₁ d₂⟩
      | .inr (.B b₁),   _              => ⟨error,   .SubBoolL d₁⟩
      | .inr (.Cls ..), _              => ⟨error,   .SubClsL d₁⟩
      | .inl ε₁,        _              => ⟨ε₁,      .SubErrL d₁⟩
      | _,              .inr (.B b₂)   => ⟨error,   .SubBoolR d₂⟩
      | _,              .inr (.Cls ..) => ⟨error,   .SubClsR d₂⟩
      | _,              .inl ε₂        => ⟨ε₂,      .SubErrR d₂⟩
  | Mul e₁ e₂ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (e₁.Mul e₂).fv := Expr.fv.Mul ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      let ⟨r₂, d₂⟩ :=
        have : e₂.fv ⊆ (e₁.Mul e₂).fv := Expr.fv.Mul ▸ Union.subset_intro_right
        eval_aux e₂ env (Subset.trans this bounded)
      match r₁, r₂ with
      | .inr (.Z i₁),   .inr (.Z i₂)   => ⟨i₁ * i₂, .Mul d₁ d₂⟩
      | .inr (.B b₁),   _              => ⟨error,   .MulBoolL d₁⟩
      | .inr (.Cls ..), _              => ⟨error,   .MulClsL d₁⟩
      | .inl ε₁,        _              => ⟨ε₁,      .MulErrL d₁⟩
      | _,              .inr (.B b₂)   => ⟨error,   .MulBoolR d₂⟩
      | _,              .inr (.Cls ..) => ⟨error,   .MulClsR d₂⟩
      | _,              .inl ε₂        => ⟨ε₂,      .MulErrR d₂⟩
  | LT e₁ e₂ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (e₁.LT e₂).fv := Expr.fv.LT ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      let ⟨r₂, d₂⟩ :=
        have : e₂.fv ⊆ (e₁.LT e₂).fv := Expr.fv.LT ▸ Union.subset_intro_right
        eval_aux e₂ env (Subset.trans this bounded)
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) =>
          if h : i₁ < i₂
          then ⟨true,  .LTT d₁ d₂ h⟩
          else ⟨false, .LTF d₁ d₂ h⟩
      | .inr (.B b₁),   _              => ⟨error, .LTBoolL d₁⟩
      | .inr (.Cls ..), _              => ⟨error, .LTClsL d₁⟩
      | .inl ε₁,        _              => ⟨ε₁,    .LTErrL d₁⟩
      | _,              .inr (.B b₂)   => ⟨error, .LTBoolR d₂⟩
      | _,              .inr (.Cls ..) => ⟨error, .LTClsR d₂⟩
      | _,              .inl ε₂        => ⟨ε₂,    .LTErrR d₂⟩
  | If e₁ e₂ e₃ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      match r₁ with
      | .inr (.B true) =>
          let ⟨r₂, d₂⟩ :=
            have : e₂.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ (Subset.trans Union.subset_intro_left Union.subset_intro_right)
            eval_aux e₂ env (Subset.trans this bounded)
          match r₂ with
          | .inr v => ⟨v, .IfT    d₁ d₂⟩
          | .inl ε => ⟨ε, .IfTErr d₁ d₂⟩
      | .inr (.B false) =>
          let ⟨r₃, d₃⟩ :=
            have : e₃.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ (Subset.trans Union.subset_intro_right Union.subset_intro_right)
            eval_aux e₃ env (Subset.trans this bounded)
          match r₃ with
          | .inr v => ⟨v, .IfF d₁ d₃⟩
          | .inl ε => ⟨ε, .IfFErr d₁ d₃⟩
      | .inr (.Cls ..) => ⟨error, .IfCls d₁⟩
      | .inr (.Z _)    => ⟨error, .IfInt d₁⟩
      | .inl ε         => ⟨ε,     .IfErr d₁⟩
  | Let x e₁ e₂ =>
      let ⟨r₁, d₁⟩ :=
        have : e₁.fv ⊆ (Expr.Let x e₁ e₂).fv := Expr.fv.Let ▸ Union.subset_intro_left
        eval_aux e₁ env (Subset.trans this bounded)
      match r₁ with
      | .inr v =>
          let env' := Env.cons (x, v) env
          have bounded' : e₂.fv ⊆ env'.dom :=
            Env.dom.cons ▸ fun y h =>
              if heq : x = y
              then Or.inr (heq ▸ rfl)
              else Or.inl (bounded y (Expr.fv.Let ▸ Or.inr ⟨h, fun h => absurd h heq⟩))
          let ⟨r₂, d₂⟩ := e₂.eval_aux env' bounded'
          match r₂ with
          | .inr v => ⟨v, .Let d₁ d₂⟩
          | .inl ε => ⟨ε, .LetExprErr d₁ d₂⟩
      | .inl ε => ⟨ε, .LetBindingErr d₁⟩
  | Fn x e => ⟨Value.Cls env x e, .Fn⟩
  | App (.Fn x e₀) e₂ =>
      have h₀ : (Expr.Fn x e₀).fv ⊆ (Expr.App (Expr.Fn x e₀) e₂).fv := Expr.fv.App ▸ Union.subset_intro_left
      let ⟨.inr (.Cls E' ..), _⟩ := eval_aux (Expr.Fn x e₀) env (Subset.trans h₀ bounded)

      let ⟨r₂, d₂⟩ :=
        have : e₂.fv ⊆ (Expr.App (.Fn x e₀) e₂).fv := Expr.fv.App ▸ Union.subset_intro_right
        eval_aux e₂ env (Subset.trans this bounded)
      match r₂ with
      | .inr v₂ =>
          let env' := env.cons (x, v₂)

          have : env.dom ∪ { x } = (Env.cons (x, v₂) env).dom := by simp [Env.dom]
          have : e₀.fv \ { x } ⊆ (env.cons (x, v₂)).dom :=
            (this ▸ Union.subset_intro_left)
            |> Subset.trans bounded
            |> Subset.trans h₀
            |> (Expr.fv.Fn ▸ ·)
          have : e₀.fv ⊆ (env.cons (x, v₂)).dom := fun a he₀ =>
            if ha : a = x
            then ha ▸ Env.dom.cons ▸ Or.inr rfl
            else this a ⟨he₀, fun heq => absurd (Singleton.mem_iff_eq_elem.mp heq |> .symm) ha⟩

          let ⟨r, d⟩ :=
            eval_aux e₀ (env.cons (x, v₂)) this

          match r with
          | .inr v => ⟨v, .App .Fn d₂ d⟩
          | .inl ε => ⟨ε, .AppErrA .Fn d₂ d⟩
      | .inl ε₂ => ⟨ε₂, .AppErrR .Fn d₂⟩
  | App e₁ e₂ =>
      have h₀ : e₁.fv ⊆ (Expr.App e₁ e₂).fv := Expr.fv.App ▸ Union.subset_intro_left
      let ⟨r₁, d₁⟩ := eval_aux e₁ env (Subset.trans h₀ bounded)
      match e₁, r₁ with
      | .Fn x e₀, .inr (.Cls E' ..) =>
          let ⟨r₂, d₂⟩ :=
            have : e₂.fv ⊆ (Expr.App (.Fn x e₀) e₂).fv := Expr.fv.App ▸ Union.subset_intro_right
            eval_aux e₂ env (Subset.trans this bounded)

          match r₂ with
          | .inr v₂ =>
              let env' := env.cons (x, v₂)

              have : env.dom ∪ { x } = env'.dom := by simp [env', Env.dom]
              have : e₀.fv \ { x } ⊆ env'.dom :=
                (this ▸ Union.subset_intro_left)
                |> Subset.trans bounded
                |> Subset.trans h₀
                |> (Expr.fv.Fn ▸ ·)
              have : e₀.fv ⊆ env'.dom := fun a he₀ =>
                if ha : a = x
                then ha ▸ Env.dom.cons ▸ Or.inr rfl
                else this a ⟨he₀, fun heq => absurd (Singleton.mem_iff_eq_elem.mp heq |> .symm) ha⟩

              let ⟨r, d⟩ := eval_aux e₀ env' this
              match r with
              | .inr v => ⟨v, .App .Fn d₂ d⟩
              | .inl ε => ⟨ε, .AppErrA .Fn d₂ d⟩
          | .inl ε => ⟨ε, .AppErrR d₁ d₂⟩

      | .App .., .inr (.Cls E' x e₀) =>
          let ⟨r₂, d₂⟩ :=
            have : e₂.fv ⊆ (Expr.App _ e₂).fv := Expr.fv.App ▸ Union.subset_intro_right
            eval_aux e₂ env (Subset.trans this bounded)
          match r₂ with
          | .inr v₂ =>
              let ⟨r, d⟩ :=
                eval_aux e₀ (E'.cons (x, v₂)) sorry
              match r with
              | .inr v => ⟨v, .App d₁ d₂ d⟩
              | .inl ε => ⟨ε, .AppErrA d₁ d₂ d⟩
          | .inl ε => ⟨ε, .AppErrR d₁ d₂⟩

      | _, .inr (.Cls ..) => sorry
      | _, .inr (.Z _) => ⟨error, .AppIntL d₁⟩
      | _, .inr (.B _) => ⟨error, .AppBoolL d₁⟩
      | _, .inl ε => ⟨ε, .AppErrL d₁⟩
-/

/--
EvalML3における判断$\MV{\mathcal{E}} \vdash \MV{e} \Evals \MV{v}$の導出に関する帰納法
-/
def Evaluation.induction
  {motive : Env → Expr → Value → Sort _} -- P(E,e,v)
  (HInt   : ∀ {E : Env} {i : ℤ}, motive E i i)
  (HBool  : ∀ {E : Env} {b : 𝔹}, motive E b b)
  (HVar   : ∀ {E : Env} {x : VarName} {v : Value}, motive (E.cons (x, v)) x v)
  (HVarIr : ∀ {E : Env} {x y : VarName} {v₁ v₂ : Value}, y ≠ x → motive E x v₂ → motive (E.cons (y, v₁)) x v₂)
  (HAdd   : ∀ {E : Env} {e₁ e₂ : Expr} {i₁ i₂ i₃ : ℤ}, motive E e₁ i₁ → motive E e₂ i₂ → i₁ + i₂ = i₃ → motive E (e₁ + e₂) i₃)
  (HSub   : ∀ {E : Env} {e₁ e₂ : Expr} {i₁ i₂ i₃ : ℤ}, motive E e₁ i₁ → motive E e₂ i₂ → i₁ - i₂ = i₃ → motive E (e₁ - e₂) i₃)
  (HMul   : ∀ {E : Env} {e₁ e₂ : Expr} {i₁ i₂ i₃ : ℤ}, motive E e₁ i₁ → motive E e₂ i₂ → i₁ * i₂ = i₃ → motive E (e₁ * e₂) i₃)
  (HLTT   : ∀ {E : Env} {e₁ e₂ : Expr} {i₁ i₂ : ℤ}, motive E e₁ i₁ → motive E e₂ i₂ → i₁ < i₂ → motive E (e₁.LT e₂) true)
  (HLTF   : ∀ {E : Env} {e₁ e₂ : Expr} {i₁ i₂ : ℤ}, motive E e₁ i₁ → motive E e₂ i₂ → ¬ i₁ < i₂ → motive E (e₁.LT e₂) false)
  (HIfT   : ∀ {E : Env} {e₁ e₂ e₃ : Expr} {v : Value}, motive E e₁ true → motive E e₂ v → motive E (.If e₁ e₂ e₃) v)
  (HIfF   : ∀ {E : Env} {e₁ e₂ e₃ : Expr} {v : Value}, motive E e₁ false → motive E e₃ v → motive E (.If e₁ e₂ e₃) v)
  (HLet   : ∀ {E : Env} {e₁ e₂ : Expr} {x : VarName} {v v₁ : Value}, motive E e₁ v₁ → motive (E.cons (x, v₁)) e₂ v → motive E (.Let x e₁ e₂) v)
  (HFun   : ∀ {E : Env} {x : VarName} {e : Expr}, motive E (.Fn x e) (.Cls E x e))
  (HApp   : ∀ {E E': Env} {e₀ e₁ e₂ : Expr} {x : VarName} {v v₂ : Value}, motive E e₁ (.Cls E' x e₀) → motive E e₂ v₂ → motive (E'.cons (x, v₂)) e₀ v → motive E (.App e₁ e₂) v)
  {E : Env} {e : Expr} {v : Value}
: Evaluation E e v → motive E e v := fun d =>
  match d with
  | .Int  => HInt
  | .Bool => HBool
  | .Var  => HVar
  | .VarIr d hne =>
      have d := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d
      HVarIr hne d
  | .Add d₁ d₂ h =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HAdd d₁ d₂ h
  | .Sub d₁ d₂ h =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HSub d₁ d₂ h
  | .Mul d₁ d₂ h =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HMul d₁ d₂ h
  | .LTT d₁ d₂ h =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HLTT d₁ d₂ h
  | .LTF d₁ d₂ h =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HLTF d₁ d₂ h
  | .IfT d₁ d₂ =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HIfT d₁ d₂
  | .IfF d₁ d₃ =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₃ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₃
      HIfF d₁ d₃
  | .Let d₁ d₂ =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      HLet d₁ d₂
  | .Fn => HFun
  | .App d₁ d₂ d =>
      have d₁ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₁
      have d₂ := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d₂
      have d  := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d
      HApp d₁ d₂ d

/--
TypingML3が扱う型
$$\Set{Types} \ni \MV{\tau} ::= \TT{int} \mid \TT{bool} \mid \TT{$\MV{\tau}$ → $\MV{\tau}$}$$
-/
inductive Types where
  | Int
  | Bool
  | Fn (τ₁ τ₂ : Types)
  /-- 型変数$\MV{\alpha}$-/
  | Var (α : VarName)
  deriving DecidableEq, Repr

-- def Types.depth : Types → Nat
--   | .Int      => 0
--   | .Bool     => 0
--   | .Var _    => 1
--   | .Fn τ₁ τ₂ => 1 + Nat.max τ₁.depth τ₂.depth

def Types.fv : Types → List VarName
  | .Int      => []
  | .Bool     => []
  | .Var α    => [ α ]
  | .Fn τ₁ τ₂ => τ₂.fv ++ τ₁.fv
theorem Types.fv.Int : Types.fv .Int = ∅ := by simp [Types.fv]
theorem Types.fv.Var : Types.fv (.Var α) = [ α ] := by simp [Types.fv]
theorem Types.fv.Fn : Types.fv (.Fn τ₁ τ₂) = τ₂.fv ++ τ₁.fv := by simp [Types.fv]

def Types.fv' : Types → Set VarName
  | .Int      => ∅
  | .Bool     => ∅
  | .Var α    => { α }
  | .Fn τ₁ τ₂ => τ₁.fv' ∪ τ₂.fv'

/--
型環境
-/
abbrev TypeEnv := List (VarName × Types)

/--
型環境において型宣言されている変数の集合
-/
def TypeEnv.dom : TypeEnv → Set VarName
  | []          => ∅
  | (x, _) :: Γ => TypeEnv.dom Γ ∪ { x }
theorem TypeEnv.dom.nil  : TypeEnv.dom [] = ∅ := by simp [TypeEnv.dom]
theorem TypeEnv.dom.cons : TypeEnv.dom ((x, τ) :: (Γ' : TypeEnv)) = Γ'.dom ∪ { x } := by simp [TypeEnv.dom]

/--
ML3式の型付け規則

"$\MV{\Gamma}\vdash\MV{e}\colon\MV{\tau}$" means that the type of the expression $\MV{e}$ is $\MV{\tau}$ in the type environment $\MV{\Gamma}$.
-/
inductive Typed : TypeEnv → Expr → Types → Prop
  | Int {i : Int}
    : Typed Γ i .Int
  | Bool {b : Bool}
    : Typed Γ b .Bool
  | Var {x : VarName} {τ : Types}
    : Typed ((x, τ) :: Γ) x τ
  | VarIr {x y : VarName} {τ : Types} (d : Typed Γ x τ) (hne : y ≠ x := by trivial)
    : Typed ((y, _) :: Γ) x τ
  | Add {e₁ e₂ : Expr} (d₁ : Typed Γ e₁ .Int) (d₂ : Typed Γ e₂ .Int)
    : Typed Γ (e₁ + e₂) .Int
  | Sub {e₁ e₂ : Expr} (d₁ : Typed Γ e₁ .Int) (d₂ : Typed Γ e₂ .Int)
    : Typed Γ (e₁ - e₂) .Int
  | Mul {e₁ e₂ : Expr} (d₁ : Typed Γ e₁ .Int) (d₂ : Typed Γ e₂ .Int)
    : Typed Γ (e₁ * e₂) .Int
  | LT {e₁ e₂ : Expr} (d₁ : Typed Γ e₁ .Int) (d₂ : Typed Γ e₂ .Int)
    : Typed Γ (.LT e₁ e₂) .Bool
  | If {e₁ e₂ e₃ : Expr} (d₁ : Typed Γ e₁ .Bool) (d₂ : Typed Γ e₂ τ) (d₃ : Typed Γ e₃ τ)
    : Typed Γ (.If e₁ e₂ e₃) τ
  | Let {τ₁ τ₂ : Types} (d₁ : Typed Γ e₁ τ₁) (d₂ : Typed ((x, τ₁) :: Γ) e₂ τ₂)
    : Typed Γ (.Let x e₁ e₂) τ₂
  | Fn {Γ : TypeEnv} (d : Typed (Γ.cons (x, τ₁)) e τ₂)
    : Typed Γ (.Fn x e) (.Fn τ₁ τ₂)
  | App (d₁ : Typed Γ e₁ (.Fn τ₁ τ₂)) (d₂ : Typed Γ e₂ τ₁)
    : Typed Γ (.App e₁ e₂) τ₂

mutual
  /--
  値$\MV{v}$が型$\MV{\tau}$に適合していること
  $\models \MV{v} : \MV{\tau}$
  -/
  def ValueCompat : Value → Types → Prop
    | .Z _,       .Int      => True
    | .B _,       .Bool     => True
    | .Cls E x e, .Fn τ₁ τ₂ => ∃ Γ, EnvCompat E Γ ∧ Typed (Γ.cons (x, τ₁)) e τ₂
    | _,          _         => False

  /--
  環境$\MV{\mathcal{E}}$が型環境$\MV{\Gamma}$に適合していること
  $\models \MV{\mathcal{E}} : \MV{\Gamma}$
  -/
  def EnvCompat : Env → TypeEnv → Prop
    | Env.nil,            List.nil            => True
    | Env.cons (x, v) E', List.cons (y, τ) Γ' => x = y ∧ EnvCompat E' Γ' ∧ ValueCompat v τ
    | _,                  _                   => False
end

theorem ValueCompat.Z_Int {i : ℤ} :
  ValueCompat (.Z i) .Int = True
:= by simp [ValueCompat]

theorem ValueCompat.Z_Bool {i : ℤ} :
  ValueCompat (.Z i) .Bool = False
:= by simp [ValueCompat]

theorem ValueCompat.Z_Cls {i : ℤ} :
  ValueCompat (.Z i) (.Fn τ₁ τ₂) = False
:= by simp [ValueCompat]

theorem ValueCompat.B_Bool {b : 𝔹} :
  ValueCompat (.B b) .Bool = True
:= by simp [ValueCompat]

theorem ValueCompat.B_Int {b : 𝔹}:
  ValueCompat (.B b) .Int = False
:= by simp [ValueCompat]

theorem ValueCompat.B_Cls {b : 𝔹} :
  ValueCompat (.B b) (.Fn τ₁ τ₂) = False
:= by simp [ValueCompat]

theorem ValueCompat.Cls_Int {E : Env} {x : VarName} {e : Expr} :
  ValueCompat (.Cls E x e) .Int = False
:= by simp [ValueCompat]

theorem ValueCompat.Cls_Bool {E : Env} {x : VarName} {e : Expr} :
  ValueCompat (.Cls E x e) .Bool = False
:= by simp [ValueCompat]

theorem ValueCompat.Cls_Fn {E : Env} {x : VarName} {e : Expr} :
  ValueCompat (.Cls E x e) (.Fn τ₁ τ₂) = ∃ Γ, EnvCompat E Γ ∧ Typed (Γ.cons (x, τ₁)) e τ₂
:= by simp [ValueCompat]

theorem EnvCompat.cons_cons :
  EnvCompat (Env.cons (x, v) E') (List.cons (y, τ) Γ') = (x = y ∧ EnvCompat E' Γ' ∧ ValueCompat v τ)
:= by simp [EnvCompat]

/-!
ML2までと異なり、$\TT{fun $\MV{x}$ → $\MV{e}$}$のような式に対して素朴な再帰的アルゴリズムでは型を決定することができない。
そこで型変数を導入してそれに関する方程式を立てて解くことによって型推論を行うのである。
\[基礎概念]の第10章の内容である。
-/

/--
型代入 \[基礎概念,§9.4]

型変数$\MV{\alpha}$を型$\MV{\tau}$で置き換える型代入を$\MV{\alpha} := \MV{\tau}$の気持ちで`(α, τ)`と書く。
数式的には$[\MV{\tau}/\MV{\alpha}]$。
-/
abbrev TypeSubst := List (VarName × Types)

/--
型$\MV{\tau}$に型代入$S$を適用（$S\MV{\tau}$）する。
-/
def Types.subst (S : TypeSubst) : Types → Types
  | .Int => .Int
  | .Bool => .Bool
  | .Fn τ₁ τ₂ => .Fn (τ₁.subst S) (τ₂.subst S)
  | .Var α =>
      match S.findSome? (fun ⟨β, τ⟩ => if β = α then some τ else none) with
      | some τ => τ
      | none   => .Var α

/--
型代入$S$を型$\MV{\tau}$から型$S\MV{\tau}$への写像とみなす。
-/
instance : CoeFun TypeSubst (fun _ => Types → Types) where
  coe := Types.subst

/--
型環境$\MV{\Gamma}$に型代入$S$を適用（$S\MV{\Gamma}$）する。
-/
def TypeEnv.subst (S : TypeSubst) : TypeEnv → TypeEnv :=
  List.map (fun ⟨x, τ⟩ => (x, S τ))

/--
主要型 \[基礎概念,§10.2]
-/
structure PrincipalType (Γ : TypeEnv) (e : Expr) where
  S : TypeSubst
  τ : Types
  h : Typed (Γ.subst S) e τ
  /-- 主要型にさらに代入を施すことで、具体的な任意の型を得られる。 -/
  instantiate : Typed (Γ.subst S') e τ' → ∃ S'', (Γ.subst S).subst S'' = Γ.subst S' ∧ τ.subst S'' = τ'

/--
型に関する連立方程式$E = (E^1, E^0)$

両辺が関数型の方程式${ {\MV{\tau_1}→\MV{\tau_2}} = {\MV{\tau'_1}→\MV{\tau'_2}} } \in E^1$は、
引数の型の方程式${\MV{\tau_1}=\MV{\tau'_1}} \in E^0$と返り値の型の方程式${\MV{\tau_2}=\MV{\tau'_2}} \in E^0$とに分解できるから、
分解後に方程式が「小さく」なることが（各次数の方程式の数の辞書式順序で）示せるように分けて定義する。
-/
structure SimultaneousEquation where
  /--
  `τ₁ → τ₂ = τ₁' → τ₂'`
  -/
  fst_deg : List (Types × Types)
  /--
  `α = τ`
  -/
  zero_deg : List (Types × Types)

/--
連立方程式に型代入を適用する。
-/
def SimultaneousEquation.subst (S : TypeSubst) : SimultaneousEquation → SimultaneousEquation :=
  let subst := fun (⟨τ₁, τ₂⟩ : Types × Types) => (⟨τ₁.subst S, τ₂.subst S⟩ : Types × Types)
  fun ⟨E₁, E₀⟩ => ⟨E₁.map subst, E₀.map subst⟩

/--
連立方程式に型代入を適用しても方程式の数は変わらない。
-/
theorem SimultaneousEquation.length_eq_of_subst : (E : SimultaneousEquation) → (E.subst S).fst_deg.length = E.fst_deg.length ∧ (E.subst S).zero_deg.length = E.zero_deg.length
  | ⟨[], []⟩ => ⟨rfl, rfl⟩
  | ⟨[], e :: es⟩ =>
      have ⟨_, h⟩ := SimultaneousEquation.length_eq_of_subst ⟨[], es⟩
      have := h ▸ List.length_cons e es
      ⟨rfl, this ▸ rfl⟩
  | ⟨e :: es, []⟩ =>
      have ⟨h, _⟩ := SimultaneousEquation.length_eq_of_subst ⟨es, []⟩
      have := h ▸ List.length_cons ..
      ⟨this ▸ rfl, rfl⟩
  | ⟨e₁ :: es₁, e₀ :: es₀⟩ =>
      have ⟨h₁, h₀⟩ := SimultaneousEquation.length_eq_of_subst ⟨es₁, es₀⟩
      have h₁ := h₁ ▸ List.length_cons e₁ es₁
      have h₀ := h₀ ▸ List.length_cons e₀ es₀
      ⟨h₁ ▸ rfl, h₀ ▸ rfl⟩


/--
式$\MV{e}$について、与えられた型環境$\MV{\Gamma}$のもとで型に関する連立方程式$E$と式$\MV{e}$の型$\MV{\tau}$の組$(E, \MV{\tau})$を返す。

`parital`ではないのでLeanの仕様上この関数は全域で停止する（練習問題10.1 \[基礎概念,10章]）。
-/
def Expr.extract (e : Expr) (Γ : TypeEnv) (bounded : e.fv ⊆ Γ.dom) (Λ : List VarName := []) : SimultaneousEquation × Types × List VarName :=
  match e with
  | .Z _   => (⟨[], []⟩, .Int, Λ)
  | .B _   => (⟨[], []⟩, .Bool, Λ)
  | .Var x =>
      match Γ with
      | [] =>
          let α := s!"α{Λ.length}"
          (⟨[], [(.Var α, .Var α)]⟩, .Var α, α :: Λ)
      | (y, τ) :: (Γ' : TypeEnv) =>
          if h : x = y
          then (⟨[], []⟩, τ, Λ)
          else
            have bounded' : (Var x).fv ⊆ Γ'.dom :=
              fun a h' =>
                have : a ∈ Γ'.dom ∨ a ∈ {y} := (TypeEnv.dom.cons ▸ bounded) a h'
                Or.elim this
                  id
                  (fun h'' : a ∈ {y} =>
                    have hx := Singleton.mem_iff_eq_elem.mp (Expr.fv.Var ▸ h')
                    have hy := Singleton.mem_iff_eq_elem.mp h''
                    have := hx ▸ hy
                    absurd this.symm h
                  )
            (Var x).extract Γ' bounded' Λ
  | .Add e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (e₁.Add e₂).fv := Expr.fv.Add ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (e₁.Add e₂).fv := Expr.fv.Add ▸ Union.subset_intro_right
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      (⟨E₂₁ ++ E₁₁, (τ₂, .Int) :: (τ₁, .Int) :: E₂₀ ++ E₁₀⟩, .Int, Λ₂)
  | .Sub e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (e₁.Sub e₂).fv := Expr.fv.Sub ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (e₁.Sub e₂).fv := Expr.fv.Sub ▸ Union.subset_intro_right
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      (⟨E₂₁ ++ E₁₁, (τ₂, .Int) :: (τ₁, .Int) :: E₂₀ ++ E₁₀⟩, .Int, Λ₂)
  | .Mul e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (e₁.Mul e₂).fv := Expr.fv.Mul ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (e₁.Mul e₂).fv := Expr.fv.Mul ▸ Union.subset_intro_right
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      (⟨E₂₁ ++ E₁₁, (τ₂, .Int) :: (τ₁, .Int) :: E₂₀ ++ E₁₀⟩, .Int, Λ₂)
  | .LT e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (e₁.LT e₂).fv := Expr.fv.LT ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (e₁.LT e₂).fv := Expr.fv.LT ▸ Union.subset_intro_right
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      (⟨E₂₁ ++ E₁₁, (τ₂, .Int) :: (τ₁, .Int) :: E₂₀ ++ E₁₀⟩, .Bool, Λ₂)
  | .If e₁ e₂ e₃ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ (Subset.trans Union.subset_intro_left Union.subset_intro_right)
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      let ⟨⟨E₃₁, E₃₀⟩, τ₃, Λ₃⟩ :=
        have : e₃.fv ⊆ (Expr.If e₁ e₂ e₃).fv := Expr.fv.If ▸ Set.union_assoc ▸ (Subset.trans Union.subset_intro_right Union.subset_intro_right)
        e₃.extract Γ (Subset.trans this bounded) Λ₂
      let E'₀ := (τ₁, .Bool) :: E₃₀ ++ E₂₀ ++ E₁₀
      let E'₁ := E₃₁ ++ E₂₁ ++ E₁₁
      match τ₂, τ₃ with
      | .Fn _ _, .Fn _ _ => (⟨(τ₂, τ₃) :: E'₁,             E'₀⟩, τ₂, Λ₃)
      | _,       _       => (⟨            E'₁, (τ₂, τ₃) :: E'₀⟩, τ₂, Λ₃)
  | .Let x e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (Expr.Let x e₁ e₂).fv := Expr.fv.Let ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        let Γ' : TypeEnv := (x, τ₁) :: Γ
        have bounded' : e₂.fv ⊆ Γ'.dom :=
          TypeEnv.dom.cons ▸ fun y h =>
            if heq : x = y
            then Or.inr (heq ▸ rfl)
            else Or.inl (bounded y (Expr.fv.Let ▸ Or.inr ⟨h, fun h => absurd h heq⟩))
        e₂.extract Γ' bounded' Λ₁
      (⟨E₂₁ ++ E₁₁, E₂₀ ++ E₁₀⟩, τ₂, Λ₂)
  | .Fn x e =>
      let α : VarName := s!"α{Λ.length}"
      let Γ' : TypeEnv := (x, .Var α) :: Γ
      let ⟨E, τ, Λ'⟩ :=
        have bounded' : e.fv ⊆ Γ'.dom :=
          TypeEnv.dom.cons ▸ fun y h =>
            if heq : x = y
            then Or.inr (heq ▸ rfl)
            else Or.inl (bounded y (Expr.fv.Fn ▸ ⟨h, fun h => absurd (Singleton.mem_iff_eq_elem.mp h) heq⟩))
        e.extract Γ' bounded' (Λ.cons α)
      (E, .Fn (.Var α) τ, Λ')
  | .App e₁ e₂ =>
      let ⟨⟨E₁₁, E₁₀⟩, τ₁, Λ₁⟩ :=
        have : e₁.fv ⊆ (Expr.App e₁ e₂).fv := Expr.fv.App ▸ Union.subset_intro_left
        e₁.extract Γ (Subset.trans this bounded) Λ
      let ⟨⟨E₂₁, E₂₀⟩, τ₂, Λ₂⟩ :=
        have : e₂.fv ⊆ (Expr.App e₁ e₂).fv := Expr.fv.App ▸ Union.subset_intro_right
        e₂.extract Γ (Subset.trans this bounded) Λ₁
      let α : VarName := s!"α{Λ₂.length}"
      let E'₀ := E₂₀ ++ E₁₀
      let E'₁ := E₂₁ ++ E₁₁
      match τ₁ with
      | .Fn _ _ => (⟨(τ₁, .Fn τ₂ (.Var α)) :: E'₁,                          E'₀⟩, .Var α, α :: Λ₂)
      | _       => (⟨                         E'₁, (τ₁, .Fn τ₂ (.Var α)) :: E'₀⟩, .Var α, α :: Λ₂)

theorem Expr.extract.Z (h : (Expr.Z i).fv ⊆ TypeEnv.dom Γ) : (Expr.Z i).extract Γ h Λ = (⟨[], []⟩, .Int, Λ) := by simp [Expr.extract]
theorem Expr.extract.Var (h : (Expr.Var x).fv ⊆ TypeEnv.dom [(y, τ)]) (heq : x = y := by trivial) : (Expr.Var x).extract [(y, τ)] h Λ = (⟨[], []⟩, τ, Λ) := by simp [Expr.extract] ; exact heq
theorem Expr.extract.Fn
  {Λ : List VarName}
  {h' : e.fv ⊆ TypeEnv.dom ((x, Types.Var s!"α{Λ.length}") :: Γ)}
  (h₀ : e.extract ((x, .Var s!"α{Λ.length}") :: Γ) h' (s!"α{Λ.length}" :: Λ) = (E, τ, Λ'))
: (Expr.Fn x e).extract Γ h Λ = (E, .Fn (.Var s!"α{Λ.length}") τ, Λ')
:= by simp [Expr.extract] ; exact h₀ ▸ ⟨rfl, rfl, rfl⟩
theorem Expr.extract.App
  (h₁ : e₁.extract Γ b₁ Λ  = (⟨E₁₁, E₁₀⟩, τ₁, Λ₁))
  (h₂ : e₂.extract Γ b₂ Λ₁ = (⟨E₂₁, E₂₀⟩, τ₂, Λ₂))
: (Expr.App e₁ e₂).extract Γ b Λ = (
    (
      match τ₁ with
      | .Fn _ _ => ⟨(τ₁, .Fn τ₂ (.Var s!"α{Λ₂.length}")) :: E₂₁ ++ E₁₁, E₂₀ ++ E₁₀⟩
      | _ => ⟨E₂₁ ++ E₁₁, (τ₁, .Fn τ₂ (.Var s!"α{Λ₂.length}")) :: E₂₀ ++ E₁₀⟩
    ),
    .Var s!"α{Λ₂.length}",
    s!"α{Λ₂.length}" :: Λ₂
  )
:= by
  simp [Expr.extract, h₁, h₂]
  match τ₁ with
  | .Int    => exact rfl
  | .Bool   => exact rfl
  | .Var _  => exact rfl
  | .Fn _ _ => exact rfl

/--
$$
\text{
型代入$S$が連立方程式
$\{
  {\MV{\tau_{11}} = \MV{\tau_{12}}},\,
  \dots,\,
  {\MV{\tau_{n1}} = \MV{\tau_{n2}}}
\}$
の解である}
\mathrel{\overset{\text{def}}{\iff}}
\forall i \in \\{1,\dots,n\\}. S\MV{\tau_{i1}} \equiv S\MV{\tau_{i2}}
$$
（定義10.2 \[基礎概念,§10.4]）
-/
def TypeSubst.solved (S : TypeSubst) : SimultaneousEquation → Prop
  | ⟨[], []⟩             => True
  | ⟨[], (τ₁, τ₂) :: E₀⟩ => τ₁.subst S = τ₂.subst S ∧ S.solved ⟨[], E₀⟩
  | ⟨(τ₁, τ₂) :: E₁, E₀⟩ => τ₁.subst S = τ₂.subst S ∧ S.solved ⟨E₁, E₀⟩

example : TypeSubst.solved [] ⟨[], []⟩ := by simp [TypeSubst.solved] -- True.intro
example : TypeSubst.solved [("'b", .Int)] ⟨[], []⟩ := by simp [TypeSubst.solved] -- True.intro

example : TypeSubst.solved [] ⟨[], [(.Int, .Int)]⟩ := by simp [TypeSubst.solved] -- ⟨rfl, True.intro⟩
example : TypeSubst.solved [("'b", .Int)] ⟨[], [(.Var "'b", .Int)]⟩ := by simp [TypeSubst.solved, Types.subst, List.findSome?] -- ⟨rfl, True.intro⟩
example : TypeSubst.solved [("'b", .Int), ("'a", .Fn .Int .Int)] ⟨[], [(.Var "'b", .Int), (.Var "'a", .Fn .Int (.Var "'b"))]⟩
:= by simp [TypeSubst.solved, Types.subst, List.findSome?]
-- := ⟨rfl, rfl, True.intro⟩

example : TypeSubst.solved [("'c", .Int), ("'b", .Fn .Int .Int), ("'a", .Fn .Int (.Fn .Int .Int))] ⟨[], [(.Var "'b", .Fn .Int (.Var "'c")), (.Var "'a", .Fn .Int (.Var "'b"))]⟩
:= by simp [TypeSubst.solved, Types.subst, List.findSome?]
-- := ⟨rfl, rfl, True.intro⟩
example : TypeSubst.solved [("'c", .Bool), ("'b", .Fn .Int .Bool), ("'a", .Fn .Int (.Fn .Int .Bool))] ⟨[], [(.Var "'b", .Fn .Int (.Var "'c")), (.Var "'a", .Fn .Int (.Var "'b"))]⟩
:= by simp [TypeSubst.solved, Types.subst, List.findSome?]
-- := ⟨rfl, rfl, True.intro⟩
example : TypeSubst.solved [("'c", .Fn .Int .Int), ("'b", .Fn .Int (.Fn .Int .Int)), ("'a", .Fn .Int (.Fn .Int (.Fn .Int .Int)))] ⟨[], [(.Var "'b", .Fn .Int (.Var "'c")), (.Var "'a", .Fn .Int (.Var "'b"))]⟩
:= by simp [TypeSubst.solved, Types.subst, List.findSome?]
-- := ⟨rfl, rfl, True.intro⟩

/--
型代入$S$が連立方程式$E$の最汎単一化子であること。
-/
def TypeSubst.most_general (S : TypeSubst) (E : SimultaneousEquation) : Prop :=
  S.solved E ∧ ∀ S' : TypeSubst, S'.solved E → ∃ S'' : TypeSubst, S' = S'' ∘ S

/--
連立方程式の一階の単一化アルゴリズムUnify \[基礎概念,§10.4]

`parital`ではないのでLeanの仕様上この関数は全域で停止する（練習問題10.2）。

以下を示すのが肝であった。
- $(E^1, E^0 \cup \{\MV{\alpha} = \MV{\tau}\}) \prec ([\MV{\tau}/\MV{\alpha}]E^1, [\MV{\tau}/\MV{\alpha}]E^0)$
- $(E^1 \cup \{{\MV{\tau_1}→\MV{\tau_2}} = {\MV{\tau'_1}→\MV{\tau'_2}}\}, E^0) \prec (E^1, E^0 \cup \{ {\MV{\tau_1}=\MV{\tau'_1}} ,\, {\MV{\tau_2}=\MV{\tau'_2}} \})$
-/
def SimultaneousEquation.unify : SimultaneousEquation → Error ⊕ TypeSubst
  | ⟨[], []⟩ => .inr []
  | ⟨E₁, (.Int, .Int) :: E₀⟩ => SimultaneousEquation.unify ⟨E₁, E₀⟩
  | ⟨E₁, (.Bool, .Bool) :: E₀⟩ => SimultaneousEquation.unify ⟨E₁, E₀⟩
  | ⟨E₁, (.Var α, τ) :: E₀⟩ =>
      if .Var α = τ
      then SimultaneousEquation.unify ⟨E₁, E₀⟩
      else
        if α ∈ τ.fv
        then .inl error
        else
          let E' := SimultaneousEquation.subst [(α, τ)] ⟨E₁, E₀⟩
          match E'.unify with
          | .inr S => .inr ((α, τ.subst S) :: S)
          | .inl ε => .inl ε
  | ⟨E₁, (τ, .Var α) :: E₀⟩ =>
      if .Var α = τ
      then SimultaneousEquation.unify ⟨E₁, E₀⟩
      else
        if α ∈ τ.fv
        then .inl error
        else
          let E' := SimultaneousEquation.subst [(α, τ)] ⟨E₁, E₀⟩
          match E'.unify with
          | .inr S => .inr ((α, τ.subst S) :: S)
          | .inl ε => .inl ε
  | ⟨(.Fn τ₁₁ τ₁₂, .Fn τ₂₁ τ₂₂) :: E₁, E₀⟩ => SimultaneousEquation.unify ⟨E₁, ((τ₁₂, τ₂₂) :: (τ₁₁, τ₂₁) :: E₀)⟩
  | _ => .inl error
termination_by E => (E.fst_deg.length, E.zero_deg.length)
decreasing_by
  all_goals simp_wf
  . apply Prod.Lex.right ; simp_arith
  . apply Prod.Lex.right ; simp_arith
  . apply Prod.Lex.right ; simp_arith
  . -- `| [τ/α]E | = | E |`であって、
    have h1 : E'.fst_deg.length = E₁.length  := SimultaneousEquation.length_eq_of_subst _ |> And.left
    have h2 : E'.zero_deg.length ≤ E₀.length := SimultaneousEquation.length_eq_of_subst _ |> And.right |> Nat.le_of_eq
    rw [h1]
    -- 0次の方はパターンから小さくなっている
    apply Prod.Lex.right ; simp_arith ; exact h2
  . apply Prod.Lex.right ; simp_arith
  . -- `| [τ/α]E | = | E |`であって、
    have h1 : E'.fst_deg.length = E₁.length  := SimultaneousEquation.length_eq_of_subst _ |> And.left
    have h2 : E'.zero_deg.length ≤ E₀.length := SimultaneousEquation.length_eq_of_subst _ |> And.right |> Nat.le_of_eq
    rw [h1]
    -- 0次の方はパターンから小さくなっている
    apply Prod.Lex.right ; simp_arith ; exact h2
  . apply Prod.Lex.left ; simp_arith

theorem SimultaneousEquation.unify_nil
: SimultaneousEquation.unify ⟨[], []⟩ = .inr [] := by simp [SimultaneousEquation.unify]
theorem SimultaneousEquation.unify.Var (h0 : .Var α ≠ τ) (h1 : α ∉ τ.fv) (h2 : (SimultaneousEquation.subst [(α, τ)] ⟨E₁, E₀⟩).unify = .inr S)
: SimultaneousEquation.unify ⟨E₁, (.Var α, τ) :: E₀⟩ = .inr ((α, τ.subst S) :: S)
:= by simp [SimultaneousEquation.unify, h0, h1, h2]

/-
#eval (SimultaneousEquation.unify ⟨[], [(.Var "'b", .Int), (.Var "'a", .Fn .Int (.Var "'b"))]⟩)
/-
Sum.inr [("'b", HelloTypeSystem.ML3.Types.Int),
 ("'a", HelloTypeSystem.ML3.Types.Fn (HelloTypeSystem.ML3.Types.Int) (HelloTypeSystem.ML3.Types.Int))]
-/
-/

/-
/--
`eval`はML3式を評価してその結果を返します。
-/
def Expr.eval (e : Expr) (empty : e.fv = ∅) : Result :=
  e.eval_aux Env.nil (show e.fv ⊆ Env.nil.dom from fun _ h => (empty ▸ h : _ ∈ ∅))
  |> Sigma.fst
-/
