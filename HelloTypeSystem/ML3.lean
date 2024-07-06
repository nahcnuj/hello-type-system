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
  (HInt   : ∀ {E : Env} (i : ℤ), motive E i i)
  (HBool  : ∀ {E : Env} (b : 𝔹), motive E b b)
  (HVar   : ∀ {E : Env} {x : VarName} {v : Value}, motive (E.cons (x, v)) x v)
  (HVarIr : ∀ (E : Env) (x y : VarName) (v₁ : Value) {v₂ : Value}, y ≠ x → motive E x v₂ → motive (E.cons (y, v₁)) x v₂)
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
  | .Int  (i := i) => HInt i
  | .Bool (b := b) => HBool b
  | .Var  => HVar
  | .VarIr (E := E) (x := x) (y := y) (w := w) d hne =>
      have d := induction HInt HBool HVar HVarIr HAdd HSub HMul HLTT HLTF HIfT HIfF HLet HFun HApp d
      HVarIr E x y w hne d
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

/-
/--
`eval`はML3式を評価してその結果を返します。
-/
def Expr.eval (e : Expr) (empty : e.fv = ∅) : Result :=
  e.eval_aux Env.nil (show e.fv ⊆ Env.nil.dom from fun _ h => (empty ▸ h : _ ∈ ∅))
  |> Sigma.fst
-/
