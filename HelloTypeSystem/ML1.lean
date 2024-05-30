import HelloTypeSystem.Basic

namespace HelloTypeSystem

/-!
# 整数・真偽値式の評価 ML1
\[基礎概念,3章]
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
EvalML1Errで発生する実行時エラーの種類
$$\begin{align*}
\Set{Error} \ni \MV{\varepsilon} &{}::= \TT{error}\_{\TT{+}} \mid \TT{error}\_{\TT{-}} \mid \TT{error}\_{\TT{\*}} \mid \TT{error}\_{\TT{<}} \mid \TT{error}\_{\TT{if}\_{\mathrm{cond}}} \mid \TT{error}\_{\TT{if}\_{\mathrm{value}}} \\\\
\end{align*}$$
-/
inductive Error where
  | Plus
  | Minus
  | Times
  | LT
  | IfCond

/--
$\Set{Result} := \Set{Error} \uplus \Set{Value}$
-/
abbrev Result := Error ⊕ Value
instance : Coe Value Result where
  coe := .inr
instance : Coe Error Result where
  coe := .inl

instance : OfNat Result n where
  ofNat := .inr (.Z n)

/-!
\[基礎概念]では型システムは8章に登場するが、後ろの章で定義されるML4がベースとなっている。
先取りしてML1に型判断とその導出規則を導入し（TypingML1と呼ぶ）、その型安全性を証明してみたい。
-/

/--
TypingML1が扱う型
$$\Set{Types} \ni \MV{\tau} ::= \TT{int} \mid \TT{bool}$$
-/
inductive Types where
  | Int
  | Bool

/--
導出システムEvalML1Err、TypingML1における判断
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
  "$\MV{e} \Evals \MV{r}$" means that the result of an expression $\MV{e}$ is $\MV{r}$.
  -/
  | Eval (e : Expr) (r : Result)
  /--
  "$\vdash\MV{e}\colon\MV{\tau}$" means that the type of an expression $\MV{e}$ is $\MV{\tau}$.
  -/
  | Typable (e : Expr) (τ : Types)

notation:50 e:51 " ⇓ " n:51 => Judgement.Eval e n
notation:50 "⊢ " e:51 " : " τ:51 => Judgement.Typable e τ

/--
導出システムEvalML1Err、TypingML1の導出規則

付帯条件はLeanのPropで表現している。
-/
inductive Derivation : Judgement → Type where
  -- 判断の導出規則
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

  -- 評価についての導出規則
  | E_Int {i : Int}
    : Derivation (i ⇓ i)
  | E_Bool {b : Bool}
    : Derivation (b ⇓ b)
  | E_Plus {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ + i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (p : Derivation (.Plus i₁ i₂ h))
    : Derivation (e₁ + e₂ ⇓ i₃)
  | E_Minus {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ - i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (m : Derivation (.Minus i₁ i₂ h))
    : Derivation (e₁ - e₂ ⇓ i₃)
  | E_Times {e₁ e₂ : Expr} {i₁ i₂ i₃ : Int} {h : i₁ * i₂ = i₃} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (t : Derivation (.Times i₁ i₂ h))
    : Derivation (e₁ * e₂ ⇓ i₃)
  | E_LT {e₁ e₂ : Expr} {i₁ i₂ : Int} {b : Bool} (l : Derivation (e₁ ⇓ i₁)) (r : Derivation (e₂ ⇓ i₂)) (lt : Derivation (.LT i₁ i₂ b))
    : Derivation (.LT e₁ e₂ ⇓ b)
  | E_IfT {e₁ e₂ e₃: Expr} {v : Value} (c : Derivation (e₁ ⇓ true)) (t : Derivation (e₂ ⇓ v))
    : Derivation (.If e₁ e₂ e₃ ⇓ v)
  | E_IfF {e₁ e₂ e₃: Expr} {v : Value} (c : Derivation (e₁ ⇓ false)) (f : Derivation (e₃ ⇓ v))
    : Derivation (.If e₁ e₂ e₃ ⇓ v)

  -- 型付け規則
  | T_Int {i : Int}
    : Derivation (⊢ i : .Int)
  | T_Bool {b : Bool}
    : Derivation (⊢ b : .Bool)
  | T_Plus {e₁ e₂ : Expr} (d₁ : Derivation (⊢ e₁ : .Int)) (d₂ : Derivation (⊢ e₂ : .Int))
    : Derivation (⊢ e₁ + e₂ : .Int)
  | T_Minus {e₁ e₂ : Expr} (d₁ : Derivation (⊢ e₁ : .Int)) (d₂ : Derivation (⊢ e₂ : .Int))
    : Derivation (⊢ e₁ - e₂ : .Int)
  | T_Times {e₁ e₂ : Expr} (d₁ : Derivation (⊢ e₁ : .Int)) (d₂ : Derivation (⊢ e₂ : .Int))
    : Derivation (⊢ e₁ * e₂ : .Int)
  | T_LT {e₁ e₂ : Expr} (d₁ : Derivation (⊢ e₁ : .Int)) (d₂ : Derivation (⊢ e₂ : .Int))
    : Derivation (⊢ .LT e₁ e₂ : .Bool)
  | T_If {e₁ e₂ e₃ : Expr} {τ : Types} (d₁ : Derivation (⊢ e₁ : .Bool)) (d₂ : Derivation (⊢ e₂ : τ)) (d₃ : Derivation (⊢ e₃ : τ))
    : Derivation (⊢ .If e₁ e₂ e₃ : τ)

  -- 実行時エラーについての導出規則

  /--
  加算において、左辺は整数だが右辺が真偽値の場合は実行時エラー
  -/
  | E_PlusIntBool (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inr (.B b₂)))
    : Derivation (e₁ + e₂ ⇓ Error.Plus)
  /--
  加算において、左辺は整数だが右辺が実行時エラーの場合は右辺の実行時エラー
  -/
  | E_PlusIntErr (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inl ε₂))
    : Derivation (e₁ + e₂ ⇓ ε₂)
  /--
  加算において、左辺が真偽値の場合は右辺によらず実行時エラー
  -/
  | E_PlusBool (l : Derivation (e₁ ⇓ .inr (.B b₂)))
    : Derivation (e₁ + e₂ ⇓ Error.Plus)
  /--
  加算において、左辺が実行時エラーの場合は右辺によらず左辺の実行時エラー（練習問題3.6 \[基礎概念,§3.2]）
  -/
  | E_PlusErr (l : Derivation (e₁ ⇓ .inl ε₁))
    : Derivation (e₁ + e₂ ⇓ ε₁)

  /--
  減算において、左辺は整数だが右辺が真偽値の場合は実行時エラー
  -/
  | E_MinusIntBool (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inr (.B b₂)))
    : Derivation (e₁ - e₂ ⇓ Error.Minus)
  /--
  減算において、左辺は整数だが右辺が実行時エラーの場合は右辺の実行時エラー
  -/
  | E_MinusIntErr (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inl ε₂))
    : Derivation (e₁ - e₂ ⇓ ε₂)
  /--
  減算において、左辺が真偽値の場合は右辺によらず実行時エラー
  -/
  | E_MinusBool (l : Derivation (e₁ ⇓ .inr (.B b₂)))
    : Derivation (e₁ - e₂ ⇓ Error.Minus)
  /--
  減算において、左辺が実行時エラーの場合は右辺によらず左辺の実行時エラー
  -/
  | E_MinusErr (l : Derivation (e₁ ⇓ .inl ε₁))
    : Derivation (e₁ - e₂ ⇓ ε₁)

  /--
  乗算において、左辺は整数だが右辺が真偽値の場合は実行時エラー
  -/
  | E_TimesIntBool (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inr (.B b₂)))
    : Derivation (e₁ * e₂ ⇓ Error.Times)
  /--
  乗算において、左辺は整数だが右辺が実行時エラーの場合は右辺の実行時エラー
  -/
  | E_TimesIntErr (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inl ε₂))
    : Derivation (e₁ * e₂ ⇓ ε₂)
  /--
  乗算において、左辺が真偽値の場合は右辺によらず実行時エラー
  -/
  | E_TimesBool (l : Derivation (e₁ ⇓ .inr (.B b₂)))
    : Derivation (e₁ * e₂ ⇓ Error.Times)
  /--
  乗算において、左辺が実行時エラーの場合は右辺によらず左辺の実行時エラー
  -/
  | E_TimesErr (l : Derivation (e₁ ⇓ .inl ε₁))
    : Derivation (e₁ * e₂ ⇓ ε₁)

  /--
  小なりの比較において、左辺は整数だが右辺が真偽値の場合は実行時エラー
  -/
  | E_LTIntBool (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inr (.B b₂)))
    : Derivation (.LT e₁ e₂ ⇓ Error.LT)
  /--
  小なりの比較において、左辺は整数だが右辺が実行時エラーの場合は右辺の実行時エラー
  -/
  | E_LTIntErr (l : Derivation (e₁ ⇓ .inr (.Z i₁))) (r : Derivation (e₂ ⇓ .inl ε₂))
    : Derivation (.LT e₁ e₂ ⇓ ε₂)
  /--
  小なりの比較において、左辺が真偽値の場合は右辺によらず実行時エラー
  -/
  | E_LTBool (l : Derivation (e₁ ⇓ .inr (.B b₁)))
    : Derivation (.LT e₁ e₂ ⇓ Error.LT)
  /--
  小なりの比較において、左辺が実行時エラーの場合は右辺によらず左辺の実行時エラー
  -/
  | E_LTErr (l : Derivation (e₁ ⇓ .inl ε₁))
    : Derivation (.LT e₁ e₂ ⇓ ε₁)

  /--
  条件分岐において、条件式が整数の場合は実行時エラー
  -/
  | E_IfCondInt (c : Derivation (e₁ ⇓ .inr (.Z i₁)))
    : Derivation (.If e₁ e₂ e₃ ⇓ Error.IfCond)
  /--
  条件分岐において、条件式が実行時エラーの場合はそのエラー
  -/
  | E_IfCondErr (c : Derivation (e₁ ⇓ .inl ε₁))
    : Derivation (.If e₁ e₂ e₃ ⇓ ε₁)
  /--
  条件分岐において、条件式は真だがthen節が実行時エラーの場合はそのエラー
  -/
  | E_IfTErr (c : Derivation (e₁ ⇓ .inr (.B true))) (t : Derivation (e₂ ⇓ .inl ε₂))
    : Derivation (.If e₁ e₂ e₃ ⇓ ε₂)
  /--
  条件分岐において、条件式は偽だがelse節が実行時エラーの場合はそのエラー
  -/
  | E_IfFErr (c : Derivation (e₁ ⇓ .inr (.B false))) (t : Derivation (e₃ ⇓ .inl ε₃))
    : Derivation (.If e₁ e₂ e₃ ⇓ ε₃)

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

/--
`Expr.eval`はML1式$\MV{e}$を評価し、評価結果$\MV{r} \in \Set{Error} \uplus \Set{Value}$とその導出$\mathcal{D} \in (\MV{e}\Evals\MV{r})$を返します。
-/
def Expr.eval : (e : Expr) → (r : Result) × Derivation (e ⇓ r)
  | .C (.Z i) => ⟨i, .E_Int⟩
  | .C (.B b) => ⟨b, .E_Bool⟩
  | .Add e₁ e₂ =>
      let ⟨r₁, d₁⟩ := eval e₁
      let ⟨r₂, d₂⟩ := eval e₂
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ + i₂, .E_Plus d₁ d₂ (.B_Plus rfl)⟩
      | .inr (.Z _),  .inr (.B _)  => ⟨Error.Plus, .E_PlusIntBool d₁ d₂⟩
      | .inr (.Z _),  .inl ε₂      => ⟨ε₂, .E_PlusIntErr d₁ d₂⟩
      | .inr (.B _),  _            => ⟨Error.Plus, .E_PlusBool d₁⟩
      | .inl ε₁,      _            => ⟨ε₁, .E_PlusErr d₁⟩
  | .Sub e₁ e₂ =>
      let ⟨r₁, d₁⟩ := eval e₁
      let ⟨r₂, d₂⟩ := eval e₂
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ - i₂, .E_Minus d₁ d₂ (.B_Minus rfl)⟩
      | .inr (.Z _),  .inr (.B _)  => ⟨Error.Minus, .E_MinusIntBool d₁ d₂⟩
      | .inr (.Z _),  .inl ε₂      => ⟨ε₂, .E_MinusIntErr d₁ d₂⟩
      | .inr (.B _),  _            => ⟨Error.Minus, .E_MinusBool d₁⟩
      | .inl ε₁,      _            => ⟨ε₁, .E_MinusErr d₁⟩
  | .Mul e₁ e₂ =>
      let ⟨r₁, d₁⟩ := eval e₁
      let ⟨r₂, d₂⟩ := eval e₂
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => ⟨i₁ * i₂, .E_Times d₁ d₂ (.B_Times rfl)⟩
      | .inr (.Z _),  .inr (.B _)  => ⟨Error.Times, .E_TimesIntBool d₁ d₂⟩
      | .inr (.Z _),  .inl ε₂      => ⟨ε₂, .E_TimesIntErr d₁ d₂⟩
      | .inr (.B _),  _            => ⟨Error.Times, .E_TimesBool d₁⟩
      | .inl ε₁,      _            => ⟨ε₁, .E_TimesErr d₁⟩
  | .LT e₁ e₂ =>
      let ⟨r₁, d₁⟩ := eval e₁
      let ⟨r₂, d₂⟩ := eval e₂
      match r₁, r₂ with
      | .inr (.Z i₁), .inr (.Z i₂) => Or.by_cases (Decidable.em (i₁ < i₂))
          (fun h :   i₁ < i₂ => ⟨true,  .E_LT d₁ d₂ (.B_LTT h)⟩)
          (fun h : ¬ i₁ < i₂ => ⟨false, .E_LT d₁ d₂ (.B_LTF h)⟩)
      | .inr (.Z _),  .inr (.B _)  => ⟨Error.LT, .E_LTIntBool d₁ d₂⟩
      | .inr (.Z _),  .inl ε₂      => ⟨ε₂, .E_LTIntErr d₁ d₂⟩
      | .inr (.B _),  _            => ⟨Error.LT, .E_LTBool d₁⟩
      | .inl ε₁,      _            => ⟨ε₁, .E_LTErr d₁⟩
  | .If e₁ e₂ e₃ =>
      let ⟨r₁, d₁⟩ := eval e₁
      match r₁ with
      | .inr (.B true) =>
          let ⟨r₂, d₂⟩ := eval e₂
          match r₂ with
          | .inr v₂ => ⟨v₂, .E_IfT d₁ d₂⟩
          | .inl ε₂ => ⟨ε₂, .E_IfTErr d₁ d₂⟩
      | .inr (.B false) =>
          let ⟨r₃, d₃⟩ := eval e₃
          match r₃ with
          | .inr v₃ => ⟨v₃, .E_IfF d₁ d₃⟩
          | .inl ε₃ => ⟨ε₃, .E_IfFErr d₁ d₃⟩
      | .inr (.Z _) => ⟨Error.IfCond, .E_IfCondInt d₁⟩
      | .inl ε₁     => ⟨ε₁, .E_IfCondErr d₁⟩

/--
型付けの結果
-/
inductive TypingResult (e : Expr) where
  | Ok    : (τ : Types) → Derivation (⊢ e : τ) → TypingResult e
  | Error : TypingResult e

/--
与えられた式の型検査を行う。
-/
def Expr.check : (e : Expr) → TypingResult e
  | .C (.Z _) => .Ok .Int  .T_Int
  | .C (.B _) => .Ok .Bool .T_Bool
  | .Add e₁ e₂ =>
      match e₁.check, e₂.check with
      | .Ok .Int d₁, .Ok .Int d₂ => .Ok .Int (.T_Plus d₁ d₂)
      | _          , _           => .Error
  | .Sub e₁ e₂ =>
      match e₁.check, e₂.check with
      | .Ok .Int d₁, .Ok .Int d₂ => .Ok .Int (.T_Minus d₁ d₂)
      | _          , _           => .Error
  | .Mul e₁ e₂ =>
      match e₁.check, e₂.check with
      | .Ok .Int d₁, .Ok .Int d₂ => .Ok .Int (.T_Times d₁ d₂)
      | _          , _           => .Error
  | .LT e₁ e₂ =>
      match e₁.check, e₂.check with
      | .Ok .Int d₁, .Ok .Int d₂ => .Ok .Bool (.T_LT d₁ d₂)
      | _          , _           => .Error
  | .If e₁ e₂ e₃ =>
      match e₁.check, e₂.check, e₃.check with
      | .Ok .Bool d₁, .Ok .Int  d₂, .Ok .Int  d₃ => .Ok .Int (.T_If d₁ d₂ d₃)
      | .Ok .Bool d₁, .Ok .Bool d₂, .Ok .Bool d₃ => .Ok .Bool (.T_If d₁ d₂ d₃)
      | _           , _           , _            => .Error

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

def AExpr.toML1 : AExpr → ML1.Expr
  | .C i         => .C i
  | .Add lhs rhs => .Add lhs.toML1 rhs.toML1
  | .Sub lhs rhs => .Sub lhs.toML1 rhs.toML1
  | .Mul lhs rhs => .Mul lhs.toML1 rhs.toML1

def BExpr.toML1 : BExpr → ML1.Expr
  | .C b        => .C b
  | .LT lhs rhs => .LT lhs.toML1 rhs.toML1

def Expr.toML1 : Expr → ML1.Expr
  | .A a         => a.toML1
  | .B b         => b.toML1
  | .If cond t f => .If cond.toML1 t.toML1 f.toML1

end ML1'
