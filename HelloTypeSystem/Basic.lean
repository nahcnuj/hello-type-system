namespace HelloTypeSystem

/--
ペアノ自然数
$$\begin{align*}
\Set{PNat} \ni \MV{n} ::={}& \TT{Z} \mid \TT{S}\MV{n} \\\\
\end{align*}$$
-/
inductive PNat
  | Z
  | S (n : PNat)

instance : OfNat PNat 0 where
  ofNat := PNat.Z

instance (n : Nat) [OfNat PNat n] : OfNat PNat (Nat.succ n) where
  ofNat := PNat.S (OfNat.ofNat n)

def PNat.toNat : PNat → Nat
  | .Z   => Nat.zero
  | .S n => Nat.succ n.toNat

instance : Coe PNat Nat where
  coe n := n.toNat

instance : ToString PNat where
  toString n := s!"{n.toNat}"

/--
算術式
$$\begin{align*}
\Set{Expr} \ni \MV{e} ::={}& \MV{n} \mid \TT{$\MV{e}$ + $\MV{e}$} \mid \TT{$\MV{e}$ * $\MV{e}$} \\\\
\end{align*}$$
-/
inductive Expr where
  | Nat (n : PNat)
  | Add (e₁ e₂ : Expr)
  | Mul (e₁ e₂ : Expr)

instance : Coe PNat Expr where
  coe := .Nat
instance : Add Expr where
  add := .Add
instance : Mul Expr where
  mul := .Mul

/--
判断

この型の項は形式上は正しい判断であるが、内容的にも正しいとは限らない。
-/
inductive Judgement where
  /--
  "$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Plus (n₁ n₂ n₃ : PNat)
  /--
  "$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$"
  -/
  | Times (n₁ n₂ n₃ : PNat)
  /--
  "$\TT{$\MV{n_1}$ is less than $\MV{n_2}$}$"
  -/
  | LT (n₁ n₂ : PNat)
  /--
  "$\MV{e} \Evals \MV{n}$" means that $\MV{e}$ evaluates to $\MV{n}$.
  -/
  | Eval (e : Expr) (n : PNat)

notation:50 e:51 " ⇓ " n:51 => Judgement.Eval e n
