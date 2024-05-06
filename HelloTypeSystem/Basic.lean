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

instance [OfNat PNat n] : OfNat Expr n where
  ofNat := Expr.Nat (OfNat.ofNat n)

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
  /--
  "$\MV{e} \Reduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ at a time.
  -/
  | Reduce (e : Expr) (e' : Expr)
  /--
  "$\MV{e} \MReduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ at some time.
  -/
  | MReduce (e : Expr) (e' : Expr)
  /--
  "$\MV{e} \DReduces \MV{e'}$" means that $\MV{e}$ is reduced to $\MV{e'}$ deterministically.
  -/
  | DReduce (e : Expr) (e' : Expr)

notation:50 e:51 " ⇓ " n:51  => Judgement.Eval e n
notation:50 e:51 " ⟶ " e':51 => Judgement.Reduce e e'
notation:50 e:51 " ⟶* " e':51 => Judgement.MReduce e e'
notation:50 e:51 " ⟶' " e':51 => Judgement.DReduce e e'

/--
与えられた判断が導出できるという命題
-/
inductive Derivable {Derivation : Judgement → Type v} (𝒥 : Judgement) : Prop where
  | intro (h : Derivation 𝒥)

/--
導出の項が構築できたときは明らかに導出できるので型強制する
-/
instance {𝒥 : Judgement} {Derivation : Judgement → Type u} : Coe (Derivation 𝒥) (Derivable (Derivation := Derivation) 𝒥) where
  coe := Derivable.intro
