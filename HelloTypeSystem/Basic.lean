namespace HelloTypeSystem

/--
ペアノ自然数
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
判断

この型の項は形式上は正しい判断であるが、内容的にも正しいとは限らない。
内容的な正しい判断は導出システムによって規定される。
-/
inductive Judgement where
  /--
  "$n_1$ plus $n_2$ is $n_3$"
  -/
  | Plus (n₁ n₂ n₃ : PNat)
  /--
  "$n_1$ times $n_2$ is $n_3$"
  -/
  | Times (n₁ n₂ n₃ : PNat)
  /--
  "$n_1$ is less than $n_2$"
  -/
  | LT (n₁ n₂ : PNat)
