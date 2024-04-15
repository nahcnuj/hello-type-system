/--
ペアノ自然数
-/
inductive PNat
  | Z
  | S (n : PNat)

def PNat.toNat : PNat → Nat
  | .Z   => Nat.zero
  | .S n => Nat.succ n.toNat

theorem PNat.toNat_succ (n : PNat) : 1 + PNat.toNat n = PNat.toNat (.S n) :=
  calc 1 + PNat.toNat n
    _ = PNat.toNat n + 1 := Nat.add_comm _ _

instance : OfNat PNat 0 where
  ofNat := PNat.Z

instance (n : Nat) [OfNat PNat n] : OfNat PNat (Nat.succ n) where
  ofNat := PNat.S (OfNat.ofNat n)

instance : ToString PNat where
  toString n := s!"{n.toNat}"

instance : Coe PNat Nat where
  coe n := n.toNat

def PNat.add : PNat → PNat → PNat
  | .Z, k => k
  | .S n, k => .S (PNat.add n k)

instance : Add PNat where
  add := PNat.add

def PNat.mul : PNat → PNat → PNat
  | .Z,   _ => .Z
  | .S n, k => k + PNat.mul n k

instance : Mul PNat where
  mul := PNat.mul

/--
判断
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
