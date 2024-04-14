namespace HelloTypeSystem

/--
ペアノ自然数
-/
inductive PNat
  | Z
  | S (n : PNat)

def PNat.toNat : PNat → Nat
  | .Z   => Nat.zero
  | .S n => Nat.succ n.toNat

instance : OfNat PNat 0 where
  ofNat := PNat.Z

instance (n : Nat) [OfNat PNat n] : OfNat PNat (Nat.succ n) where
  ofNat := PNat.S (OfNat.ofNat n)

instance : ToString PNat where
  toString n := s!"{n.toNat}"
