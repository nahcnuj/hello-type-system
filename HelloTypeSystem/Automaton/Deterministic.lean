import HelloTypeSystem.Util

namespace HelloTypeSystem.Automaton

/--
アルファベット$A$上の（$n$-状態）決定性有限オートマトン(deterministic finite automata, DFA)$D := \langle \{q_0,\dots,q_{n-1}\},A,\delta,q_0,F \rangle$
-/
structure DFA (n : Nat) (A : Type u) where
  /-- 状態遷移関数$\delta$ -/
  next : Fin n → A → Fin n
  /-- 受理状態集合$F \subseteq \\{q_0,\dots,q_{n-1}\\}$ -/
  accept : Set (Fin n)

section
variable {A : Type u} {n : Nat}
variable (dfa : DFA n.succ A)

/--
DFA $D = \langle Q,A,\delta,q_0,F \rangle$の遷移関数$\delta$を文字列$A^{\*}$上に拡張した関数$\hat{\delta}$
$$\begin{align*}
\hat{\delta} \colon{}&& Q \times A^{*} \to{}& Q; \\
&& (q, \epsilon) \mapsto{}& q, \\
\forall w\in A^{*}. \forall a\in A.&& (q, wa) \mapsto{}& \mathop{\delta}( \mathop{\hat{\delta}}(q, w) , a ).
\end{align*}$$
-/
protected def DFA.work (q : Fin n.succ) : List A → Fin n.succ :=
  List.foldl dfa.next q
-- fun w =>
--   match w with
--   | .nil => q
--   | .cons a w => dfa.next (dfa.work q w) a

/--
DFA $D = \langle Q,A,\delta,q_0,F \rangle$が受理する言語$L(D) := \{ w \in A^{*} \mid \mathop{\hat{\delta}}(q_0, w) \in F \}$
-/
def DFA.lang : Set (List A) :=
  fun w => dfa.accept <| dfa.work 0 w.reverse

end

namespace Example

/--
アルファベット$\\{0,1\\}$上の文字列を2進数と見て、3の倍数であれば受理する3状態DFA
-/
def dfa : DFA 3 (Fin 2) :=
  let next : Fin 3 → Fin 2 → Fin 3
    | 0, 0 => 0 -- 2 * 0 + 0 = 0 ≡ 0 (mod 3)
    | 0, 1 => 1 -- 2 * 0 + 1 = 1 ≡ 1
    | 1, 0 => 2 -- 2 * 1 + 0 = 2 ≡ 2
    | 1, 1 => 0 -- 2 * 1 + 1 = 3 ≡ 0
    | 2, 0 => 1 -- 2 * 2 + 0 = 4 ≡ 1
    | 2, 1 => 2 -- 2 * 2 + 1 = 5 ≡ 2
  {
    next
    accept := fun q => q = 0
  }

/-- 0₂ ≡ 0 (mod 3) -/
example : dfa.work 0 [0] = 0 := rfl
/-- 1₂ ≡ 1 (mod 3) -/
example : dfa.work 0 [1] = 1 := rfl
/-- 10₂ ≡ 2 (mod 3) -/
example : dfa.work 0 [1,0] = 2 := rfl
/-- 11₂ ≡ 0 (mod 3) -/
example : dfa.work 0 [1,1] = 0 := rfl

/--
DFA `dfa`は文字列`110`を受理する
すなわち$110 \in L(\mathtt{dfa})$
-/
example : [1,1,0] ∈ dfa.lang := rfl

end Example
