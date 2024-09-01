import HelloTypeSystem.Util

namespace HelloTypeSystem.Automaton

/--
アルファベット$A$上の（$n$-状態）非決定性有限オートマトン(nondeterministic finite automata, NFA)$N := \langle {Q := \{q_0,\dots,q_{n-1}\}},A,\Delta,q_0,F \rangle$
-/
structure NFA (n : Nat) (A : Type u) where
  /-- 遷移関係$\Delta \colon Q \times A \to \mathop{\mathscr{P}}(Q)$ -/
  next : Fin n → A → List (Fin n)
  /-- 受理状態集合$F \subseteq Q$ -/
  acceptable : List (Fin n)

section
variable {A : Type u} {n : Nat}
variable (nfa : NFA n.succ A)

def NFA.accept : Fin n.succ → Bool :=
  nfa.acceptable.contains

/--
NFA $N = \langle Q,A,\Delta,q_0,F \rangle$の遷移関係$\Delta$を文字列$A^{\*}$上に拡張した関係$\hat{\Delta}$
$$\begin{align*}
\hat{\Delta} \colon{}&& Q \times A^{*} \to{}& \mathop{\mathscr{P}}(Q); \\
&& (q, \epsilon) \mapsto{}& \{q\}, \\
\forall w\in A^{*}. \forall a\in A.&& (q, wa) \mapsto{}& \bigcup_{p \in \hat\Delta(q,w)} \mathop{\Delta}(p,a).
\end{align*}$$
-/
protected def NFA.work (q : Fin n.succ) : List A → List (Fin n.succ)
  | .nil      => [q]
  | .cons a w =>
      have := List.map (fun q => nfa.next q a) (NFA.work q w)
      this.foldl (List.append ∘ List.eraseDups) []

/--
NFA $N = \langle Q,A,\Delta,q_0,F \rangle$が受理する言語$L(N) := \{ w \in A^{*} \mid \mathop{\hat{\Delta}}(q_0, w) \cap F \neq \varnothing \}$
-/
def NFA.lang : Set (List A) :=
  fun w => List.any (nfa.work 0 w.reverse) nfa.accept

end

namespace Example

/--
アルファベット$\\{0,1\\}$上の`01`で終わる文字列のみを受理するNFA
-/
def nfa : NFA 3 (Fin 2) :=
  let next : Fin 3 → Fin 2 → List (Fin 3)
    | 0, 0 => [0, 1]
    | 0, 1 => [0]
    | 1, 1 => [2]
    | _, _ => []
  {
    next
    acceptable := [2]
  }

example : nfa.work 0 []          = [0]   := rfl
example : nfa.work 0 [0]         = [0,1] := rfl
example : nfa.work 0 [0,0]       = [0,1] := rfl
example : nfa.work 0 [1,0,0]     = [0,2] := rfl
example : nfa.work 0 [0,1,0,0]   = [0,1] := rfl
example : nfa.work 0 [1,0,1,0,0] = [0,2] := rfl

example : [0,0,1,0,1] ∈ nfa.lang := rfl

end Example
