import HelloTypeSystem.Util

namespace HelloTypeSystem.Automaton

/--
決定性有限オートマトン(deterministic finite automata, DFA)
$$\begin{align*}
D :={}& \langle Q,\Sigma,\delta,q_0,F \rangle, \text{where} \\
Q \colon{}& \text{状態の有限集合}, \\
\Sigma \colon{}& \text{入力記号の有限集合}, \\
\text{状態遷移関数} \delta \colon{}& Q \times \Sigma \to Q, \\
\text{初期状態} q_0 \in{}& Q, \\
\text{受理状態集合} F \subseteq{}& Q.
\end{align*}$$
-/
structure DFA (Q : Type u) (A : Type v) where
  next : Q → A → Q
  start : Q
  accept : Set Q

/--
DFA $D := \langle Q,\Sigma,\delta,q_0,F \rangle$の遷移関数$\delta$を文字列$\Sigma^{\*}$上に拡張した関数$\hat{\delta}$
$$\begin{align*}
\hat{\delta} \colon{}&& Q \times \Sigma^{*} \to{}& Q; \\
&& (q, \epsilon) \mapsto{}& q, \\
\forall w\in\Sigma^{*}. \forall a\in\Sigma.&& (q, wa) \mapsto{}& \mathop{\delta}( \mathop{\hat{\delta}}(q, w) , a ).
\end{align*}$$
-/
def DFA.work (dfa : DFA Q A) (q : Q) : List A → Q :=
  List.foldl dfa.next q
-- fun w =>
--   match w with
--   | .nil => q
--   | .cons a w => dfa.next (dfa.work q w) a

/--
DFA $D = \langle Q,\Sigma,\delta,q_0,F \rangle$が受理する言語$L(D) := \{ w \in \Sigma^{*} \mid \mathop{\hat{\delta}}(q_0, w) \in F \}$
-/
def DFA.lang (dfa : DFA Q A) : Set (List A) :=
  fun w => dfa.accept <| dfa.work dfa.start w

namespace Example

/--
アルファベット$\Set{Bin} := \\{0,1\\}$
-/
inductive Bin
| O
| I

/--
状態の有限集合$Q := \\{q_0, q_1, q_2\\}$
-/
inductive States
| q₀
| q₁
| q₂
deriving Repr

/--
遷移関数$\delta$
-/
def next : States → Bin → States
  | .q₀, .O => .q₀ -- 2 * 0 + 0 = 0 ≡ 0 (mod 3)
  | .q₀, .I => .q₁ -- 2 * 0 + 1 = 1 ≡ 1
  | .q₁, .O => .q₂ -- 2 * 1 + 0 = 2 ≡ 2
  | .q₁, .I => .q₀ -- 2 * 1 + 1 = 3 ≡ 0
  | .q₂, .O => .q₁ -- 2 * 2 + 0 = 4 ≡ 1
  | .q₂, .I => .q₂ -- 2 * 2 + 1 = 5 ≡ 2

/--
DFA $\langle Q, \Set{Bin}, \delta, q_0, \{q_0\} \rangle$
-/
def dfa : DFA States Bin :=
  {
    next := next,
    start := .q₀,
    accept := fun q => q = .q₀
  }

/-- 0₂ ≡ 0 (mod 3) -/
example : dfa.work .q₀ [.O] = .q₀ := rfl
/-- 1₂ ≡ 1 (mod 3) -/
example : dfa.work .q₀ [.I] = .q₁ := rfl
/-- 10₂ ≡ 2 (mod 3) -/
example : dfa.work .q₀ [.I, .O] = .q₂ := rfl
/-- 11₂ ≡ 0 (mod 3) -/
example : dfa.work .q₀ [.I, .I] = .q₀ := rfl

/--
DFA `dfa`は文字列`110`を受理する
すなわち$110 \in L(\mathtt{dfa})$
-/
example : [.I, .I, .O] ∈ dfa.lang := rfl

end Example
