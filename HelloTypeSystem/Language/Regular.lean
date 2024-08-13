namespace HelloTypeSystem.Language

/--
アルファベット$\Sigma$上の正規言語$\mathcal{R} := \bigcup_{k\in\mathbb{N}}{\mathcal{R}_k} \subseteq \mathop{\mathscr{P}}(\Sigma^{*})$

$$\begin{align*}
\mathcal{R}_0 :={}&
  \{\varnothing\}
    \cup \{ \{a\} \mid a\in\Sigma \}, \\
\mathcal{R}_{k+1} :={}&
  \mathcal{R}_k
    \cup \{ S^{*} \mid S\in\mathcal{R}_k \}
    \cup \{ S\cup T \mid {S,T}\in\mathcal{R}_k \}
    \cup \{ ST \mid {S,T}\in\mathcal{R}_k \},
  \\
\end{align*}$$
where

$$\begin{align*}
S^{*} :={}& \bigcup_{n\in\mathbb{N}}\{ s^n \mid s\in S \}, \\
ST :={}& \{ st \mid s\in S \land t\in T \}.
\end{align*}$$
-/
inductive Regular (S : Type u)
  /-- $\varnothing\in\mathcal{R}_0$ -/
  | Empty
  /-- $\forall a\in\Sigma. \{a\}\in\mathcal{R}_0$ -/
  | Single (a : S)
  /-- $\forall k\in{\mathbb{N}}. \forall S\in\mathcal{R}_k. (S^{*})\in\mathcal{R}_{k+1}$ -/
  | Star (n : Nat) (R : Regular S)
  /-- $\forall k\in{\mathbb{N}}. \forall {S,T}\in\mathcal{R}_k. (S \mid T) := S \cup T \in\mathcal{R}_{k+1}$ -/
  | Union (R₁ R₂ : Regular S)
  /-- $\forall k\in{\mathbb{N}}. \forall {S,T}\in\mathcal{R}_k. (ST)\in\mathcal{R}_{k+1}$ -/
  | Concat (R₁ R₂ : Regular S)
