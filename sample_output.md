# Narrated Lean Proof: sample.lean

*This document is a human-readable narration of the Lean 4 proof file `sample.lean`.*

---

## Imports

This proof file imports the following libraries:

- `Mathlib`

---

## Definitions

### seq_converges_to

A sequence $a : \mathbb{N} \to \mathbb{R}$ converges to $L \in \mathbb{R}$ if for every $\epsilon > 0$, there exists $N \in \mathbb{N}$ such that for all $n \geq N$, we have $|a_n - L| < \epsilon$. In symbols,
$$
\forall \epsilon > 0,\, \exists N \in \mathbb{N},\, \forall n \geq N,\; |a_n - L| < \epsilon.
$$

---

## Theorems

### Theorem: sequence_squeeze_theorem

**Theorem (Sequence Squeeze Theorem):** If a sequence $b_n$ is squeezed between two sequences $a_n$ and $c_n$ that both converge to the same limit $L$, then $b_n$ also converges to $L$.

**Given:**
- Sequences $a_n$, $b_n$, $c_n : \mathbb{N} \to \mathbb{R}$
- $L \in \mathbb{R}$
- $\forall n,\ a_n \leq b_n$
- $\forall n,\ b_n \leq c_n$
- $\lim_{n \to \infty} a_n = L$
- $\lim_{n \to \infty} c_n = L$

**Then:**
$$
\lim_{n \to \infty} b_n = L
$$

#### Proof

**Proof.**

Let $(a_{n})$, $(b_{n})$, $(c_{n})$ be sequences of real numbers and $L \in \mathbb{R}$ such that for all $n \in \mathbb{N}$,
$$
a_{n} \leq b_{n} \leq c_{n},
$$
and suppose that $\lim_{n \to \infty} a_{n} = L$ and $\lim_{n \to \infty} c_{n} = L$. We show that $\lim_{n \to \infty} b_{n} = L$.

**Step 1:** *Unfolding the definition of convergence.*

By hypothesis, for every $\epsilon > 0$, there exist $N_{1}, N_{2} \in \mathbb{N}$ such that
$$
|a_{n} - L| < \frac{\epsilon}{2} \quad \text{for all } n \geq N_{1},
$$
and
$$
|c_{n} - L| < \frac{\epsilon}{2} \quad \text{for all } n \geq N_{2}.
$$

**Step 2:** *Choosing a common index.*

Let $N = \max\{N_{1}, N_{2}\}$. Then for all $n \geq N$, both inequalities above hold.

**Step 3:** *Bounding $b_{n} - L$.*

For any $n \geq N$, we have
$$
a_{n} - L \leq b_{n} - L \leq c_{n} - L.
$$
From $|a_{n} - L| < \frac{\epsilon}{2}$, it follows that
$$
-\frac{\epsilon}{2} < a_{n} - L < \frac{\epsilon}{2}.
$$
Similarly, $|c_{n} - L| < \frac{\epsilon}{2}$ gives
$$
-\frac{\epsilon}{2} < c_{n} - L < \frac{\epsilon}{2}.
$$

Therefore,
$$
-\frac{\epsilon}{2} < a_{n} - L \leq b_{n} - L \leq c_{n} - L < \frac{\epsilon}{2},
$$
which implies
$$
-\frac{\epsilon}{2} < b_{n} - L < \frac{\epsilon}{2}.
$$

**Step 4:** *Concluding the proof.*

Thus,
$$
|b_{n} - L| < \frac{\epsilon}{2} < \epsilon
$$
for all $n \geq N$. Since $\epsilon > 0$ was arbitrary, this shows that $\lim_{n \to \infty} b_{n} = L$.

∎

---
