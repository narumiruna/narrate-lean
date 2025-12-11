-- Advanced proofs in Lean 4
-- Demonstrates more complex mathematical structures

def isEven (n : Nat) : Bool :=
  n % 2 = 0

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : factorial n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold factorial
    apply Nat.mul_pos
    · exact Nat.succ_pos n
    · exact ih

theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction n with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_mul]
  | succ n ih =>
    rw [Nat.mul_succ, ih, Nat.succ_mul]

def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

theorem fib_positive (n : Nat) (h : n > 0) : fibonacci n > 0 := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => unfold fibonacci; decide
    | succ n =>
      unfold fibonacci
      apply Nat.add_pos_left
      apply fib_positive
      exact Nat.succ_pos n
