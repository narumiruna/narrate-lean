-- Basic proofs in Lean 4
-- This file demonstrates simple mathematical theorems and proofs

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_succ, ih]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => 
    rw [add_zero, zero_add]
  | succ n ih => 
    rw [Nat.add_succ, ih, Nat.succ_add]

def double (n : Nat) : Nat := n + n

theorem double_eq_twice (n : Nat) : double n = 2 * n := by
  unfold double
  rw [Nat.two_mul]

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => 
    rw [add_zero, add_zero]
  | succ c ih => 
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]
