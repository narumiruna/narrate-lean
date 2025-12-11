import Mathlib

def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
 ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

theorem sequence_squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (a_leq_b : ∀ n, a n ≤ b n)
  (b_leq_c : ∀ n, b n ≤ c n)
  (ha : seq_converges_to a L)
  (hc : seq_converges_to c L) :
  seq_converges_to b L := by
  unfold seq_converges_to at ha hc
  unfold seq_converges_to
  intro ε ε_pos
  have half_pos : 0 < ε / 2 := by linarith
  obtain ⟨N1, h1⟩ := ha (ε / 2) half_pos
  obtain ⟨N2, h2⟩ := hc (ε / 2) half_pos
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right _ _) hn
  have h1' := h1 n hn1
  have h2' := h2 n hn2
  -- pick N1, N2 so tail of a, c stay within ε/2 of L
  obtain ⟨ha_lower, ha_upper⟩ := abs_lt.mp h1'
  obtain ⟨hc_lower, hc_upper⟩ := abs_lt.mp h2'
  have h_an_le_bn : a n - L ≤ b n - L := by linarith [a_leq_b n]
  have h_bn_le_cn : b n - L ≤ c n - L := by linarith [b_leq_c n]
  have hb_ge_lower : -(ε / 2) < b n - L := lt_of_lt_of_le ha_lower h_an_le_bn
  have hb_le_upper : b n - L < ε / 2 := lt_of_le_of_lt h_bn_le_cn hc_upper
  have hb_abs : |b n - L| < ε / 2 := abs_lt.mpr ⟨hb_ge_lower, hb_le_upper⟩
  have h_eps : ε / 2 ≤ ε := by linarith
  exact lt_of_lt_of_le hb_abs h_eps
