import Mathlib

open Real Complex

theorem cexp_eq_cexp_iff_eq (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 2 * π)
                                      (hβ0 : 0 ≤ β) (hβ1 : β < 2 * π) :
  exp (α * I) = exp (β * I) ↔ α = β := by
  constructor
  · -- exp (α * I) = exp (β * I) → α = β
    intro h
    have h_period : ∃ n : ℤ, (α - β) * I = (2 * π * n) * I := by
      rw [Complex.exp_eq_exp_iff_exists_int] at h
      rcases h with ⟨n, hn⟩
      use n
      linear_combination hn
    rcases h_period with ⟨n, h_period⟩
    simp at h_period;
    have h_eq : α - β = 2 * π * n := by
      norm_cast at h_period

    have hn0 : n = 0 := by
      by_contra hn_ne_zero
      have h_bound : |α - β| < 2 * π := by
        rw [abs_sub_lt_iff]
        constructor
        · linarith
        · linarith
      rw [h_eq] at h_bound
      have h_contra : |2 * π * n| ≥ 2 * π := by
        calc |2 * π * ↑n|
          = |2 * π| * |↑n| := abs_mul (2 * π) ↑n
          _ = (2 * π) * |↑n| := by rw [abs_of_pos]; linarith
          _ ≥ (2 * π) * 1 := by
              apply mul_le_mul_of_nonneg_left
              · norm_cast
                exact Int.one_le_abs hn_ne_zero
              · linarith
          _ = 2 * π := by ring
      linarith [h_bound, h_contra]
    rw [hn0] at h_eq
    simp at h_eq
    linarith
  · -- α = β → exp (α * I) = exp (β * I)
    intro h
    rw [h]
