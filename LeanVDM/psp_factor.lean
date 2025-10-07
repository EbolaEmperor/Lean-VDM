import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators

open Matrix BigOperators Finset

lemma sum_diff_helper_1 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) =
  (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i)) + x^(n-1) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
  have : 1 + n' - 1 = n' := by omega
  simp [this]
  rw [Nat.add_comm 1 n', Finset.sum_range_succ]
  simp

lemma sum_diff_helper_2 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) =
  (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i)) + y^(n-1) := by
  have : range n = insert 0 (Ico 1 n) := by
    ext i; simp [Finset.mem_Ico]; omega
  rw [this, Finset.sum_insert]
  · simp [pow_zero, one_mul, add_comm]
  · simp

lemma sum_shift_one (n : ℕ) (hn : n ≥ 1) (u : ℕ → ℝ) :
  ∑ i ∈ range (n-1), u i = ∑ i ∈ Ico 1 n, u (i-1) := by
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp [Finset.mem_Ico]
    omega
  · omega
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    use b - 1
    refine ⟨?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · simp

lemma sum_diff_helper_3 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  x * (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i)) =
  y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i)) := by

  let u : ℕ → ℝ := fun i => x ^ (i + 1) * y ^ (n - 1 - i);

  calc x * (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i))
    = ∑ i ∈ range (n-1), x * x ^ i * y ^ (n - 1 - i) := by rw [Finset.mul_sum]; congr 1; ext i; ring
  _ = ∑ i ∈ range (n-1), x ^ (i+1) * y ^ (n - 1 - i) := by
      congr 1; ext i; ring_nf;
  _ = ∑ i ∈ range (n-1), u i := by rfl
  _ = ∑ i ∈ Ico 1 n, u (i-1) := by apply sum_shift_one n hn u
  _ = ∑ i ∈ Ico 1 n, x ^ i * y ^ (n - i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_Ico] at hi
      have hi1 : i - 1 + 1 = i := by omega
      have hin : n - 1 - (i - 1) = n - i := by omega
      unfold u; rw [hi1, hin];
  _ = y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_Ico] at hi
      have : n - i = 1 + (n - 1 - i) := by omega
      rw [this, pow_add, pow_one]; ring


/-- 多项式恒等式：x^n - y^n = (x - y) * Σᵢ x^i * y^(n-1-i) -/
theorem pow_sub_pow_factor (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  (x - y) * (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  have h1 := sum_diff_helper_1 x y n hn
  have h2 := sum_diff_helper_2 x y n hn
  have h3 := sum_diff_helper_3 x y n hn
  rw [sub_mul]
  calc x * (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) -
       y * (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i))
      = x * (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i) + x^(n-1)) -
        y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i) + y^(n-1)) := by rw [← h1, ← h2]
    _ = (x * (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i))) -
        y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i))
        + x*x^(n-1) - y*y^(n-1) := by ring
    _ = (y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i))) -
        y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i))
        + x*x^(n-1) - y*y^(n-1) := by congr 3;
    _ = x*x^(n-1) - y*y^(n-1) := by ring
    _ = x^n - y^n := by rw [mul_comm x, mul_comm y,
                            ← pow_succ, ← pow_succ,
                            Nat.sub_add_cancel (by omega : 1 ≤ n)]
