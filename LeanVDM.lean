import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators

open Matrix BigOperators Finset

def ClassicalVDM (n : ℕ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i ^ (j : ℕ)


lemma sum_diff_helper_1 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) =
  (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i)) + x^(n-1) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 1 + n' - 1 = n' := by omega
  simp only [h1]
  rw [Nat.add_comm 1 n', Finset.sum_range_succ]
  congr 1
  rw [Nat.sub_self]
  simp

lemma sum_diff_helper_2 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) =
  (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i)) + y^(n-1) := by
  have : range n = insert 0 (Ico 1 n) := by
    ext i; simp [Finset.mem_Ico]; omega
  rw [this, Finset.sum_insert]
  · simp [pow_zero, one_mul, add_comm]
  · simp

lemma sum_diff_helper_3 (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
  x * (∑ i ∈ range (n-1), x ^ i * y ^ (n - 1 - i)) =
  y * (∑ i ∈ Ico 1 n, x ^ i * y ^ (n - 1 - i)) := by
  sorry

/-- 多项式恒等式：x^n - y^n = (x - y) * Σᵢ x^i * y^(n-1-i) -/
lemma pow_sub_pow_factor (x y : ℝ) (n : ℕ) (hn : n ≥ 1) :
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

/-- 简化的 Vandermonde 矩阵与原矩阵的关系 -/
lemma vandermonde_reduction (n : ℕ) (u : Fin (n + 1) → ℝ) :
  let u' : Fin n → ℝ := fun i => u i.succ
  det (ClassicalVDM (n + 1) u) =
    (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') := by
  sorry

/-- 乘积重排引理：将 Fin (n+1) 上的乘积分解为第一项和剩余项 -/
lemma prod_ioi_succ (n : ℕ) (u : Fin (n + 1) → ℝ) :
  (∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i)) =
    (∏ i : Fin n, (u i.succ - u 0)) *
    (∏ i : Fin n, ∏ j ∈ Ioi i, (u j.succ - u i.succ)) := by
  sorry

/-- Vandermonde 矩阵的行列式等于所有 (u_j - u_i) 的乘积，其中 i < j -/
lemma det_ClassicalVDM (n : ℕ) (u : Fin n → ℝ) :
  det (ClassicalVDM n u) = ∏ i : Fin n, ∏ j ∈ Ioi i, (u j - u i) := by
  -- 证明策略：使用关于 n 的归纳法
  induction n with
  | zero =>
    -- 基础情况：0×0 矩阵的行列式为 1，空乘积也是 1
    simp [det_isEmpty, Finset.prod_empty]
  | succ n ih =>
    -- 归纳步骤：假设对 n 成立，证明对 n+1 成立
    -- 定义 u' 为去掉第一个元素后的向量
    let u' : Fin n → ℝ := fun i => u i.succ

    -- 步骤 1: 使用列操作将矩阵简化（从每列减去第一列的倍数）
    -- 这样可以从每一行（除第一行外）提取因子 (uᵢ - u₀)
    have h_reduction : det (ClassicalVDM (n + 1) u) =
      (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') :=
        vandermonde_reduction n u

    -- 步骤 2: 应用归纳假设到 u'
    have h_ih : det (ClassicalVDM n u') =
      ∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i) := ih u'

    -- 步骤 3: 重写右侧的乘积
    have h_prod : (∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i)) =
      (∏ i : Fin n, (u i.succ - u 0)) *
      (∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i)) := prod_ioi_succ n u

    -- 步骤 4: 组合所有等式
    calc det (ClassicalVDM (n + 1) u)
        = (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') :=
            h_reduction
      _ = (∏ i : Fin n, (u i.succ - u 0)) *
          (∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i)) := by
            rw [h_ih]
      _ = ∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i) := by
            rw [← h_prod]
