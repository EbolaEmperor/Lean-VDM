import LeanVDM.GeVDM
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Finset Matrix BigOperators

def P (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) (k : ℕ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun i j =>
  let i0 : Fin n := ⟨0, by omega⟩
  let i' : Fin n := ⟨i.val + 1, by omega⟩
  let j' : Fin n := ⟨j.val + 1, by omega⟩
  if j.val < n - 2 ∧ i.val < k then
    (u i' - u i0) * u i' ^ j.val
  else if j.val < n - 2 ∧ i.val ≥ k then
    u i' ^ j.val
  else if i.val < k then
    (u i' - u i0) * (u i' + u i0) * u i' ^ (n - 2)
  else
    (u i' + u i0) * u i' ^ (n - 2)

/-- 当 P 矩阵的行变换界限从 k 增加到 k+1 时，
    行列式会多出一个因子 (u (k+1) - u 0) -/
lemma det_P_succ (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) (k : ℕ)
    (hk_bound : k + 2 ≤ n) :
  let kn : Fin n := ⟨k + 1, by omega⟩
  det (P n (by omega) u (k+1)) =
  (u kn - u ⟨0, by omega⟩) * det (P n (by omega) u k)
     := by
  sorry

lemma det_P_product_succ (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) (k : ℕ) (hk : k ≤ n - 1) :
  det (P n (by omega) u k) =
    (∏ i : Fin k, (u ⟨i.val + 1, by omega⟩ - u ⟨0, by omega⟩)) *
    det (P n (by omega) u 0) := by
  induction k with
  | zero => simp
  | succ k' ih =>
    have hk' : k' ≤ n - 1 := by omega
    have h_trans : det (P n hn u (k' + 1)) =
                   (u ⟨k' + 1, by omega⟩ - u ⟨0, by omega⟩) * det (P n hn u k') := by
      apply det_P_succ n hn u k' (by omega)
    rw [h_trans, ih hk']
    rw [← mul_assoc]
    congr 1
    by_cases hk'_zero : k' = 0
    · subst hk'_zero
      norm_num
      simp
    · have hk'_pos : 0 < k' := Nat.pos_of_ne_zero hk'_zero
      simp [Fin.prod_univ_castSucc, mul_comm]

lemma det_P_product (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) :
  det (P n (by omega) u (n-1)) =
    (∏ i : Fin (n - 1), (u ⟨i.val + 1, by omega⟩ - u ⟨0, by omega⟩)) *
    det (P n (by omega) u 0 ) := by
  apply det_P_product_succ n hn u (n-1) (by omega)
