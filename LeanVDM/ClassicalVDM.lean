import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators

open Matrix BigOperators Finset

namespace ClassicalVDMs

variable {F : Type*} [Field F]

def ClassicalVDM (n : ℕ) (u : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => u i ^ (j : ℕ)

/-- 辅助引理：构造经过列操作后的矩阵 -/
def ReducedVDM (n : ℕ) (u : Fin (n + 1) → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  fun i j => if j = 0 then 1 else (u i ^ (j : ℕ) - u 0 * u i ^ ((j : ℕ) - 1))

/-- ReducedVDM 按第一行展开的子矩阵 -/
def ReducedSubmatrix (n : ℕ) (u : Fin (n + 1) → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => ReducedVDM n u i.succ j.succ

/-- ReducedSubmatrix 与缩放的 ClassicalVDM 的关系 -/
lemma reduced_submatrix_eq_scaled (n : ℕ) (u : Fin (n + 1) → F) :
  ∀ i j, ReducedSubmatrix n u i j =
    (u i.succ - u 0) * u i.succ ^ (j : ℕ) := by
  intro i j
  simp only [ReducedSubmatrix, ReducedVDM]
  have : j.succ ≠ 0 := Fin.succ_ne_zero j
  simp only [this, ↓reduceIte]
  have hj : (j.succ : ℕ) ≥ 1 := Nat.succ_pos j
  calc u i.succ ^ (j.succ : ℕ) - u 0 * u i.succ ^ ((j.succ : ℕ) - 1)
      = (u i.succ - u 0) * u i.succ ^ ((j.succ : ℕ) - 1) := by
        conv_lhs => arg 1; rw [← Nat.sub_add_cancel hj, pow_succ]
        ring
    _ = (u i.succ - u 0) * u i.succ ^ (j : ℕ) := by
        have : (j.succ : ℕ) - 1 = (j : ℕ) := by simp [Fin.val_succ]
        rw [this]

/-- 列操作引理：通过列操作将 Vandermonde 矩阵转换为 ReducedVDM -/
lemma vandermonde_to_reduced (n : ℕ) (u : Fin (n + 1) → F) :
  det (ClassicalVDM (n + 1) u) = det (ReducedVDM n u) := by
  apply det_eq_of_forall_col_eq_smul_add_pred (fun _ => u 0)
  · -- 第0列保持不变：ClassicalVDM 和 ReducedVDM 的第0列都是全1
    intro i
    simp [ClassicalVDM, ReducedVDM, pow_zero]
  · -- 对于第 j.succ 列，有列操作关系
    intro i j
    simp only [ClassicalVDM]
    rw [ReducedVDM]
    have : j.succ ≠ 0 := Fin.succ_ne_zero j
    rw [if_neg this]
    simp only [Fin.coe_castSucc, Fin.val_succ]
    have h1 : (j : ℕ) + 1 - 1 = (j : ℕ) := by omega
    rw [h1]
    ring

/-- ReducedVDM 的第一行为 [1, 0, 0, ...] -/
lemma reduced_first_row (n : ℕ) (u : Fin (n + 1) → F) :
  ∀ j : Fin (n + 1), ReducedVDM n u 0 j = if j = 0 then 1 else 0 := by
  intro j
  simp only [ReducedVDM]
  split_ifs with h
  · rfl
  · have hj : (j : ℕ) ≥ 1 := by
      have : j ≠ 0 := h
      have : 0 < (j : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_of_ne this)
      omega
    calc u 0 ^ (j : ℕ) - u 0 * u 0 ^ ((j : ℕ) - 1)
        = u 0 * u 0 ^ ((j : ℕ) - 1) - u 0 * u 0 ^ ((j : ℕ) - 1) := by
            conv_lhs => arg 1; rw [← Nat.sub_add_cancel hj, pow_succ]; ring_nf
      _ = 0 := sub_self _

/-- ReducedVDM 的其他行可以提取因子 (u_i - u_0) -/
lemma reduced_row_factor (n : ℕ) (u : Fin (n + 1) → F) (i : Fin n) (j : Fin (n + 1)) :
  ReducedVDM n u i.succ j =
    if j = 0 then 1 else (u i.succ - u 0) * u i.succ ^ ((j : ℕ) - 1) := by
  simp only [ReducedVDM]
  split_ifs with h
  · rfl
  · have hj : (j : ℕ) ≥ 1 := by
      have : j ≠ 0 := h
      have : 0 < (j : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_of_ne this)
      omega
    have : u i.succ ^ (j : ℕ) - u 0 * u i.succ ^ ((j : ℕ) - 1) =
           (u i.succ - u 0) * u i.succ ^ ((j : ℕ) - 1) := by
      conv_lhs => arg 1; rw [← Nat.sub_add_cancel hj, pow_succ]
      ring
    exact this

/-- 简化的 Vandermonde 矩阵与原矩阵的关系 -/
lemma vandermonde_reduction (n : ℕ) (u : Fin (n + 1) → F) :
  let u' : Fin n → F := fun i => u i.succ
  det (ClassicalVDM (n + 1) u) =
    (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') := by
  intro u'
  -- Step 1: 使用列操作将 ClassicalVDM 转换为 ReducedVDM
  rw [vandermonde_to_reduced]

  -- Step 2: 按第一行展开 ReducedVDM
  rw [det_succ_row_zero]

  -- Step 3: 第一行是 [1, 0, 0, ...] (用 reduced_first_row)
  have h_first_row := reduced_first_row n u
  conv_lhs =>
    arg 2; ext j
    rw [h_first_row j]

  -- Step 4: 简化求和，只有 j=0 的项非零
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, ite_true, mul_one]

    have h_submatrix : ∀ i j, (ReducedVDM n u).submatrix Fin.succ (0 : Fin (n+1)).succAbove i j =
        (u i.succ - u 0) * u' i ^ (j : ℕ) := by
      intro i j
      simp only [submatrix, Fin.succAbove_zero]
      exact reduced_submatrix_eq_scaled n u i j

    let M : Matrix (Fin n) (Fin n) F := fun i j => (u i.succ - u 0) * u' i ^ (j : ℕ)
    have : (ReducedVDM n u).submatrix Fin.succ (0 : Fin (n+1)).succAbove = M := by
      ext i j; exact h_submatrix i j
    rw [this]

    have : det M = (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') := by
      simp only [M]
      rw [← det_mul_column (fun (i : Fin n) => u i.succ - u 0)]
      congr 1
    rw [this]
  · intro j _ hj
    simp only [if_neg hj, zero_mul, mul_zero]
  · simp

/-- 乘积重排引理：将 Fin (n+1) 上的乘积分解为第一项和剩余项 -/
lemma prod_ioi_succ (n : ℕ) (u : Fin (n + 1) → F) :
  (∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i)) =
    (∏ i : Fin n, (u i.succ - u 0)) *
    (∏ i : Fin n, ∏ j ∈ Ioi i, (u j.succ - u i.succ)) := by
  -- 使用 Fin.prod_univ_succ 将 Fin (n+1) 上的乘积分解为 i=0 和 i=k.succ 两部分
  rw [Fin.prod_univ_succ]
  congr 1

  -- 简化 i=0 的情况：Ioi 0 对应所有 j > 0，即所有 (Fin n).succ
  · have : Ioi (0 : Fin (n + 1)) = Finset.univ.image Fin.succ := by
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨fun hj => ⟨j.pred (Fin.pos_iff_ne_zero.mp hj),
                          Fin.succ_pred j (Fin.pos_iff_ne_zero.mp hj)⟩,
              fun ⟨i, hi⟩ => hi ▸ Fin.succ_pos i⟩
    rw [this, Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succ_inj.mp hab

  -- 简化 i=k.succ 的情况
  · conv_lhs => arg 2; ext k; rw [show Fin.succ k = k.succ from rfl]
    congr 1
    ext k
    have : Ioi (Fin.succ k) = (Ioi k).image Fin.succ := by
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_image]
      constructor
      · intro hj
        have hpos : 0 < j := Nat.zero_lt_of_lt (Nat.lt_trans (Fin.succ_pos k) hj)
        refine ⟨j.pred (Fin.pos_iff_ne_zero.mp hpos),
                ⟨?_, Fin.succ_pred j (Fin.pos_iff_ne_zero.mp hpos)⟩⟩
        rw [← Fin.succ_lt_succ_iff, Fin.succ_pred j (Fin.pos_iff_ne_zero.mp hpos)]
        exact hj
      · intro ⟨i, hi, heq⟩
        rw [← heq]
        exact Fin.succ_lt_succ_iff.mpr hi
    rw [this, Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succ_inj.mp hab

/-- Vandermonde 矩阵的行列式等于所有 (u_j - u_i) 的乘积，其中 i < j -/
theorem det_ClassicalVDM (n : ℕ) (u : Fin n → F) :
  det (ClassicalVDM n u) = ∏ i : Fin n, ∏ j ∈ Ioi i, (u j - u i) := by
  induction n with
  | zero =>
    simp [det_isEmpty, Finset.prod_empty]
  | succ n ih =>
    let u' : Fin n → F := fun i => u i.succ

    have h_reduction : det (ClassicalVDM (n + 1) u) =
      (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') :=
        vandermonde_reduction n u

    have h_ih : det (ClassicalVDM n u') =
      ∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i) := ih u'

    have h_prod : (∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i)) =
      (∏ i : Fin n, (u i.succ - u 0)) *
      (∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i)) := prod_ioi_succ n u

    calc det (ClassicalVDM (n + 1) u)
        = (∏ i : Fin n, (u i.succ - u 0)) * det (ClassicalVDM n u') :=
            h_reduction
      _ = (∏ i : Fin n, (u i.succ - u 0)) *
          (∏ i : Fin n, ∏ j ∈ Ioi i, (u' j - u' i)) := by
            rw [h_ih]
      _ = ∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (u j - u i) := by
            rw [← h_prod]

theorem det_ClassicalVDM_non_zero (n : ℕ) (u : Fin n → F)
        (hu : ∀ i j : Fin n, i ≠ j → u i ≠ u j) :
  det (ClassicalVDM n u) ≠ 0 := by
  rw [det_ClassicalVDM n u]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij_gt : i < j := by simpa [Finset.mem_Ioi] using hj
  have hne_ij : u j ≠ u i := hu j i (ne_of_gt hij_gt)
  exact sub_ne_zero.mpr hne_ij

theorem rank_ClassicalVDM_full (n : ℕ) (u : Fin n → F)
        (hu : ∀ i j : Fin n, i ≠ j → u i ≠ u j) :
  rank (ClassicalVDM n u) = n  := by
  have hdet : det (ClassicalVDM n u) ≠ 0 :=
    det_ClassicalVDM_non_zero n u hu
  have hUnit : IsUnit (det (ClassicalVDM n u)) :=
    isUnit_iff_ne_zero.mpr hdet
  simpa [Matrix.rank_one, Fintype.card_fin] using
    (Matrix.rank_mul_eq_left_of_isUnit_det
      (A := ClassicalVDM n u)
      (B := (1 : Matrix (Fin n) (Fin n) F))
      hUnit)

end ClassicalVDMs
