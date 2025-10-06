import LeanVDM.GeVDM
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Finset Matrix BigOperators

def T (n : ℕ) (hn : n > 0) (u : Fin n → ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  let i0 : Fin n := ⟨0, hn⟩
  fun i j =>
    if j ≤ k then
      u i ^ j.val
    else if i.val = 0 then
      0
    else if j.val < n - 1 then
      (u i - u i0) * u i ^ (j.val - 1)
    else
      (u i ^ 2 - u i0 ^ 2) * u i ^ (n - 2)

lemma T_col_trans (n : ℕ) (hn : n > 0) (u : Fin n → ℝ) (k : Fin n) (hk : k.val < n - 2) :
    let hk1 : k.val + 1 < n := by omega
    let k' : Fin n := ⟨k.val + 1, hk1⟩
    let i0 : Fin n := ⟨0, hn⟩
    T n hn u k = updateCol (T n hn u k') k'
      (fun j => (T n hn u k') j k' + (-(u i0)) • (T n hn u k') j k) := by
  intro hk1 k' i0
  ext i j
  simp only [updateCol, T, smul_eq_mul]
  -- 对 j 进行分类：j = k' 或 j ≠ k'
  by_cases hj_eq : j = k'
  · -- 情况 1: j = k'，列被更新
    simp [hj_eq]
    have hk'_not_le_k : ¬k' ≤ k := by
      intro h
      have : k'.val ≤ k.val := h
      simp only [k'] at this
      omega
    have hk_le_k' : k ≤ k' := by
      show k ≤ k'
      simp only [k']
      omega

    simp only [hk'_not_le_k, hk_le_k', ↓reduceIte]

    -- 现在需要对 i.val = 0 和 k'.val < n-1 进行分类讨论
    by_cases hi_eq : i.val = 0
    · -- i.val = 0
      simp [hi_eq]
      have hi_eq_i0 : i = i0 := by ext; exact hi_eq
      rw [hi_eq_i0]
      have hk'_val : k'.val = k.val + 1 := rfl
      have : u i0 ^ k'.val = u i0 * u i0 ^ k.val := by
        rw [hk'_val]
        rw [pow_succ]
        ring
      rw [this]
      ring
    · -- i.val ≠ 0
      by_cases hk'_lt : k'.val < n - 1
      · -- k'.val < n - 1
        simp only [hi_eq, hk'_lt, ↓reduceIte]
        -- 统一 ⟨0, hn⟩ 和 i0 的表示
        have hi0_eq : (⟨0, hn⟩ : Fin n) = i0 := rfl
        simp only [hi0_eq]
        -- 使用 k' = k + 1
        have hk'_val : k'.val = k.val + 1 := rfl
        rw [hk'_val, pow_succ]
        -- 现在需要简化 u i ^ (1 + k - 1) = u i ^ k
        simp only [Nat.add_sub_cancel]
        ring
      · -- k'.val ≥ n - 1
        have hk'_eq : k'.val = n - 1 := by omega
        have : k.val + 1 = n - 1 := by simpa [k'] using hk'_eq
        have hk_eq : k.val = n - 2 := by omega
        omega
  · -- 情况 2: j ≠ k'，列不变
    simp [hj_eq]
    by_cases hj_le_k : j ≤ k
    · have hj_le_k' : j ≤ k' := by
        change j.val ≤ k'.val
        have : j.val < k'.val := by
          calc j.val ≤ k.val := hj_le_k
            _ < k.val + 1 := Nat.lt_succ_self _
            _ = k'.val := rfl
        omega
      simp [hj_le_k, hj_le_k']
    · by_cases hj_le_k' : j ≤ k'
      · have hj_val : j.val = k'.val := by
          have : ¬j.val ≤ k.val := hj_le_k
          have : j.val ≤ k'.val := hj_le_k'
          have : k'.val = k.val + 1 := rfl
          omega
        have : j = k' := by ext; exact hj_val
        exact absurd this hj_eq
      · simp [hj_le_k, hj_le_k']

lemma det_eq_T_col_trans (n : ℕ) (hn : n > 0) (u : Fin n → ℝ) (k : Fin n) (hk : k.val < n - 2) :
    let hk1 : k.val + 1 < n := by omega
    let k' : Fin n := ⟨k.val + 1, hk1⟩
    det (T n hn u k) = det (T n hn u k') := by
  intro hk1 k'
  let i0 : Fin n := ⟨0, hn⟩
  have hne : k' ≠ k := by
    intro h
    have : k'.val = k.val := by rw [h]
    simp only [k'] at this
    omega
  rw [T_col_trans n hn u k hk]
  exact det_updateCol_add_smul_self (T n hn u k') hne (-(u i0))

lemma det_column_transform (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ)
    (e : Fin n → ℕ) (he : ∀ i : Fin n, i.val < n-1 → e i = i.val)
    (iLast : Fin n) (hiLast : iLast.val = n-1)
    (heN : e iLast = n)
    (i0 : Fin n) (hi0 : i0.val = 0):
  det (GeVDM n u e) = det (T n (by omega : n > 0) u ⟨n-2, by omega⟩) := by
  let hn_pos : n > 0 := by omega
  have hn2 : n - 2 < n := by omega
  let n2 : Fin n := ⟨n-2, hn2⟩
  let M := T n hn_pos u n2
  have hn1 : n - 1 < n := Nat.pred_lt (Nat.ne_zero_of_lt hn_pos)
  have hne : (⟨n-2, hn2⟩ : Fin n) ≠ ⟨n-1, hn1⟩ := by
    intro h
    simp at h
    omega
  -- 首先证明 M 等于对 GeVDM 进行列变换后的结果
  -- 注意：列变换是第 n-1 列加上第 n-2 列的 (-u i0^2) 倍
  have hM : M = updateCol (GeVDM n u e) ⟨n-1, hn1⟩
      (fun k => (GeVDM n u e) k ⟨n-1, hn1⟩ + (-(u i0 ^ 2)) • (GeVDM n u e) k ⟨n-2, hn2⟩) := by
    ext i j
    simp only [updateCol, of_apply, GeVDM, smul_eq_mul, Function.update]
    -- 对列索引 j 进行分类讨论
    split_ifs with hj
    · -- 情况 1: j = ⟨n-1, hn1⟩ (最后一列，被更新的列)
      subst hj
      -- 首先获取 e 的值
      have he_last : e ⟨n-1, hn1⟩ = n := by
        have : (⟨n-1, hn1⟩ : Fin n) = iLast := by ext; simp; exact hiLast.symm
        rw [this]; exact heN
      have he_n2 : e ⟨n-2, hn2⟩ = n - 2 := by
        apply he; simp; omega
      -- 计算 M i ⟨n-1, hn1⟩ 的值，需要分情况讨论 i 是否等于 i0
      by_cases hi_eq : i = i0
      · -- 子情况: i = i0
        rw [hi_eq]
        -- 此时 M i0 ⟨n-1, hn1⟩ = 0
        have hM_val : M i0 ⟨n-1, hn1⟩ = 0 := by
          simp only [M, T]
          -- ⟨n-1, hn1⟩ > n2，因为 n-1 > n-2
          have h_not_le : ¬⟨n-1, hn1⟩ ≤ n2 := by
            simp [n2]
            omega
          -- i0.val = 0
          have h_i0 : i0.val = 0 := hi0
          simp [h_not_le, h_i0]
        rw [hM_val, he_last, he_n2]
        -- 需要证明: 0 = u i0 ^ n + -(u i0^2) * u i0 ^ (n - 2)
        -- 即: 0 = u i0 ^ n - u i0^2 * u i0 ^ (n - 2)
        have h_pow : u i0 ^ n = u i0 ^ 2 * u i0 ^ (n - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [h_pow]
        ring
      · -- 子情况: i ≠ i0
        have hM_val : M i ⟨n-1, hn1⟩ = (u i ^ 2 - u i0 ^ 2) * u i ^ (n - 2) := by
          simp only [M, T]
          -- ⟨n-1, hn1⟩ > n2，因为 n-1 > n-2
          have h_not_le : ¬⟨n-1, hn1⟩ ≤ n2 := by
            simp [n2]
            omega
          -- i.val ≠ 0
          have h_i_ne : i.val ≠ 0 := by
            intro h_contra
            have : i = i0 := by
              ext
              rw [h_contra]
              exact hi0.symm
            exact hi_eq this
          -- j.val = n-1 不满足 j.val < n-1
          have h_not_lt : ¬(n - 1 : ℕ) < n - 1 := by omega
          -- 展开 if 语句
          simp only [h_not_le, ↓reduceIte, h_i_ne, h_not_lt]
          -- 需要证明 T 中 i0 的定义
          have hi0_eq : (⟨0, hn_pos⟩ : Fin n) = i0 := by
            ext
            simp [hi0]
          rw [hi0_eq]
        rw [hM_val, he_last, he_n2]
        -- 需要证明: (u i ^ 2 - u i0 ^ 2) * u i ^ (n - 2) = u i ^ n + -(u i0^2) * u i ^ (n - 2)
        have h_pow : u i ^ n = u i ^ 2 * u i ^ (n - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [h_pow]
        ring
    · -- 情况 2: j ≠ ⟨n-1, hn1⟩ (其他列保持不变)
      -- 需要证明 M i j = u i ^ e j
      by_cases hj0 : j.val = 0
      · -- 子情况 2.1: j.val = 0
        have hM_j : M i j = u i ^ 0 := by
          simp only [M, T]
          -- j ≤ n2 因为 j.val = 0 < n-2
          have : j ≤ n2 := by
            simp [n2]
            omega
          simp [this, hj0]
        rw [hM_j]
        -- 需要证明 e j = 0
        have hej : e j = 0 := by
          have : j.val < n - 1 := by simp [hj0]; omega
          rw [he j this]
          exact hj0
        rw [hej]
      · -- j.val ≠ 0
        by_cases hj_lt : j.val < n - 1
        · -- 子情况 2.2: 0 < j.val < n-1
          have hM_j : M i j = u i ^ j.val := by
            simp only [M, T]
            -- j ≤ n2 因为 j.val < n-1 意味着 j.val ≤ n-2
            have hj_le_n2 : j ≤ n2 := by
              change j.val ≤ n2.val
              simp only [n2]
              omega
            simp only [hj_le_n2, ↓reduceIte]
          rw [hM_j]
          have hej : e j = j.val := by
            apply he; exact hj_lt
          rw [hej]
        · -- 子情况 2.3: j.val ≥ n-1 且 j ≠ ⟨n-1, hn1⟩，导致矛盾
          exfalso
          have hj_eq : j.val = n - 1 := by omega
          have : j = ⟨n-1, hn1⟩ := by ext; simp; exact hj_eq
          exact hj this
  -- 现在使用 hM 和行列式性质
  change det (GeVDM n u e) = det M
  rw [hM]
  rw [det_updateCol_add_smul_self (GeVDM n u e) (i := ⟨n-1, hn1⟩) (j := ⟨n-2, hn2⟩)
      hne.symm (-(u i0 ^ 2))]

-- 从 T u k 递归地降到 T u 0（使用 det_eq_T_col_trans）
lemma det_T_to_zero (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) (k : ℕ) (hk : k ≤ n - 2) :
    det (T n (by omega : n > 0) u ⟨k, by omega⟩) =
    det (T n (by omega : n > 0) u ⟨0, by omega⟩) := by
  have hn_pos : n > 0 := by omega
  -- 对 k 进行归纳
  induction k with
  | zero =>
    -- k = 0，目标两边相等
    rfl
  | succ k' ih =>
    -- 归纳步骤：假设对 k' 成立，证明对 k'+1 成立
    have hk' : k' ≤ n - 2 := by omega
    have hk'_lt : k' < n - 2 := by omega
    -- 使用 det_eq_T_col_trans: det (T u k') = det (T u (k'+1))
    have h_trans : det (T n hn_pos u ⟨k', by omega⟩) = det (T n hn_pos u ⟨k' + 1, by omega⟩) := by
      exact det_eq_T_col_trans n hn_pos u ⟨k', by omega⟩ hk'_lt
    -- 使用归纳假设和传递性
    rw [← h_trans]
    exact ih hk'

-- 主定理：det (GeVDM n u e) = det (T u 0)
theorem det_GeVDM_to_T0 (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ)
    (e : Fin n → ℕ) (he : ∀ i : Fin n, i.val < n-1 → e i = i.val)
    (iLast : Fin n) (hiLast : iLast.val = n-1)
    (heN : e iLast = n)
    (i0 : Fin n) (hi0 : i0.val = 0):
  det (GeVDM n u e) = det (T n (by omega : n > 0) u ⟨0, by omega⟩) := by
  -- 先用 det_column_transform 得到 det (GeVDM n u e) = det (T u (n-2))
  rw [det_column_transform n (by omega) u e he iLast hiLast heN i0 hi0]
  -- 再用 det_T_to_zero 从 T u (n-2) 降到 T u 0
  exact det_T_to_zero n hn u (n-2) (by omega)

def SimpM (n : ℕ) (hn : n ≥ 2) (u : Fin n → ℝ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun i j =>
  let i0 : Fin n := ⟨0, by omega⟩
  let i' : Fin n := ⟨i.val + 1, by omega⟩
  let j' : Fin n := ⟨j.val + 1, by omega⟩
  if j.val < n - 2 then
    u i' ^ j.val
  else
    (u i' + u i0) * u i' ^ (n - 2)

theorem det_GeVDM_example1 (n : ℕ) (hn : n ≥ 1) (u : Fin n → ℝ)
        (e : Fin n → ℕ) (he : ∀ i : Fin n, i.val < n-1 → e i = i.val)
        (iLast : Fin n) (hiLast : iLast.val = n-1)
        (heN : e iLast = n) :
  det (GeVDM n u e) = (∑ i : Fin n, u i) * det (ClassicalVDM n u) := by
  -- 对 n 进行归纳
  match n, hn with
  | 1, _ =>
    -- 基础情况: n = 1
    -- 此时 GeVDM 和 ClassicalVDM 都是 1x1 矩阵
    have h0 : iLast = 0 := by
      ext
      exact hiLast
    rw [h0] at heN
    simp [GeVDM, ClassicalVDM]
    rw [heN]
    ring
  | n' + 2, _ =>
    -- 归纳步骤: n ≥ 2
    -- 假设对于 n' + 1，定理成立

    let n := n' + 2
    have hn_pos : n > 0 := by omega
    have hn_ge2 : n ≥ 2 := by omega

    let i0 : Fin n := ⟨0, hn_pos⟩
    have hi0 : i0.val = 0 := rfl

    -- 定义矩阵 M，它应该等于 T n hn_pos u ⟨0, hn_pos⟩
    let M : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      if j.val = 0 then
        1
      else if i.val = 0 then
        0
      else if j.val < n - 1 then
        (u i - u i0) * u i ^ (j.val - 1)
      else
        (u i - u i0) * (u i + u i0) * u i ^ (n - 2)

    -- 证明 M = T n hn_pos u ⟨0, hn_pos⟩
    have hM_eq_T : M = T n hn_pos u ⟨0, hn_pos⟩ := by
      ext i j
      simp only [M, T]
      -- T 的定义中，当 k = 0 时，j ≤ k 只在 j = 0 时成立
      by_cases hj0 : j.val = 0
      · -- j.val = 0
        have hj_le : j ≤ ⟨0, hn_pos⟩ := by
          change j.val ≤ 0
          exact Nat.le_of_eq hj0
        have hj_eq : j = ⟨0, hn_pos⟩ := by
          ext
          exact hj0
        simp [hj_eq]
      · -- j.val ≠ 0
        have hj_not_le : ¬j ≤ ⟨0, hn_pos⟩ := by
          intro h
          have : j.val ≤ 0 := h
          omega
        simp only [hj_not_le, hj0, ↓reduceIte]
        -- 需要证明 T 中 i0 的定义与外部一致
        have hi0_eq : (⟨0, hn_pos⟩ : Fin n) = i0 := rfl
        rw [hi0_eq]
        congr 1
        split_ifs
        · rfl
        · ring

    have hGeVDM_eq_T0 : det (GeVDM n u e) = det (T n hn_pos u ⟨0, hn_pos⟩) := by
      exact det_GeVDM_to_T0 n hn_ge2 u e he iLast hiLast heN i0 hi0
    rw [hGeVDM_eq_T0, ← hM_eq_T]

    let M1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun i j =>
      let i' : Fin n := ⟨i.val + 1, by omega⟩
      let j' : Fin n := ⟨j.val + 1, by omega⟩
      if j.val < n - 2 then
        (u i' - u i0) * u i' ^ j.val
      else
        (u i' - u i0) * (u i' + u i0) * u i' ^ (n - 2)

    -- 证明 det M = det M1（利用第一行展开）
    have hdet_M_eq_M1 : det M = det M1 := by
      -- M 的第一行是 [1, 0, 0, ..., 0]
      have hM_00 : M 0 0 = 1 := by
        simp only [M]
        simp
      -- M 第一行除了第一个元素外都是 0
      have hM_row0 : ∀ j : Fin n, j ≠ 0 → M 0 j = 0 := by
        intro j hj
        simp only [M]
        by_cases hj0 : j.val = 0
        · have : j = 0 := by ext; exact hj0
          exact absurd this hj
        · simp only [hj0, ↓reduceIte]
          have : (0 : Fin n).val = 0 := rfl
          simp
      -- M1 是 M 的子矩阵
      have hM1_eq : ∀ i j, M1 i j = M (Fin.succ i) (Fin.succ j) := by
        intro i j
        simp only [M1, M, Fin.succ]
        -- 证明 i.val + 1 ≠ 0 和 j.val + 1 ≠ 0
        have hi_ne : i.val + 1 ≠ 0 := Nat.succ_ne_zero _
        have hj_ne : j.val + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [hj_ne, ↓reduceIte, hi_ne]
        -- 证明条件等价: j < n-2 ↔ j+1 < n-1
        by_cases h : j.val < n - 2
        · have h' : j.val + 1 < n - 1 := by omega
          simp only [h, h', ↓reduceIte]
          -- j.val + 1 - 1 = j.val
          have : j.val + 1 - 1 = j.val := by omega
          rw [this]
        · have h' : ¬(j.val + 1 < n - 1) := by omega
          simp only [h, h', ↓reduceIte]
      -- 直接使用行列式展开公式
      have det_M_expand : det M =
          ∑ j : Fin n, (-1) ^ (j : ℕ) * M 0 j *
            det (M.submatrix Fin.succ j.succAbove) := by
        -- n = n' + 2 = (n' + 1).succ，所以可以直接应用
        exact det_succ_row_zero M
      rw [det_M_expand]
      -- 由于 M 0 j = 0 for j ≠ 0，求和中只有 j = 0 的项非零
      rw [Fintype.sum_eq_single (0 : Fin n)]
      · -- j = 0 的情况
        simp only [Fin.val_zero, pow_zero, one_mul]
        rw [hM_00]
        simp only [one_mul]
        -- 现在需要证明 det (M.submatrix Fin.succ (0 : Fin n).succAbove) = det M1
        congr 1
        ext i j
        -- 展开 submatrix 定义: (M.submatrix f g) i j = M (f i) (g j)
        have h_succAbove : (0 : Fin n).succAbove j = j.succ := by
          simp only [Fin.succAbove]
          split_ifs with h
          · exact absurd h (Fin.not_lt_zero _)
          · rfl
        change M (Fin.succ i) ((0 : Fin n).succAbove j) = M1 i j
        rw [h_succAbove]
        exact (hM1_eq i j).symm
      · -- j ≠ 0 的情况，证明该项为 0
        intro j hj
        rw [hM_row0 j hj]
        ring

    rw [hdet_M_eq_M1]

    let SM := SimpM n (by omega) u
    let v : Fin (n-1) → ℝ := fun i => u ⟨i.val + 1, by omega⟩ - u i0

    have hM1_eq_v_SM : M1 = of fun i j => v i * SM i j := by
      ext i j
      simp only [M1, SM, SimpM, of_apply, v]
      by_cases hj : j.val < n - 2
      · simp [hj]
      · simp [hj]
        have hu0_eq : u 0 = u i0 := by congr 1
        rw [hu0_eq]
        ring

    rw [hM1_eq_v_SM, det_mul_column]

    let v1 : Fin (n-1) → ℝ := fun i => u ⟨i.val + 1, by omega⟩ ^ (n - 1)
    let v2 : Fin (n-1) → ℝ := fun i => u ⟨0, by omega⟩ * u ⟨i.val + 1, by omega⟩ ^ (n - 2)

    have decomp_SM : SM = (updateCol SM ⟨n-2, by omega⟩ <| v1 + v2) := by
      ext i j
      simp only [updateCol, SM, v1, v2, Pi.add_apply]
      by_cases hj : j = ⟨n-2, by omega⟩
      · simp [hj]
        have hj_val : j.val = n - 2 := by simp [hj]
        have hj_not_lt : ¬(j.val < n - 2) := by omega
        simp only [SimpM]
        have : ¬(n - 2 < n - 2) := by omega
        simp
        let ui' := u ⟨i.val + 1, by omega⟩
        suffices ui' * ui' ^ (n - 2) = ui' ^ (n - 1) by
          linear_combination this
        rw [← pow_succ']
        congr 1
      · simp [hj]

    let u_trunc : Fin (n-1) → ℝ := fun i => u ⟨i.val + 1, by omega⟩
    let SM2 := updateCol SM ⟨n-2, by omega⟩ v2
    let SM2_0 := ClassicalVDM (n-1) u_trunc

    sorry
