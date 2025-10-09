import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

namespace LeanVDM_example2

def n := 4
def e : Fin n → ℕ := ![0, 1, 10, 11]

def u (α β : ℝ) : Fin n → ℂ :=
  ![exp (I * α),
    exp (I * β),
    exp (I * (α + 0.2 * π)),
    exp (I * (β + 0.2 * π))]

def V (α β : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  GeVDM n (u α β) e

-- 辅助定义：x = e^(iα), y = e^(iβ), t = e^(iπ/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def t := exp (0.2 * π * I)

lemma t_pow_10 : t^10 = 1 := by
  rw [t, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring

lemma t_pow_11 : t^11 = t := by
  calc t^11 = t^10 * t := by ring
          _ = t := by rw [t_pow_10]; simp

-- 说明 u 向量的结构：u = [x, y, t*x, t*y]
lemma u_structure (α β : ℝ) :
  u α β = ![x α, y β, t * x α, t * y β] := by
  ext i
  fin_cases i
  · simp [u, x]; ring_nf
  · simp [u, y]; ring_nf
  · simp [u, x, t]; rw [← Complex.exp_add]; ring_nf
  · simp [u, y, t]; rw [← Complex.exp_add]; ring_nf

def V₀ (α β : ℝ) := !![1, x α, (x α)^10, (x α)^11;
                       1, y β, (y β)^10, (y β)^11;
                       1, t * x α, (x α)^10, t * (x α)^11;
                       1, t * y β, (y β)^10, t * (y β)^11]

-- V 矩阵的显式表达
lemma V_explicit (α β : ℝ) :
  V α β = V₀ α β := by
  ext i j
  rw [V, GeVDM, V₀]
  simp only [u_structure]
  fin_cases i <;> fin_cases j <;> simp [e]
  · rw [mul_pow, t_pow_10]; ring
  · rw [mul_pow, t_pow_11]
  · rw [mul_pow, t_pow_10]; ring
  · rw [mul_pow, t_pow_11]

lemma t_ne_1 : t ≠ 1 := by
  intro h
  rw [t] at h;
  have hn : ∃ n : ℤ, (0.2 * π * I) = n * (2 * π * I) := by
    exact Complex.exp_eq_one_iff.mp h
  rcases hn with ⟨n, hn⟩
  have hC : (n : ℂ) = 0.1 := by
    calc (n : ℂ)
       = (n : ℂ) * 2 / 2 := by simp
     _ = 0.2 / 2 := by
        have := congrArg (fun z : ℂ => z / (π * I)) hn
        field_simp at this; simp [this]
     _ = 0.1 := by ring
  have hR : (n : ℝ) = 0.1 := by exact ofReal_inj.mp hC

  by_cases hn0 : n = 0
  · rw [hn0] at hR; norm_num at hR;
  · have : |(0.1 : ℝ)| ≥ 1 := by
      calc |(0.1 : ℝ)|
         = |(n : ℝ)| := by congr; simp [hR];
       _ = |n| := by norm_num
       _ ≥ 1 := by exact Int.cast_one_le_of_pos (Int.one_le_abs hn0)
    norm_num at this

lemma one_sub_t_ne_0 : 1 - t ≠ 0 := by
  apply sub_ne_zero.mpr (ne_comm.mp t_ne_1)

lemma exp_10_ne (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
  exp (I * (10 * β)) ≠ exp (I * (10 * α)) := by
  intro h
  -- 由 exp 的周期性，exp(z1) = exp(z2) ↔ ∃ n : ℤ, z1 - z2 = 2πni
  have h_period : ∃ n : ℤ, I * (10 * β) - I * (10 * α) = n * (2 * π * I) := by
    rw [Complex.exp_eq_exp_iff_exists_int] at h
    rcases h with ⟨n, hn⟩
    use n
    linear_combination hn

  rcases h_period with ⟨n, hn⟩

  -- 从 I * 10(β - α) = n * 2πI 得到 10(β - α) = 2πn
  have h_eq : 10 * (β - α) = 2 * π * (n : ℝ) := by
    have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h_calc : I * (10 * (β : ℂ) - 10 * (α : ℂ)) = (n : ℂ) * (2 * π * I) := by
      linear_combination hn
    have h_complex : (10 * (β - α) : ℂ) = (n : ℂ) * (2 * π) := by
      field_simp [h_I_ne] at h_calc ⊢
      linear_combination h_calc
    have := congrArg Complex.re h_complex
    simp at this
    ring_nf at this ⊢
    exact this

  -- 但 0 < 10(β - α) < 2π
  have h_range : 0 < 10 * (β - α) ∧ 10 * (β - α) < 2 * π := by
    constructor
    · linarith
    · calc 10 * (β - α)
          < 10 * (0.2 * π) := by linarith
        _ = 2 * π := by ring

  -- 如果 n = 0，则 β = α，矛盾
  by_cases hn_zero : n = 0
  · rw [hn_zero] at h_eq
    simp at h_eq
    linarith

  -- 如果 n ≠ 0，则 |2πn| ≥ 2π，但 10(β-α) < 2π，矛盾
  · have h_abs_ge : |2 * π * (n : ℝ)| ≥ 2 * π := by
      have h_n_abs : |(n : ℝ)| ≥ 1 := by
        have := Int.one_le_abs hn_zero
        exact mod_cast this
      calc |2 * π * (n : ℝ)|
          = 2 * π * |(n : ℝ)| := by
            rw [abs_mul]
            congr 1
            rw [abs_of_pos]
            linarith [Real.pi_pos]
        _ ≥ 2 * π * 1 := by
            apply mul_le_mul_of_nonneg_left h_n_abs
            linarith [Real.pi_pos]
        _ = 2 * π := by ring

    -- 但 10(β-α) = 2πn 且 0 < 10(β-α) < 2π
    -- 由 h_eq : 10(β-α) = 2πn 和 h_range.1 知 2πn > 0
    -- 所以 |2πn| = 2πn = 10(β-α) < 2π，与 |2πn| ≥ 2π 矛盾
    have : 10 * (β - α) < 2 * π := h_range.2
    have : 2 * π * (n : ℝ) < 2 * π := by rw [← h_eq]; exact this
    have h_pos : 2 * π * (n : ℝ) > 0 := by rw [← h_eq]; exact h_range.1
    have : |2 * π * (n : ℝ)| = 2 * π * (n : ℝ) := abs_of_pos h_pos
    linarith

-------------------------- Step 1 ----------------------------

def V₁ (α β : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, x α, (x α)^10, (x α)^11;
     1, y β, (y β)^10, (y β)^11;
     1 - t, 0, (1 - t) * (x α)^10, 0;
     1 - t, 0, (1 - t) * (y β)^10, 0]

lemma det_V_eq_det_V₁ (α β : ℝ) : det (V α β) = det (V₁ α β) := by
  rw [V_explicit]
  let M := updateRow (V₀ α β) 2 ((V₀ α β) 2 + (-t) • (V₀ α β) 0);
  calc det (V₀ α β)
      = det M := by
          have h_ne1 : (2 : Fin 4) ≠ (0 : Fin 4) := by decide
          rw [det_updateRow_add_smul_self (V₀ α β) h_ne1 (-t)]
    _ = det (V₁ α β) := by
          have h_ne2 : (3 : Fin 4) ≠ (1 : Fin 4) := by decide
          have hV₁ : V₁ α β = updateRow M 3 (M 3 + (-t) • M 1) := by
            unfold M
            ext i j
            simp [V₁, V₀, updateRow]
            fin_cases i <;> fin_cases j <;> simp <;> ring
          rw [hV₁, det_updateRow_add_smul_self _ h_ne2 (-t)]

-------------------------- Step 2 ----------------------------

def V₂ (α β : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, x α, (x α)^10, (x α)^11;
     1, y β, (y β)^10, (y β)^11;
     1, 0, (x α)^10, 0;
     1, 0, (y β)^10, 0]

lemma det_V₁_eq_det_V₂ (α β : ℝ) : det (V₁ α β) = (1 - t)^2 * det (V₂ α β) := by
  let M := updateRow (V₁ α β) 2 ((V₂ α β) 2)
  calc det (V₁ α β)
      = det (updateRow (V₁ α β) 2 ((1 - t) • (V₂ α β) 2)) := by
          congr 1
          ext i j
          simp [V₁, V₂, updateRow]
          fin_cases i <;> fin_cases j <;> simp
    _ = (1 - t) * det M := by
          rw [det_updateRow_smul]
    _ = (1 - t) * det (updateRow M 3 ((1 - t) • (V₂ α β) 3)) := by
          unfold M
          congr 2
          ext i j
          simp [V₁, V₂, updateRow]
          fin_cases i <;> fin_cases j <;> simp
    _ = (1 - t) * ((1 - t) * det (updateRow M 3 ((V₂ α β) 3))) := by
          rw [det_updateRow_smul]
    _ = (1 - t)^2 * det (V₂ α β) := by
          have hV₂_eq : V₂ α β = updateRow M 3 ((V₂ α β) 3) := by
            unfold M
            ext i j
            simp [V₁, V₂, updateRow]
            fin_cases i <;> fin_cases j <;> simp
          rw [← hV₂_eq]
          ring

-------------------------- Step 3 ----------------------------

def V₃ (α β : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, x α, 0, (x α)^11;
     0, y β, 0, (y β)^11;
     1, 0, (x α)^10, 0;
     1, 0, (y β)^10, 0]

lemma det_V₂_eq_det_V₃ (α β : ℝ) : det (V₂ α β) = det (V₃ α β) := by
  rw [V₃]
  let M := updateRow (V₂ α β) 0 ((V₂ α β) 0 + (-1) • (V₂ α β) 2)
  calc det (V₂ α β)
      = det M := by
          unfold M
          have h_ne1 : (0 : Fin 4) ≠ (2 : Fin 4) := by decide
          rw [← det_updateRow_add_smul_self (V₂ α β) h_ne1 (-1)]; simp
    _ = det (V₃ α β) := by
          have hV₃ : V₃ α β = updateRow M 1 (M 1 + (-1) • M 3) := by
            unfold M
            ext i j
            simp [V₃, V₂, updateRow]
            fin_cases i <;> fin_cases j <;> simp
          have h_ne2 : (1 : Fin 4) ≠ (3 : Fin 4) := by decide
          rw [hV₃, ← det_updateRow_add_smul_self _ h_ne2 (-1)]; simp

-------------------------- Step 4 ----------------------------

def V₄ (α β : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![x α, (x α)^11, 0, 0;
     y β, (y β)^11, 0, 0;
     0, 0, 1, (x α)^10;
     0, 0, 1, (y β)^10]

lemma det_V₃_eq_det_V₄ (α β : ℝ) : det (V₃ α β) = - det (V₄ α β) := by
  let σ : Equiv.Perm (Fin 4) := ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩
  have h_sign : Equiv.Perm.sign σ = -1 := by decide
  have h_V₄ : V₄ α β = (V₃ α β).submatrix id σ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  calc det (V₃ α β)
      = - (-1 * det (V₃ α β)) := by ring
    _ = - ((Equiv.Perm.sign σ) * det (V₃ α β)) := by rw [h_sign]; simp
    _ = - det ((V₃ α β).submatrix id σ) := by rw [det_permute']
    _ = - det (V₄ α β) := by rw [← h_V₄]

-------------------------- Step 5 ----------------------------

def A (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x α, (x α)^11;
     y β, (y β)^11]

def B (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (x α)^10;
     1, (y β)^10]

lemma det_A (α β : ℝ) : det (A α β) = x α * (y β)^11 - y β * (x α)^11 := by
  simp [A, det_fin_two]; ring

lemma det_B (α β : ℝ) : det (B α β) = (y β)^10 - (x α)^10 := by
  simp [B, det_fin_two]

lemma det_V₄_eq_det_A_mul_det_B (α β : ℝ) :
  det (V₄ α β) = det (A α β) * det (B α β) := by
  let e := (finSumFinEquiv (m := 2) (n := 2)).symm
  have h_eq : V₄ α β = submatrix (fromBlocks (A α β) 0 0 (B α β)) e e := by
    ext i j
    simp [submatrix, fromBlocks, e, finSumFinEquiv]
    fin_cases i <;> fin_cases j <;> rfl
  rw [h_eq, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

----------------------- Final Steps  -------------------------

lemma detV_formula (α β : ℝ) :
  det (V α β) = -(1 - t)^2 * exp (I * (α + β)) *
                 (exp (I * (10 * β)) - exp (I * (10 * α)))^2 := by
  rw [det_V_eq_det_V₁, det_V₁_eq_det_V₂, det_V₂_eq_det_V₃, det_V₃_eq_det_V₄,
      det_V₄_eq_det_A_mul_det_B, det_A, det_B]
  have h1 : (x α * y β ^ 11 - y β * x α ^ 11) * (y β ^ 10 - x α ^ 10) =
            (x α * y β) * (y β ^ 10 - x α ^ 10) ^ 2 := by ring_nf;
  have h2 : (x α * y β) = exp (I * (α + β)) := by
    unfold x y; ring_nf; simp [Complex.exp_add];
  have h3 : (y β ^ 10 - x α ^ 10) = exp (I * (10 * β)) - exp (I * (10 * α)) := by
    unfold x y; rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]; ring_nf
  rw [h1, h2, h3]
  ring

theorem detV_neq_0 (α β : ℝ)
        (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
        det (V α β) ≠ 0 := by
  rw [detV_formula]

  have h1 : (1 - t)^2 ≠ 0 := by apply pow_ne_zero 2 one_sub_t_ne_0
  have h2 : exp (I * (α + β)) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (exp (I * (10 * β)) - exp (I * (10 * α)))^2 ≠ 0 := by
    apply pow_ne_zero
    intro heq
    have : exp (I * (10 * β)) = exp (I * (10 * α)) := sub_eq_zero.mp heq
    exact exp_10_ne α β hα hαβ hβ this

  have : (1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1 h2) h3
  intro h
  apply this
  have : -(1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2 =
         -((1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2) := by ring
  rw [this] at h
  exact neg_eq_zero.mp h

end LeanVDM_example2
