import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

namespace LeanVDM_example3_6x6

def n := 6
def e : Fin n → ℕ := ![0, 1, 2, 10, 11, 12]

def u (α β : ℝ) : Fin n → ℂ :=
  ![exp (I * α),
    exp (I * β),
    exp (I * (α + 0.2 * π)),
    exp (I * (β + 0.2 * π)),
    exp (I * (α + 0.4 * π)),
    exp (I * (β + 0.4 * π))]

def V (α β : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  GeVDM n (u α β) e

-- 辅助定义：x = e^(iα), y = e^(iβ), t1 = e^(iπ/5), t2 = e^(i2π/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def t1 := exp (0.2 * π * I)
def t2 := exp (0.4 * π * I)

lemma t1_pow_10 : t1^10 = 1 := by
  rw [t1, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring

lemma t1_pow_11 : t1^11 = t1 := by
  calc t1^11 = t1^10 * t1 := by ring
          _ = t1 := by rw [t1_pow_10]; simp

lemma t1_pow_12 : t1^12 = t1^2 := by
  calc t1^12 = t1^10 * t1^2 := by ring
          _ = t1^2 := by rw [t1_pow_10]; simp

lemma t2_pow_10 : t2^10 = 1 := by
  rw [t2, ← Complex.exp_nat_mul]
  ring_nf;
  apply Complex.exp_eq_one_iff.mpr;
  use 2; ring

lemma t2_pow_11 : t2^11 = t2 := by
  calc t2^11 = t2^10 * t2 := by ring
          _ = t2 := by rw [t2_pow_10]; simp

lemma t2_pow_12 : t2^12 = t2^2 := by
  calc t2^12 = t2^10 * t2^2 := by ring
          _ = t2^2 := by rw [t2_pow_10]; simp

-- 说明 u 向量的结构：u = [x, y, t1*x, t1*y, t2*x, t2*y]
lemma u_structure (α β : ℝ) :
  u α β = ![x α, y β, t1 * x α, t1 * y β, t2 * x α, t2 * y β] := by
  ext i
  fin_cases i
  · simp [u, x]; ring_nf
  · simp [u, y]; ring_nf
  · simp [u, x, t1]; rw [← Complex.exp_add]; ring_nf
  · simp [u, y, t1]; rw [← Complex.exp_add]; ring_nf
  · simp [u, x, t2]; rw [← Complex.exp_add]; ring_nf
  · simp [u, y, t2]; rw [← Complex.exp_add]; ring_nf

def V₀ (α β : ℝ) := !![1, x α, (x α)^2, (x α)^10, (x α)^11, (x α)^12;
                       1, y β, (y β)^2, (y β)^10, (y β)^11, (y β)^12;
                       1, t1 * x α, (t1 * x α)^2, (x α)^10, t1 * (x α)^11, t1^2 * (x α)^12;
                       1, t1 * y β, (t1 * y β)^2, (y β)^10, t1 * (y β)^11, t1^2 * (y β)^12;
                       1, t2 * x α, (t2 * x α)^2, (x α)^10, t2 * (x α)^11, t2^2 * (x α)^12;
                       1, t2 * y β, (t2 * y β)^2, (y β)^10, t2 * (y β)^11, t2^2 * (y β)^12]

def V₁ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, x α, (x α)^2, (x α)^10, (x α)^11, (x α)^12;
     1, y β, (y β)^2, (y β)^10, (y β)^11, (y β)^12;
     1 - t1, 0, -(1 - t1) * t1 * (x α)^2, (1 - t1) * (x α)^10, 0, -(1 - t1) * t1 * (x α)^12;
     1 - t1, 0, -(1 - t1) * t1 * (y β)^2, (1 - t1) * (y β)^10, 0, -(1 - t1) * t1 * (y β)^12;
     1 - t2, 0, -(1 - t2) * t2 * (x α)^2, (1 - t2) * (x α)^10, 0, -(1 - t2) * t2 * (x α)^12;
     1 - t2, 0, -(1 - t2) * t2 * (y β)^2, (1 - t2) * (y β)^10, 0, -(1 - t2) * t2 * (y β)^12]

lemma det_V_eq_det_V₁ (α β : ℝ) : det (V α β) = det (V₁ α β) := by
  sorry

def V₂ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, x α, (x α)^2, (x α)^10, (x α)^11, (x α)^12;
     1, y β, (y β)^2, (y β)^10, (y β)^11, (y β)^12;
     1, 0, -t1 * (x α)^2, (x α)^10, 0, -t1 * (x α)^12;
     1, 0, -t1 * (y β)^2, (y β)^10, 0, -t1 * (y β)^12;
     1, 0, -t2 * (x α)^2, (x α)^10, 0, -t2 * (x α)^12;
     1, 0, -t2 * (y β)^2, (y β)^10, 0, -t2 * (y β)^12]

lemma det_V₁_eq_det_V₂ (α β : ℝ) :
  det (V₁ α β) = (1 - t1)^2 * (1 - t2)^2 * det (V₂ α β) := by
  sorry

def V₃ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, x α, (1 + t1) * (x α)^2, 0, (x α)^11, (1 + t1) * (x α)^12;
     0, y β, (1 + t1) * (y β)^2, 0, (y β)^11, (1 + t1) * (y β)^12;
     1, 0, -t1 * (x α)^2, (x α)^10, 0, -t1 * (x α)^12;
     1, 0, -t1 * (y β)^2, (y β)^10, 0, -t1 * (y β)^12;
     1, 0, -t2 * (x α)^2, (x α)^10, 0, -t2 * (x α)^12;
     1, 0, -t2 * (y β)^2, (y β)^10, 0, -t2 * (y β)^12]

lemma det_V₂_eq_det_V₃ (α β : ℝ) : det (V₂ α β) = det (V₃ α β) := by
  sorry

def V₄ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0,        x α, (x α)^11, (1 + t1) * (x α)^12, (1 + t1) * (x α)^2;
     0, 0,        y β, (y β)^11, (1 + t1) * (y β)^12, (1 + t1) * (y β)^2;
     1, (x α)^10, 0,   0,             -t1 * (x α)^12,      -t1 * (x α)^2;
     1, (y β)^10, 0,   0,             -t1 * (y β)^12,      -t1 * (y β)^2;
     1, (x α)^10, 0,   0,             -t2 * (x α)^12,      -t2 * (x α)^2;
     1, (y β)^10, 0,   0,             -t2 * (y β)^12,      -t2 * (y β)^2]

lemma det_V₃_eq_det_V₄ (α β : ℝ) : det (V₃ α β) = det (V₄ α β) := by
  sorry

-- V 矩阵的显式表达
lemma V_explicit (α β : ℝ) :
  V α β = V₀ α β := by
  ext i j
  rw [V, GeVDM, V₀]
  simp only [u_structure]
  fin_cases i <;> fin_cases j <;> simp [e]
  · rw [mul_pow, t1_pow_10]; ring
  · rw [mul_pow, t1_pow_11]
  · rw [mul_pow, t1_pow_12]
  · rw [mul_pow, t1_pow_10]; ring
  · rw [mul_pow, t1_pow_11]
  · rw [mul_pow, t1_pow_12]
  · rw [mul_pow, t2_pow_10]; ring
  · rw [mul_pow, t2_pow_11]
  · rw [mul_pow, t2_pow_12]
  · rw [mul_pow, t2_pow_10]; ring
  · rw [mul_pow, t2_pow_11]
  · rw [mul_pow, t2_pow_12]

def A (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x α, (x α)^11;
     y β, (y β)^11]

def B (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (x α)^2;
     1, (y β)^2]

def C (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (x α)^10;
     1, (y β)^10]

lemma det_A (α β : ℝ) : det (A α β) = x α * (y β)^11 - y β * (x α)^11 := by
  simp [A, det_fin_two]; ring

lemma det_B (α β : ℝ) : det (B α β) = (y β)^2 - (x α)^2 := by
  simp [B, det_fin_two]

lemma det_C (α β : ℝ) : det (C α β) = (y β)^10 - (x α)^10 := by
  simp [C, det_fin_two]

end LeanVDM_example3_6x6
