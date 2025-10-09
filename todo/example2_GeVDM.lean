import LeanVDM.GeVDM
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential

open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

def n := 4
def e : Fin n → ℕ := ![0, 1, 10, 11]

noncomputable def u (α β : ℝ) : Fin n → ℂ :=
  ![Complex.exp (Complex.I * α),
    Complex.exp (Complex.I * β),
    Complex.exp (Complex.I * (α + 0.2 * π)),
    Complex.exp (Complex.I * (β + 0.2 * π))]

noncomputable def V (α β : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  GeVDM n (u α β) e

-- 辅助定义：x = e^(iα), y = e^(iβ), t = e^(iπ/5)
noncomputable def x (α : ℝ) : ℂ := exp (I * α)
noncomputable def y (β : ℝ) : ℂ := exp (I * β)
noncomputable def t : ℂ := exp (I * π / 5)

-- 关键性质：t = e^(i·0.2π)
lemma t_eq : t = exp (I * (0.2 * π)) := by
  simp [t]
  ring_nf

-- 关键引理：1 - t ≠ 0 (因为 e^(iπ/5) ≠ 1)
lemma one_sub_t_ne_zero : 1 - t ≠ 0 := by
  simp only [t]
  intro h
  -- 从 1 - e^(iπ/5) = 0 得到 e^(iπ/5) = 1
  have h_exp_eq : exp (I * (π / 5)) = 1 := by
    have h1 : 1 - exp (I * ↑π / 5) = 0 := h
    linarith
  -- 利用 exp_eq_one_iff: exp z = 1 ↔ ∃ n : ℤ, z = 2πni
  rw [Complex.exp_eq_one_iff] at h_exp_eq
  rcases h_exp_eq with ⟨n, hn⟩
  -- 所以 I * (π / 5) = n * (2π * I)
  -- 消去 I 得 π / 5 = 2πn，即 1 = 10n
  have h_pi_ne : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero

  -- 从等式推导出 1 = 10n
  have h_eq : (1 : ℂ) = 10 * ↑n := by
    have eq1 : I * (↑π / 5 : ℂ) = ↑n * (2 * ↑π * I) := hn
    have eq2 : (↑π / 5 : ℂ) = ↑n * (2 * ↑π) := by
      field_simp [h_I_ne] at eq1 ⊢
      linear_combination eq1
    field_simp [h_pi_ne] at eq2 ⊢
    linear_combination eq2

  -- 取实部得到实数等式 1 = 10n
  have h_real : (1 : ℝ) = 10 * (n : ℝ) := by
    have := congrArg Complex.re h_eq
    simp at this
    exact this

  -- 但 1 = 10n 对整数 n 不可能（因为 |10n| ≥ 10 或 n = 0 时 10n = 0 ≠ 1）
  by_cases hn : n = 0
  · rw [hn] at h_real; norm_num at h_real
  · have : |10 * (n : ℝ)| ≥ 10 := by
      have : |(n : ℝ)| ≥ 1 := by
        have := Int.one_le_abs hn
        exact mod_cast this
      calc |10 * (n : ℝ)| = 10 * |(n : ℝ)| := by rw [abs_mul]; norm_num
        _ ≥ 10 * 1 := by linarith
        _ = 10 := by norm_num
    rw [← h_real] at this
    norm_num at this

-- exp 的性质
lemma exp_ne_zero (z : ℂ) : exp z ≠ 0 := Complex.exp_ne_zero z

-- 关键引理：在给定条件下 e^(10iβ) ≠ e^(10iα)
lemma exp_10_ne (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
  exp (I * (10 * β)) ≠ exp (I * (10 * α)) := by
  intro h
  -- 由 exp 的周期性，exp(z1) = exp(z2) ↔ ∃ n : ℤ, z1 - z2 = 2πni
  have : ∃ n : ℤ, I * (10 * β) - I * (10 * α) = ↑n * (2 * π * I) := by
    rw [← Complex.exp_eq_exp_iff_exists_int]
    exact h
  rcases this with ⟨n, hn⟩
  -- 所以 10(β - α) * I = n * 2π * I
  -- 除以 I 得 10(β - α) = 2πn
  have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have : (10 * (β - α) : ℂ) = 2 * π * ↑n := by
    have : I * (10 * ↑β - 10 * ↑α) = ↑n * (2 * ↑π * I) := by
      calc I * (10 * ↑β - 10 * ↑α)
          = I * (10 * ↑β) - I * (10 * ↑α) := by ring
        _ = ↑n * (2 * ↑π * I) := hn
    calc (10 * (β - α) : ℂ)
        = 10 * ↑β - 10 * ↑α := by push_cast; ring
      _ = (I * (10 * ↑β - 10 * ↑α)) / I := by field_simp [h_I_ne]
      _ = (↑n * (2 * ↑π * I)) / I := by rw [this]
      _ = 2 * ↑π * ↑n := by field_simp [h_I_ne]; ring
  -- 但 0 < 10(β - α) < 2π，而 2πn 在这个范围内只能是 0
  -- (当 n=0 时 2πn=0，但 10(β-α) > 0)
  have h_range : 0 < 10 * (β - α) ∧ 10 * (β - α) < 2 * π := by
    constructor
    · linarith
    · calc 10 * (β - α) < 10 * (0.2 * π) := by linarith
        _ = 2 * π := by ring
  have : (10 * (β - α) : ℝ) = 2 * π * (n : ℝ) := by
    have := congrArg Complex.re this
    simp at this
    exact this
  -- 如果 n = 0，则 β = α，矛盾
  -- 如果 |n| ≥ 1，则 |2πn| ≥ 2π > 10(β-α)，矛盾
  by_cases hn_zero : n = 0
  · rw [hn_zero] at this
    simp at this
    linarith
  · have : |2 * π * (n : ℝ)| ≥ 2 * π := by
      have : |(n : ℝ)| ≥ 1 := by
        have : n ≠ 0 := hn_zero
        have := Int.one_le_abs this
        simp [abs_eq_self] at this ⊢
        exact mod_cast this
      calc |2 * π * (n : ℝ)| = 2 * π * |(n : ℝ)| := by rw [abs_mul, abs_of_pos]; linarith [Real.pi_pos]
        _ ≥ 2 * π * 1 := by linarith
        _ = 2 * π := by ring
    rw [← this] at this
    linarith

-- 关键定理：det V 的显式公式
-- det V = -(1-t)^2 * e^(i(α+β)) * (e^(10iβ) - e^(10iα))^2
lemma detV_formula (α β : ℝ) :
  det (V α β) = -(1 - t)^2 * exp (I * (α + β)) *
                 (exp (I * (10 * β)) - exp (I * (10 * α)))^2 := by
  -- 这需要通过一系列行列变换来证明
  -- 1. R₃ ← R₃ - t·R₁, R₄ ← R₄ - t·R₂
  -- 2. 提取因子 (1-t) 从第3、4行
  -- 3. R₁ ← R₁ - R₃, R₂ ← R₂ - R₄
  -- 4. 交换列得到反对角块形式
  -- 5. 应用块矩阵行列式公式
  sorry

theorem detV_neq_0 (α β : ℝ)
        (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
        det (V α β) ≠ 0 := by
  -- 使用显式公式: det V = -(1-t)^2 * e^(i(α+β)) * (e^(10iβ) - e^(10iα))^2
  rw [detV_formula]

  -- 证明所有因子非零
  have h1 : (1 - t)^2 ≠ 0 := pow_ne_zero 2 one_sub_t_ne_zero
  have h2 : exp (I * (α + β)) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (exp (I * (10 * β)) - exp (I * (10 * α)))^2 ≠ 0 := by
    apply pow_ne_zero
    intro heq
    have : exp (I * (10 * β)) = exp (I * (10 * α)) := sub_eq_zero.mp heq
    exact exp_10_ne α β hα hαβ hβ this

  -- 使用 mul_ne_zero 的变体
  have : (1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1 h2) h3
  intro h
  apply this
  have : -(1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2 =
         -((1 - t)^2 * exp (I * (α + β)) * (exp (I * (10 * β)) - exp (I * (10 * α)))^2) := by ring
  rw [this] at h
  exact neg_eq_zero.mp h
