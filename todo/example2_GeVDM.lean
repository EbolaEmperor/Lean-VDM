import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

def n := 4
def e : Fin n → ℕ := ![0, 1, 10, 11]

def u (α β : ℝ) : Fin n → ℂ :=
  ![Complex.exp (Complex.I * α),
    Complex.exp (Complex.I * β),
    Complex.exp (Complex.I * (α + 0.2 * π)),
    Complex.exp (Complex.I * (β + 0.2 * π))]

def V (α β : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  GeVDM n (u α β) e

-- 辅助定义：x = e^(iα), y = e^(iβ), t = e^(iπ/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def t := exp (0.2 * π * I)

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
  have h1 : (1 - t)^2 ≠ 0 := by apply pow_ne_zero 2 one_sub_t_ne_0
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
