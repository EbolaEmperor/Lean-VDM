import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

namespace LeanVDM_example4

/-! ## 基础定义 -/

def n := 6
def e : Fin n → ℕ := ![0, 1, 2, 10, 11, 12]

def u (α β γ : ℝ) : Fin n → ℝ :=
  ![α, β, γ, α + 0.2 * π, β + 0.2 * π, γ + 0.2 * π]

def V (α β γ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  FourierVDM n (u α β γ) e

-- 辅助定义：x = e^(iα), y = e^(iβ), z = e^(iγ), t = e^(iπ/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def z (γ : ℝ) : ℂ := exp (γ * I)
def t : ℂ := exp (0.2 * π * I)

-- t 的幂次性质
lemma t_pow_10 : t^10 = 1 := sorry

lemma t_pow_11 : t^11 = t := sorry

lemma t_pow_12 : t^12 = t^2 := sorry

lemma one_minus_t_ne_zero : (1 : ℂ) - t ≠ 0 := sorry

lemma one_plus_t_ne_zero : (1 : ℂ) + t ≠ 0 := sorry

lemma neg_t_ne_zero : -t ≠ 0 := sorry

-- V 矩阵的初始形式（按行：x, y, z, tx, ty, tz；按列：0, 1, 2, 10, 11, 12）
def V₀ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,     (x α)^2,      (x α)^10,  (x α)^11,     (x α)^12;
     1,  y β,     (y β)^2,      (y β)^10,  (y β)^11,     (y β)^12;
     1,  z γ,     (z γ)^2,      (z γ)^10,  (z γ)^11,     (z γ)^12;
     1,  t*x α,   t^2*(x α)^2,  (x α)^10,  t*(x α)^11,   t^2*(x α)^12;
     1,  t*y β,   t^2*(y β)^2,  (y β)^10,  t*(y β)^11,   t^2*(y β)^12;
     1,  t*z γ,   t^2*(z γ)^2,  (z γ)^10,  t*(z γ)^11,   t^2*(z γ)^12]

lemma V_eq_V₀ (α β γ : ℝ) : V α β γ = V₀ α β γ := sorry


/-! ## 第一步：行变换制造结构化零元 -/

section RowTransformation

/-- 对每对行 (ζ, tζ) 做行变换：R_{tζ} ← (R_{tζ} - t·R_ζ) / (1-t) -/
def row_transform_step1 (M : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j =>
    match i with
    | 0 => M 0 j  -- x 行不变
    | 1 => M 1 j  -- y 行不变
    | 2 => M 2 j  -- z 行不变
    | 3 => (M 3 j - t * M 0 j) / (1 - t)  -- tx 行变换
    | 4 => (M 4 j - t * M 1 j) / (1 - t)  -- ty 行变换
    | 5 => (M 5 j - t * M 2 j) / (1 - t)  -- tz 行变换

/-- V_intermediate：第一步行变换后的中间矩阵（按列：0, 1, 2, 10, 11, 12）
    顶三行（ζ=x,y,z）：[1, ζ, ζ², ζ¹⁰, ζ¹¹, ζ¹²]
    底三行（tζ变换后）：[1, 0, -tζ², ζ¹⁰, 0, -tζ¹²] -/
def V_intermediate_explicit (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,     (x α)^2,      (x α)^10,  (x α)^11,     (x α)^12;
     1,  y β,     (y β)^2,      (y β)^10,  (y β)^11,     (y β)^12;
     1,  z γ,     (z γ)^2,      (z γ)^10,  (z γ)^11,     (z γ)^12;
     1,  0,       -t*(x α)^2,   (x α)^10,  0,            -t*(x α)^12;
     1,  0,       -t*(y β)^2,   (y β)^10,  0,            -t*(y β)^12;
     1,  0,       -t*(z γ)^2,   (z γ)^10,  0,            -t*(z γ)^12]

/-- 通过第一步行变换定义的中间矩阵 -/
def V_intermediate (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  row_transform_step1 (V₀ α β γ)

/-- V_intermediate 的变换定义等价于显式定义 -/
lemma V_intermediate_eq_explicit (α β γ : ℝ) :
    V_intermediate α β γ = V_intermediate_explicit α β γ := sorry

/-- 再对每对行做：R_ζ ← R_ζ - R_{tζ} -/
def row_transform_step2 (M : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j =>
    match i with
    | 0 => M 0 j - M 3 j  -- x 行减去 tx 行
    | 1 => M 1 j - M 4 j  -- y 行减去 ty 行
    | 2 => M 2 j - M 5 j  -- z 行减去 tz 行
    | 3 => M 3 j  -- tx 行不变
    | 4 => M 4 j  -- ty 行不变
    | 5 => M 5 j  -- tz 行不变

/-- V_sharp 的显式形式（按列：0, 1, 2, 10, 11, 12）
    顶三行（ζ=x,y,z）：[0, ζ, (1+t)ζ², 0, ζ¹¹, (1+t)ζ¹²]
    底三行（tζ变换后）：[1, 0, -tζ², ζ¹⁰, 0, -tζ¹²] -/
def V_sharp_explicit (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,      x α,     (1+t)*(x α)^2,   0,         (x α)^11,  (1+t)*(x α)^12;
     0,      y β,     (1+t)*(y β)^2,   0,         (y β)^11,  (1+t)*(y β)^12;
     0,      z γ,     (1+t)*(z γ)^2,   0,         (z γ)^11,  (1+t)*(z γ)^12;
     1,      0,       -t*(x α)^2,      (x α)^10,  0,         -t*(x α)^12;
     1,      0,       -t*(y β)^2,      (y β)^10,  0,         -t*(y β)^12;
     1,      0,       -t*(z γ)^2,      (z γ)^10,  0,         -t*(z γ)^12]

/-- 通过行变换定义的 V_sharp -/
def V_sharp (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  row_transform_step2 (row_transform_step1 (V₀ α β γ))

/-- V_sharp 通过 V_intermediate 和第二步变换得到 -/
lemma V_sharp_eq_step2_of_intermediate (α β γ : ℝ) :
    V_sharp α β γ = row_transform_step2 (V_intermediate α β γ) := by
  simp [V_sharp, V_intermediate]

/-- 完整的变换链条：V₀ → V_intermediate → V_sharp -/
lemma row_transform_chain (α β γ : ℝ) :
    V_intermediate α β γ = row_transform_step1 (V₀ α β γ) ∧
    V_sharp α β γ = row_transform_step2 (V_intermediate α β γ) ∧
    V_sharp α β γ = row_transform_step2 (row_transform_step1 (V₀ α β γ)) := by
  constructor
  · rfl
  constructor
  · exact V_sharp_eq_step2_of_intermediate α β γ
  · rfl

/-- V_sharp 的变换定义等价于显式定义 -/
lemma V_sharp_eq_explicit (α β γ : ℝ) : V_sharp α β γ = V_sharp_explicit α β γ := sorry

/-- 按列重排：(1,11)|(0,10)|(2,12)，使得块结构更清晰 -/
def col_permutation : Fin 6 → Fin 6
  | 0 => 1   -- 第0列 → 指数1
  | 1 => 4   -- 第1列 → 指数11
  | 2 => 0   -- 第2列 → 指数0
  | 3 => 3   -- 第3列 → 指数10
  | 4 => 2   -- 第4列 → 指数2
  | 5 => 5   -- 第5列 → 指数12

/-- V_sharp_reordered 的显式形式（按列重排后：1, 11, 0, 10, 2, 12）
    顶三行（ζ=x,y,z）：[ζ, ζ¹¹, 0, 0, (1+t)ζ², (1+t)ζ¹²]
    底三行（tζ变换后）：[0, 0, 1, ζ¹⁰, -tζ², -tζ¹²] -/
def V_sharp_reordered_explicit (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![x α,     (x α)^11,  0,  0,         (1+t)*(x α)^2,   (1+t)*(x α)^12;
     y β,     (y β)^11,  0,  0,         (1+t)*(y β)^2,   (1+t)*(y β)^12;
     z γ,     (z γ)^11,  0,  0,         (1+t)*(z γ)^2,   (1+t)*(z γ)^12;
     0,       0,         1,  (x α)^10,  -t*(x α)^2,      -t*(x α)^12;
     0,       0,         1,  (y β)^10,  -t*(y β)^2,      -t*(y β)^12;
     0,       0,         1,  (z γ)^10,  -t*(z γ)^2,      -t*(z γ)^12]

/-- 通过列重排定义的 V_sharp_reordered -/
def V_sharp_reordered (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => V_sharp α β γ i (col_permutation j)

/-- V_sharp_reordered 的变换定义等价于显式定义 -/
lemma V_sharp_reordered_eq_explicit (α β γ : ℝ) :
    V_sharp_reordered α β γ = V_sharp_reordered_explicit α β γ := by
  ext i j
  simp [V_sharp_reordered, V_sharp_reordered_explicit, V_sharp_eq_explicit, V_sharp_explicit]
  fin_cases i <;> fin_cases j <;> simp [col_permutation]

/-- V_sharp 经过行变换后的结构：
    顶三行 (ζ=x,y,z): [ζ, ζ¹¹, 0, 0, (1+t)ζ², (1+t)ζ¹²]
    底三行 (tζ变换后): [0, 0, 1, ζ¹⁰, -tζ², -tζ¹²] -/
lemma V_sharp_structure (α β γ : ℝ) (hα : 0 ≤ α) (hβ : α < β) (hγ : β < γ) (hπ : γ < π / 5) :
    -- 顶三行在列 (0,10) 处为0，底三行在列 (1,11) 处为0
    (∀ i : Fin 3, V_sharp α β γ ⟨i, by omega⟩ 0 = 0 ∧ V_sharp α β γ ⟨i, by omega⟩ 3 = 0) ∧
    (∀ i : Fin 3,
      V_sharp α β γ ⟨i + 3, by omega⟩ 1 = 0 ∧ V_sharp α β γ ⟨i + 3, by omega⟩ 4 = 0) := sorry

lemma det_V_equals_det_V_sharp (α β γ : ℝ) :
    det (V α β γ) = (1 - t)^3 * det (V_sharp α β γ) := sorry

end RowTransformation


/-! ## 第二步：拉普拉斯展开 -/

section LaplaceExpansion

/-- 底三行、列 {0,10,2} 的子矩阵 -/
def Δ_bot_0_10_2 (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    let row : Fin 6 := ⟨(i : ℕ) + 3, by omega⟩  -- 底三行：行 3,4,5
    match j with
    | 0 => V_sharp α β γ row 0   -- 列 0
    | 1 => V_sharp α β γ row 3   -- 列 10
    | 2 => V_sharp α β γ row 2   -- 列 2

/-- 底三行、列 {0,10,12} 的子矩阵 -/
def Δ_bot_0_10_12 (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    let row : Fin 6 := ⟨(i : ℕ) + 3, by omega⟩
    match j with
    | 0 => V_sharp α β γ row 0   -- 列 0
    | 1 => V_sharp α β γ row 3   -- 列 10
    | 2 => V_sharp α β γ row 5   -- 列 12

/-- 顶三行、列 {1,11,12} 的子矩阵 -/
def Δ_top_1_11_12 (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    let row : Fin 6 := ⟨(i : ℕ), by omega⟩
    match j with
    | 0 => V_sharp α β γ row 1   -- 列 1
    | 1 => V_sharp α β γ row 4   -- 列 11
    | 2 => V_sharp α β γ row 5   -- 列 12

/-- 顶三行、列 {1,11,2} 的子矩阵 -/
def Δ_top_1_11_2 (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    let row : Fin 6 := ⟨(i : ℕ), by omega⟩
    match j with
    | 0 => V_sharp α β γ row 1   -- 列 1
    | 1 => V_sharp α β γ row 4   -- 列 11
    | 2 => V_sharp α β γ row 2   -- 列 2

/-- 拉普拉斯展开公式：det V^♯ = (-t)(1+t) · (两项之和) -/
lemma laplace_expansion (α β γ : ℝ) :
    det (V_sharp α β γ) = (-t) * (1 + t) * (
      - det (Δ_bot_0_10_2 α β γ) * det (Δ_top_1_11_12 α β γ) +
      det (Δ_bot_0_10_12 α β γ) * det (Δ_top_1_11_2 α β γ)
    ) := sorry

end LaplaceExpansion


/-! ## 关键三角恒等式 -/

section TrigonometricIdentities

/-- e^(iφ) - e^(iψ) = 2i·e^(i(φ+ψ)/2)·sin((φ-ψ)/2) -/
lemma exp_diff_formula (φ ψ : ℝ) :
    exp (I * φ) - exp (I * ψ) =
    2 * I * exp (I * (φ + ψ) / 2) * Real.sin ((φ - ψ) / 2) := sorry

/-- 3×3 Fourier-Vandermonde 行列式的三角函数表达式 -/
theorem det_FourierVDM_3x3_formula (θ₁ θ₂ θ₃ : ℝ) (p q : ℕ)
    (h_order : θ₁ < θ₂ ∧ θ₂ < θ₃) (hp : 0 < p) (hq : 0 < q) :
    ∃ (C : ℂ), C ≠ 0 ∧
    let u : Fin 3 → ℝ := ![θ₁, θ₂, θ₃]
    let e : Fin 3 → ℕ := ![0, p, q]
    let Δ₁₂ := θ₂ - θ₁
    let Δ₁₃ := θ₃ - θ₁
    det (FourierVDM 3 u e) = C * (
      Real.sin (p * Δ₁₂ / 2) * Real.sin (q * Δ₁₃ / 2) -
      Real.sin (p * Δ₁₃ / 2) * Real.sin (q * Δ₁₂ / 2)
    ) := sorry

/-- 函数 Φ_p(x) := sin(px)/sin(x) -/
def Φ (p : ℕ) (x : ℝ) : ℝ := Real.sin (p * x) / Real.sin x

/-- 函数 Ψ_p(x) := sin(px/2)/sin(x/2) -/
def Ψ (p : ℕ) (x : ℝ) : ℝ := Real.sin (p * x / 2) / Real.sin (x / 2)

end TrigonometricIdentities


/-! ## 四个子式的判号 -/

section SubdeterminantSigns

variable (α β γ : ℝ) (hα : 0 ≤ α) (hβ : α < β) (hγ : β < γ) (hπ : γ < π / 5)

/-- Φ₅(x) = 16sin⁴x - 20sin²x + 5 -/
lemma Φ_5_formula (x : ℝ) : Φ 5 x = 16 * (Real.sin x)^4 - 20 * (Real.sin x)^2 + 5 := sorry

/-- Φ₅ 在 (0, π/5) 上严格单调递减 -/
lemma Φ_5_strict_anti : ∀ x y, 0 < x → x < y → y < π / 5 → Φ 5 y < Φ 5 x := sorry

/-- Δ_bot(0,10,2) ≠ 0 -/
lemma det_Δ_bot_0_10_2_ne_zero :
    det (Δ_bot_0_10_2 α β γ) ≠ 0 := sorry

/-- Δ_bot(0,10,12) ≠ 0 -/
lemma det_Δ_bot_0_10_12_ne_zero :
    det (Δ_bot_0_10_12 α β γ) ≠ 0 := sorry

/-- Ψ₁₁ 在 (0, π/10) 上严格单调递减 -/
lemma Ψ_11_strict_anti : ∀ x y, 0 < x → x < y → y < π/10 → Ψ 11 y < Ψ 11 x := sorry

/-- Δ_top(1,11,2) ≠ 0 -/
lemma det_Δ_top_1_11_2_ne_zero :
    det (Δ_top_1_11_2 α β γ) ≠ 0 := sorry

/-- Δ_top(1,11,12) ≠ 0 -/
lemma det_Δ_top_1_11_12_ne_zero :
    det (Δ_top_1_11_12 α β γ) ≠ 0 := sorry

lemma laplace_terms_same_sign :
    - det (Δ_bot_0_10_2 α β γ) * det (Δ_top_1_11_12 α β γ) +
    det (Δ_bot_0_10_12 α β γ) * det (Δ_top_1_11_2 α β γ) ≠ 0 := sorry

/-- 在几何约束 0 ≤ α < β < γ < π / 5 下，V 矩阵行列式非零 -/
theorem V_invertible : det (V α β γ) ≠ 0 := by
  -- 使用行变换公式：det V = (1-t)³ · det V^♯
  rw [det_V_equals_det_V_sharp]
  apply mul_ne_zero
  -- 证明 (1-t)³ ≠ 0
  · apply pow_ne_zero
    exact one_minus_t_ne_zero
  -- 证明 det V^♯ ≠ 0
  · -- 使用拉普拉斯展开：det V^♯ = (-t)(1+t) · (两项之和)
    rw [laplace_expansion]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_t_ne_zero
      · exact one_plus_t_ne_zero
    · -- 两项之和不为零
      exact laplace_terms_same_sign α β γ

end SubdeterminantSigns

end LeanVDM_example4
