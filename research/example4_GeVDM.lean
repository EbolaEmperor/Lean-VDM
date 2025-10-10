import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

namespace LeanVDM_example4

def n := 6
def e : Fin n → ℕ := ![0, 1, 2, 10, 11, 12]

def u (α β γ : ℝ) : Fin n → ℂ :=
  ![exp (I * α),
    exp (I * β),
    exp (I * γ),
    exp (I * (α + 0.2 * π)),
    exp (I * (β + 0.2 * π)),
    exp (I * (γ + 0.2 * π))]

def V (α β γ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  GeVDM n (u α β γ) e

-- 辅助定义：x = e^(iα), y = e^(iβ), z = e^(iγ), t = e^(iπ/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def z (γ : ℝ) : ℂ := exp (γ * I)
def t := exp (0.2 * π * I)

-- t 的幂次性质
lemma t_pow_10 : t^10 = 1 := sorry

lemma t_pow_11 : t^11 = t := sorry

lemma t_pow_12 : t^12 = t^2 := sorry

-- 说明 u 向量的结构：u = [x, y, z, t*x, t*y, t*z]
lemma u_structure (α β γ : ℝ) :
  u α β γ = ![x α, y β, z γ, t * x α, t * y β, t * z γ] := sorry

-- V 矩阵的初始形式
def V₀ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,     (x α)^2,      (x α)^10,  (x α)^11,     (x α)^12;
     1,  y β,     (y β)^2,      (y β)^10,  (y β)^11,     (y β)^12;
     1,  z γ,     (z γ)^2,      (z γ)^10,  (z γ)^11,     (z γ)^12;
     1,  t*x α,   t^2*(x α)^2,  (x α)^10,  t*(x α)^11,   t^2*(x α)^12;
     1,  t*y β,   t^2*(y β)^2,  (y β)^10,  t*(y β)^11,   t^2*(y β)^12;
     1,  t*z γ,   t^2*(z γ)^2,  (z γ)^10,  t*(z γ)^11,   t^2*(z γ)^12]

-- V 矩阵的显式表达
lemma V_explicit (α β γ : ℝ) : V α β γ = V₀ α β γ := sorry

-- Vandermonde/DFT 变换矩阵 F（2x2）
-- 用于处理两个频率：1 和 t
def F : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,  1;
     1,  t]

-- F 的行列式非零
lemma det_F : det F = t - 1 := sorry

lemma t_ne_1 : t ≠ 1 := sorry

lemma det_F_ne_0 : det F ≠ 0 := sorry

-------------------------- Step 1: 行重排 ----------------------------

-- 行置换：将 V₀ 的行从 [x, y, z, tx, ty, tz] 重排为 [x, tx, y, ty, z, tz]
-- 即行索引从 [0,1,2,3,4,5] 重排为 [0,3,1,4,2,5]
def σ_row : Equiv.Perm (Fin 6) :=
  ⟨![0, 3, 1, 4, 2, 5], ![0, 2, 4, 1, 3, 5], by decide, by decide⟩

-- 行重排后的矩阵：(x,tx), (y,ty), (z,tz) 配对
def V₀_perm (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,     (x α)^2,      (x α)^10,  (x α)^11,     (x α)^12;
     1,  t*x α,   t^2*(x α)^2,  (x α)^10,  t*(x α)^11,   t^2*(x α)^12;
     1,  y β,     (y β)^2,      (y β)^10,  (y β)^11,     (y β)^12;
     1,  t*y β,   t^2*(y β)^2,  (y β)^10,  t*(y β)^11,   t^2*(y β)^12;
     1,  z γ,     (z γ)^2,      (z γ)^10,  (z γ)^11,     (z γ)^12;
     1,  t*z γ,   t^2*(z γ)^2,  (z γ)^10,  t*(z γ)^11,   t^2*(z γ)^12]

-- V₀_perm 就是 V₀ 的行置换
lemma V₀_perm_eq_row_perm (α β γ : ℝ) :
  V₀_perm α β γ = (V₀ α β γ).submatrix σ_row id := sorry

-- 行置换不改变行列式的绝对值
lemma sign_σ_row : Equiv.Perm.sign σ_row = 1 := sorry

lemma det_V₀_eq_det_V₀_perm (α β γ : ℝ) :
  det (V₀ α β γ) = det (V₀_perm α β γ) := sorry

-------------------------- Step 2: 应用分块 Vandermonde 变换 ----------------------------

-- 构造分块对角矩阵 diag(F⁻¹, F⁻¹, F⁻¹)
-- 这里我们用等价关系将 Fin 2 ⊕ Fin 2 ⊕ Fin 2 转换为 Fin 6
def blockDiagF_inv : Matrix (Fin 6) (Fin 6) ℂ :=
  let e := ((Equiv.sumCongr (finSumFinEquiv (m := 2) (n := 2)) (Equiv.refl (Fin 2))).trans
            (finSumFinEquiv (m := 4) (n := 2))).symm
  submatrix (fromBlocks (fromBlocks F⁻¹ 0 0 F⁻¹) 0 0 F⁻¹) e e

-- 应用变换后，行按照同余类重新组织
-- 行对 0-1：F⁻¹ 作用于 x, tx
-- 行对 2-3：F⁻¹ 作用于 y, ty
-- 行对 4-5：F⁻¹ 作用于 z, tz
def V₁ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  blockDiagF_inv * V₀_perm α β γ

-- V₁ 的显式形式：对每对行应用 F⁻¹ = (1/(t-1)) × [[t, -1], [-1, 1]]
-- 计算方法：V₁ 可以分块为 3×3 个 2×2 块，每块 V₁[i,j] = F⁻¹ × V₀_perm[i,j]
-- 例如 V₁[0,1]（行0-1，列2-3）：
--   F⁻¹ × [[(x α)^2, (x α)^10], [t^2*(x α)^2, (x α)^10]]
--   = (1/(t-1)) × [[t*(x α)^2 - t^2*(x α)^2, t*(x α)^10 - (x α)^10],
--                  [-(x α)^2 + t^2*(x α)^2, -(x α)^10 + (x α)^10]]
--   = [[-t*(x α)^2, (x α)^10], [(t+1)*(x α)^2, 0]]
lemma V₁_explicit (α β γ : ℝ) : V₁ α β γ =
  !![1,  0,      -t*(x α)^2,         (x α)^10,  0,              -t*(x α)^12;
     0,  x α,    (t+1)*(x α)^2,      0,         (x α)^11,       (t+1)*(x α)^12;
     1,  0,      -t*(y β)^2,         (y β)^10,  0,              -t*(y β)^12;
     0,  y β,    (t+1)*(y β)^2,      0,         (y β)^11,       (t+1)*(y β)^12;
     1,  0,      -t*(z γ)^2,         (z γ)^10,  0,              -t*(z γ)^12;
     0,  z γ,    (t+1)*(z γ)^2,      0,         (z γ)^11,       (t+1)*(z γ)^12] := sorry

-- 行列式关系
lemma det_V₀_perm_eq_det_V₁ (α β γ : ℝ) :
  det (V₀_perm α β γ) = det F ^ 3 * det (V₁ α β γ) := sorry

lemma det_V_eq_det_V₁ (α β γ : ℝ) : det (V α β γ) = det F ^ 3 * det (V₁ α β γ) := sorry

-------------------------- Step 3: 列操作，消去第 2 列和第 5 列 ----------------------------

-- 观察 V₁：第 1 列和第 4 列在 V₁ 的偶数行有非零元素 (x α, y β, z γ)
-- 我们可以用第 1 列和第 4 列来消去其他列的某些元素

-- 列操作：第 2 列 += t × 第 1 列（这样可以消去偶数行）
-- 列操作：第 5 列 += t × 第 4 列
-- 实现：构造新矩阵，每列根据列索引决定是否修改
def V₂ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j =>
    match j with
    | 0 => (V₁ α β γ) i 0                    -- 第 0 列不变
    | 1 => (V₁ α β γ) i 1                    -- 第 1 列不变
    | 2 => (V₁ α β γ) i 2 + t * (V₁ α β γ) i 1  -- 第 2 列 += t × 第 1 列
    | 3 => (V₁ α β γ) i 3                    -- 第 3 列不变
    | 4 => (V₁ α β γ) i 4                    -- 第 4 列不变
    | 5 => (V₁ α β γ) i 5 + t * (V₁ α β γ) i 4  -- 第 5 列 += t × 第 4 列

-- V₂ 的显式形式：第 2 列和第 5 列的偶数行被消成 0
lemma V₂_explicit (α β γ : ℝ) : V₂ α β γ =
  !![1,  0,      0,              (x α)^10,  0,              0;
     0,  x α,    (t+1)*(x α)^2,  0,         (x α)^11,       (t+1)*(x α)^12;
     1,  0,      0,              (y β)^10,  0,              0;
     0,  y β,    (t+1)*(y β)^2,  0,         (y β)^11,       (t+1)*(y β)^12;
     1,  0,      0,              (z γ)^10,  0,              0;
     0,  z γ,    (t+1)*(z γ)^2,  0,         (z γ)^11,       (t+1)*(z γ)^12] := sorry

-- 列操作不改变行列式
lemma det_V₁_eq_det_V₂ (α β γ : ℝ) : det (V₁ α β γ) = det (V₂ α β γ) := sorry

-------------------------- Step 4: 列重排，按同余类分组 ----------------------------

-- 将列重排为：[0,3] (同余类0), [1,4] (同余类1), [2,5] (同余类2)
def σ_col : Equiv.Perm (Fin 6) :=
  ⟨![0, 3, 1, 4, 2, 5], ![0, 2, 4, 1, 3, 5], by decide, by decide⟩

def V₃ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (V₂ α β γ).submatrix id σ_col

-- V₃ 的显式形式：按同余类分成三个 6×2 块
lemma V₃_explicit (α β γ : ℝ) : V₃ α β γ =
  !![1,  (x α)^10,  0,      0,           0,              (t+1)*(x α)^2;
     0,  0,         x α,    (x α)^11,    (t+1)*(x α)^2,  0;
     1,  (y β)^10,  0,      0,           0,              (t+1)*(y β)^2;
     0,  0,         y β,    (y β)^11,    (t+1)*(y β)^2,  0;
     1,  (z γ)^10,  0,      0,           0,              (t+1)*(z γ)^2;
     0,  0,         z γ,    (z γ)^11,    (t+1)*(z γ)^2,  0] := sorry

lemma sign_σ_col : Equiv.Perm.sign σ_col = 1 := sorry

lemma det_V₂_eq_det_V₃ (α β γ : ℝ) : det (V₂ α β γ) = det (V₃ α β γ) := sorry

-------------------------- Step 5: 行重排，按奇偶分组 ----------------------------

-- 将奇数行和偶数行分开：[0,2,4,1,3,5]
def σ_row2 : Equiv.Perm (Fin 6) :=
  ⟨![0, 2, 4, 1, 3, 5], ![0, 3, 1, 4, 2, 5], by decide, by decide⟩

def V₄ (α β γ : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (V₃ α β γ).submatrix σ_row2 id

-- V₄ 的显式形式：前3行是奇数行，后3行是偶数行
lemma V₄_explicit (α β γ : ℝ) : V₄ α β γ =
  !![1,  (x α)^10,  0,      0,           0,              (t+1)*(x α)^2;
     1,  (y β)^10,  0,      0,           0,              (t+1)*(y β)^2;
     1,  (z γ)^10,  0,      0,           0,              (t+1)*(z γ)^2;
     0,  0,         x α,    (x α)^11,    (t+1)*(x α)^2,  0;
     0,  0,         y β,    (y β)^11,    (t+1)*(y β)^2,  0;
     0,  0,         z γ,    (z γ)^11,    (t+1)*(z γ)^2,  0] := sorry

lemma sign_σ_row2 : Equiv.Perm.sign σ_row2 = 1 := sorry

lemma det_V₃_eq_det_V₄ (α β γ : ℝ) : det (V₃ α β γ) = det (V₄ α β γ) := sorry

-------------------------- Step 6: 观察 V₄ 的分块结构 ----------------------------

-- V₄ 可以看作 2×3 分块矩阵：
-- [[A₀, 0,  C],
--  [0,  A₁, D]]
-- 其中 A₀, A₁ 是 3×2, C, D 是 3×2

def A₀ (α β γ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![1,        (x α)^10;
     1,        (y β)^10;
     1,        (z γ)^10]

def A₁ (α β γ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![x α,      (x α)^11;
     y β,      (y β)^11;
     z γ,      (z γ)^11]

def C (α β γ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![0,              (t+1)*(x α)^2;
     0,              (t+1)*(y β)^2;
     0,              (t+1)*(z γ)^2]

def D (α β γ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![(t+1)*(x α)^2,  0;
     (t+1)*(y β)^2,  0;
     (t+1)*(z γ)^2,  0]

-------------------------- Step 7: 利用分块行列式公式 ----------------------------

-- V₄ 的行列式可以通过 Laplace 展开或分块行列式公式计算
-- 由于 V₄ 有特殊的 2×3 块结构 [[A₀, 0, C], [0, A₁, D]]
-- 我们可以利用这个结构

-- 关键观察：C 和 D 的结构简单，可以进一步消去
-- 列操作：第 4 列不变，第 5 列 -= (t+1)*(x α)/(x α)^11 * 第 3 列（对第二块行）

-------------------------- Step 8: 最终行列式公式 ----------------------------

-- A₀ 和 A₁ 的秩和结构分析
lemma rank_A₀ (α β γ : ℝ) (hαβ : α < β) (hβγ : β < γ) :
  (A₀ α β γ).rank = 2 := sorry

lemma rank_A₁ (α β γ : ℝ) (hαβ : α < β) (hβγ : β < γ) :
  (A₁ α β γ).rank = 2 := sorry

-- 综合所有步骤，得到最终的行列式公式
-- 注意：实际公式会更复杂，需要仔细计算分块行列式
lemma detV_formula (α β γ : ℝ) :
  det (V α β γ) = det F ^ 3 *
    ((y β)^10 - (x α)^10) * ((z γ)^10 - (x α)^10) * ((z γ)^10 - (y β)^10) *
    (y β - x α) * (z γ - x α) * (z γ - y β) := sorry

-- 辅助引理：在给定条件下，各项非零
lemma exp_10_pairwise_ne (α β γ : ℝ)
  (hα : 0 ≤ α) (hαβ : α < β) (hβγ : β < γ) (hγ : γ < 0.2 * π) :
  exp (↑(10 * β) * I) ≠ exp (↑(10 * α) * I) ∧
  exp (↑(10 * γ) * I) ≠ exp (↑(10 * α) * I) ∧
  exp (↑(10 * γ) * I) ≠ exp (↑(10 * β) * I) := sorry

lemma exp_pairwise_ne (α β γ : ℝ)
  (hα : 0 ≤ α) (hαβ : α < β) (hβγ : β < γ) (hγ : γ < 0.2 * π) :
  exp (β * I) ≠ exp (α * I) ∧
  exp (γ * I) ≠ exp (α * I) ∧
  exp (γ * I) ≠ exp (β * I) := sorry

-------------------------- 非零性定理 ----------------------------

theorem detV_neq_0 (α β γ : ℝ)
        (hα : 0 ≤ α) (hαβ : α < β) (hβγ : β < γ) (hγ : γ < 0.2 * π) :
        det (V α β γ) ≠ 0 := sorry

end LeanVDM_example4
