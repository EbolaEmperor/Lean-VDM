import LeanVDM.GeVDM
open Finset Matrix BigOperators GeVDMs ClassicalVDMs Real Complex

noncomputable section

namespace LeanVDM_example3

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

-- 辅助定义：x = e^(iα), y = e^(iβ), t = e^(iπ/5)
def x (α : ℝ) : ℂ := exp (α * I)
def y (β : ℝ) : ℂ := exp (β * I)
def t := exp (0.2 * π * I)

-- t 的幂次性质
lemma t_pow_10 : t^10 = 1 := sorry

lemma t_pow_11 : t^11 = t := sorry

lemma t_pow_12 : t^12 = t^2 := sorry

lemma t_pow_20 : t^20 = 1 := sorry

lemma t_pow_21 : t^21 = t := sorry

lemma t_pow_22 : t^22 = t^2 := sorry

-- 说明 u 向量的结构：u = [x, y, t*x, t*y, t²*x, t²*y]
lemma u_structure (α β : ℝ) :
  u α β = ![x α, y β, t * x α, t * y β, t^2 * x α, t^2 * y β] := sorry

-- V 矩阵的初始形式
def V₀ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,        (x α)^2,         (x α)^10,  (x α)^11,        (x α)^12;
     1,  y β,        (y β)^2,         (y β)^10,  (y β)^11,        (y β)^12;
     1,  t * x α,    t^2 * (x α)^2,   (x α)^10,  t * (x α)^11,    t^2 * (x α)^12;
     1,  t * y β,    t^2 * (y β)^2,   (y β)^10,  t * (y β)^11,    t^2 * (y β)^12;
     1,  t^2 * x α,  t^4 * (x α)^2,   (x α)^10,  t^2 * (x α)^11,  t^4 * (x α)^12;
     1,  t^2 * y β,  t^4 * (y β)^2,   (y β)^10,  t^2 * (y β)^11,  t^4 * (y β)^12]

-- V 矩阵的显式表达
lemma V_explicit (α β : ℝ) : V α β = V₀ α β := sorry

-- Vandermonde/DFT 变换矩阵 F（3x3）
def F : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,  1,    1;
     1,  t,    t^2;
     1,  t^2,  t^4]

-- F 的行列式非零
lemma det_F : det F = (t - 1)^3 * t * (t + 1) := sorry

lemma t_ne_1 : t ≠ 1 := sorry

lemma t_ne_neg_1 : t ≠ -1 := sorry

lemma t_ne_0 : t ≠ 0 := sorry

lemma det_F_ne_0 : det F ≠ 0 := sorry

-------------------------- Step 1: 行重排 ----------------------------

-- 行置换：将 V₀ 的行从 [x, y, tx, ty, t²x, t²y] 重排为 [x, tx, t²x, y, ty, t²y]
-- 即行索引从 [0,1,2,3,4,5] 重排为 [0,2,4,1,3,5]
def σ_row : Equiv.Perm (Fin 6) :=
  ⟨![0, 2, 4, 1, 3, 5], ![0, 3, 1, 4, 2, 5], by decide, by decide⟩

-- 行重排后的矩阵：x相关的行放在前3行，y相关的行放在后3行
def V₀_perm (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,  x α,        (x α)^2,         (x α)^10,  (x α)^11,        (x α)^12;
     1,  t * x α,    t^2 * (x α)^2,   (x α)^10,  t * (x α)^11,    t^2 * (x α)^12;
     1,  t^2 * x α,  t^4 * (x α)^2,   (x α)^10,  t^2 * (x α)^11,  t^4 * (x α)^12;
     1,  y β,        (y β)^2,         (y β)^10,  (y β)^11,        (y β)^12;
     1,  t * y β,    t^2 * (y β)^2,   (y β)^10,  t * (y β)^11,    t^2 * (y β)^12;
     1,  t^2 * y β,  t^4 * (y β)^2,   (y β)^10,  t^2 * (y β)^11,  t^4 * (y β)^12]

-- V₀_perm 就是 V₀ 的行置换
lemma V₀_perm_eq_row_perm (α β : ℝ) :
  V₀_perm α β = (V₀ α β).submatrix σ_row id := sorry

-- 行置换不改变行列式的绝对值
lemma sign_σ_row : Equiv.Perm.sign σ_row = 1 := sorry

lemma det_V₀_eq_det_V₀_perm (α β : ℝ) : det (V₀ α β) = det (V₀_perm α β) := sorry

-------------------------- Step 2: 应用分块 Vandermonde 变换 ----------------------------

-- 构造分块对角矩阵 diag(F⁻¹, F⁻¹)
-- 这里我们用等价关系将 Fin 3 ⊕ Fin 3 转换为 Fin 6
def blockDiagF_inv : Matrix (Fin 6) (Fin 6) ℂ :=
  let e := (finSumFinEquiv (m := 3) (n := 3)).symm
  submatrix (fromBlocks F⁻¹ 0 0 F⁻¹) e e

-- 应用变换后，行按照同余类重新组织
-- 前3行：F⁻¹ 作用于 x, tx, t²x
-- 后3行：F⁻¹ 作用于 y, ty, t²y
def V₁ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  blockDiagF_inv * V₀_perm α β

-- V₁ 的显式形式：DFT 变换后，每行只在对应的同余类列对上非零
-- 行 0: 提取 x 的频率 0 成分（同余类 0: 列 0,3）
-- 行 1: 提取 x 的频率 1 成分（同余类 1: 列 1,4）
-- 行 2: 提取 x 的频率 2 成分（同余类 2: 列 2,5）
-- 行 3-5: 对 y 做同样的提取
lemma V₁_explicit (α β : ℝ) : V₁ α β =
  !![1,  0,      0,         (x α)^10,  0,          0;
     0,  x α,    0,         0,         (x α)^11,   0;
     0,  0,      (x α)^2,   0,         0,          (x α)^12;
     1,  0,      0,         (y β)^10,  0,          0;
     0,  y β,    0,         0,         (y β)^11,   0;
     0,  0,      (y β)^2,   0,         0,          (y β)^12] := sorry

-- 行列式关系
lemma det_V₀_perm_eq_det_V₁ (α β : ℝ) :
  det (V₀_perm α β) = det F ^ 2 * det (V₁ α β) := sorry

lemma det_V_eq_det_V₁ (α β : ℝ) : det (V α β) = det F ^ 2 * det (V₁ α β) := sorry

-------------------------- Step 3: 列重排，分离同余类 ----------------------------

-- 将列按同余类 (0,10), (1,11), (2,12) 重新排列
-- 定义列置换 σ: [0,1,2,3,4,5] -> [0,3,1,4,2,5]
def σ_col : Equiv.Perm (Fin 6) :=
  ⟨![0, 3, 1, 4, 2, 5], ![0, 2, 4, 1, 3, 5], by decide, by decide⟩

-- 列重排后的矩阵
def V₂ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (V₁ α β).submatrix id σ_col

-- 列置换的符号
lemma sign_σ_col : Equiv.Perm.sign σ_col = 1 := sorry

-- 行列式关系
lemma det_V₁_eq_det_V₂ (α β : ℝ) : det (V₁ α β) = det (V₂ α β) := sorry

-------------------------- Step 4: 分块对角形式 ----------------------------

-- 经过 Vandermonde 变换和列重排后，矩阵应该呈现分块对角形式
-- 每个同余类对应一个 2x2 块
def B₀ (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,        (x α)^10;
     1,        (y β)^10]

def B₁ (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x α,      (x α)^11;
     y β,      (y β)^11]

def B₂ (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x α)^2,  (x α)^12;
     (y β)^2,  (y β)^12]

-- V₂ 应该等于三个块的分块对角矩阵
-- 这里我们用一个 6x6 矩阵来表示分块对角结构
def V₃ (α β : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  let e := ((Equiv.sumCongr (finSumFinEquiv (m := 2) (n := 2)) (Equiv.refl (Fin 2))).trans
            (finSumFinEquiv (m := 4) (n := 2))).symm
  submatrix (fromBlocks (fromBlocks (B₀ α β) 0 0 (B₁ α β)) 0 0 (B₂ α β)) e e

-- V₂ 在适当的行重排后等于 V₃
lemma V₂_block_diag (α β : ℝ) : V₂ α β = V₃ α β := sorry

-- 计算各 2×2 块的行列式
lemma det_B₀ (α β : ℝ) : det (B₀ α β) = (y β)^10 - (x α)^10 := sorry

lemma det_B₁ (α β : ℝ) : det (B₁ α β) = x α * y β * ((y β)^10 - (x α)^10) := sorry

lemma det_B₂ (α β : ℝ) : det (B₂ α β) = (x α)^2 * (y β)^2 * ((y β)^10 - (x α)^10) := sorry

-- 分块对角矩阵的行列式是各块行列式的乘积
lemma det_V₃_formula (α β : ℝ) :
  det (V₃ α β) = det (B₀ α β) * det (B₁ α β) * det (B₂ α β) := sorry

-------------------------- Step 5: 最终行列式公式 ----------------------------

-- 综合所有步骤，得到最终的行列式公式
lemma detV_formula (α β : ℝ) :
  det (V α β) = det F ^ 2 * (x α)^3 * (y β)^3 * ((y β)^10 - (x α)^10)^3 := sorry

-- 另一种形式：用指数函数表示
lemma detV_formula_exp (α β : ℝ) :
  det (V α β) = det F ^ 2 * exp (↑(3 * (α + β)) * I) *
                (exp (↑(10 * β) * I) - exp (↑(10 * α) * I))^3 := sorry

-- 辅助引理：在给定条件下，exp(10iβ) ≠ exp(10iα)
lemma exp_10_ne (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
  exp (↑(10 * β) * I) ≠ exp (↑(10 * α) * I) := sorry

-------------------------- Step 6: 非零性定理 ----------------------------

theorem detV_neq_0 (α β : ℝ)
        (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 0.2 * π) :
        det (V α β) ≠ 0 := sorry

end LeanVDM_example3
