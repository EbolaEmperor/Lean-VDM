import LeanVDM.ClassicalVDM

open Finset Matrix BigOperators

def GeVDM (n : ℕ) (u : Fin n → ℝ) (e : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i ^ (e j)

theorem GeVDM_eq_ClassicalVDM (n : ℕ) (u : Fin n → ℝ) (e : Fin n → ℕ) (he : ∀ i, e i = i) :
  GeVDM n u e = ClassicalVDM n u := by
  ext i j
  simp [GeVDM, ClassicalVDM]
  congr
  apply he
