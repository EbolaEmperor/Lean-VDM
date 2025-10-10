import LeanVDM.ClassicalVDM

open Finset Matrix BigOperators ClassicalVDMs Matrix Complex Real

namespace GeVDMs

variable {F : Type*} [Field F]

noncomputable def GeVDM (n : ℕ) (u : Fin n → F) (e : Fin n → ℕ) : Matrix (Fin n) (Fin n) F :=
  fun i j => u i ^ (e j)

theorem GeVDM_eq_ClassicalVDM (n : ℕ) (u : Fin n → F) (e : Fin n → ℕ) (he : ∀ i, e i = i) :
  GeVDM n u e = ClassicalVDM n u := by
  ext i j
  simp [GeVDM, ClassicalVDM]
  congr
  apply he

noncomputable def FourierVDM (n : ℕ) (u : Fin n → ℝ) (e : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => exp (I * (u i) * (e j))

theorem FourierVDM_eq_GeVDM (n : ℕ) (u : Fin n → ℝ) (e : Fin n → ℕ) :
  FourierVDM n u e = GeVDM n (fun i => exp (I * u i)) e := by
  ext i j
  simp [FourierVDM, GeVDM]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

end GeVDMs
