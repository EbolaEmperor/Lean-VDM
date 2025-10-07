import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators

open BigOperators Finset

def fibonacci : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | (n+2) => fibonacci (n+1) + fibonacci n

noncomputable def φ : ℝ := (1 + √5) / 2
noncomputable def ψ : ℝ := (1 - √5) / 2

lemma φ_relation : φ + 1 = φ ^ 2 := by
  simp only [φ]; ring_nf; simp; ring_nf

lemma ψ_relation : ψ + 1 = ψ ^ 2 := by
  simp only [ψ]; ring_nf; simp; ring_nf

theorem fibonacci_formula (n : ℕ) :
  fibonacci n = (φ^n - ψ^n) / √5 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      simp only [fibonacci, φ, ψ]
      simp
    | 1 =>
      simp only [fibonacci, φ, ψ]
      ring_nf; simp
    | n + 2 =>
      calc ↑(fibonacci (n + 2))
        = ↑(fibonacci (n + 1)) + ↑(fibonacci n) := by rw [fibonacci]; simp;
      _ = ((φ^(n+1) - ψ^(n+1)) / √5) + ((φ^n - ψ^n) / √5) := by
        rw [ih n (by omega), ih (n + 1) (by omega)];
      _ = ((φ + 1) * φ^n - (ψ + 1) * ψ^n) / √5 := by ring;
      _ = (φ^(n+2) - ψ^(n+2)) / √5 := by
        simp only [φ_relation, ψ_relation]; ring

lemma fibonacci_gt_0 (n : ℕ) (hn : n ≥ 1) :
  fibonacci n > 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [fibonacci]
    | succ n' =>
      rw [fibonacci]
      have : fibonacci (n' + 1) > 0 := ih (by omega)
      linarith

theorem fibonacci_incr (n : ℕ) :
  fibonacci n ≤ fibonacci (n + 1) := by
  match n with
  | 0 => simp [fibonacci]
  | 1 => simp [fibonacci]
  | n + 2 =>  exact Nat.le.intro rfl

theorem fibonacci_sum_eq_succ_sub_1 (n : ℕ) :
  ∑ i ∈ range n, fibonacci i = (fibonacci (n + 1)) - 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      calc ∑ i ∈ range (n + 1), fibonacci i
         = (fibonacci n) + ∑ i ∈ range n, fibonacci i := by
            exact sum_range_succ_comm fibonacci n
       _ = (fibonacci n) + ((fibonacci (n + 1)) - 1) := by simp [ih];
       _ = (fibonacci (n + 2)) - 1 := by
           rw [fibonacci]; ring_nf;
           refine Eq.symm (Nat.add_sub_assoc ?_ (fibonacci n))
           apply fibonacci_gt_0; omega

theorem fibonacci_even_iff_n_mod_3_eq_0 (n : ℕ) :
  Even (fibonacci n) ↔ n % 3 = 0 := by

  have h_period_succ (k : ℕ) : (fibonacci (k + 3)) % 2 = (fibonacci k) % 2 := by
    calc fibonacci (k + 3) % 2
      = (fibonacci (k + 2) + fibonacci (k + 1)) % 2 := by rw [fibonacci]
    _ = (fibonacci k + 2 * fibonacci (k + 1)) % 2 := by rw [fibonacci]; ring_nf
    _ = fibonacci k % 2 := by exact
      Nat.add_mul_mod_self_left (fibonacci k) 2 (fibonacci (k + 1))

  have h_period (k : ℕ) : (fibonacci k) % 2 = (fibonacci (k % 3)) % 2 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | k + 3 =>
        calc fibonacci (k + 3) % 2
           = fibonacci k % 2 := by simp [h_period_succ]
         _ = fibonacci (k % 3) % 2 := by simp [ih]
         _ = fibonacci ((k + 3) % 3) % 2 := by
             congr 2; exact Eq.symm (Nat.add_mod_right k 3)

  constructor
  · intro h_even
    by_contra h_not_mod3
    have h_mod_cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
    cases h_mod_cases with
    | inl h1 =>
      have : fibonacci n % 2 = 1 := by rw [h_period, h1]; rfl
      rw [Nat.even_iff.mp h_even] at this
      norm_num at this
    | inr h2 =>
      have : fibonacci n % 2 = 1 := by rw [h_period, h2]; rfl
      rw [Nat.even_iff.mp h_even] at this
      norm_num at this

  · intro h_mod3
    have : fibonacci n % 2 = 0 := by simp [h_period, h_mod3]; rfl
    exact Nat.even_iff.mpr this

theorem fibonacci_coprime (n : ℕ) :
  Nat.gcd (fibonacci n) (fibonacci (n + 1)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc Nat.gcd (fibonacci (n + 1)) (fibonacci (n + 2))
       = Nat.gcd (fibonacci (n + 1)) (fibonacci (n + 2) - fibonacci (n + 1)) := by
          refine Eq.symm (Nat.gcd_sub_self_right ?_)
          apply fibonacci_incr
     _ = Nat.gcd (fibonacci (n + 1)) (fibonacci n) := by
          congr; exact Eq.symm (Nat.eq_sub_of_add_eq' rfl)
     _ = 1 := by exact Nat.coprime_comm.mp ih

theorem fibonacci_naddm (n m : ℕ) (hm : m ≥ 1) :
  fibonacci (n + m) = (fibonacci (m - 1)) * (fibonacci n)
                    + (fibonacci m) * (fibonacci (n + 1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => omega
    | 1 => ring_nf; simp [fibonacci]
    | 2 => ring_nf; simp [fibonacci];
           calc fibonacci (2 + n)
              = fibonacci (n + 2) := by ring_nf;
            _ = fibonacci (n + 1) + fibonacci n := by rfl
           ring_nf;
    | m + 3 =>
      ring_nf
      calc fibonacci (3 + n + m)
         = fibonacci (n + m + 3) := by ring_nf
       _ = fibonacci (n + m + 2) + fibonacci (n + m + 1) := by rfl
       _ = (fibonacci (m + 1)) * (fibonacci n)
         + (fibonacci (m + 2)) * (fibonacci (n + 1))
         + (fibonacci m) * (fibonacci n)
         + (fibonacci (m + 1)) * (fibonacci (n + 1)) := by
         have h1 : n + m + 2 = n + (m + 2) := by ring
         have h2 : n + m + 1 = n + (m + 1) := by ring
         rw [h1, h2]
         have ih1 := ih (m + 2) (by omega) (by omega)
         have ih2 := ih (m + 1) (by omega) (by omega)
         have h_sub1 : m + 2 - 1 = m + 1 := by omega
         have h_sub2 : m + 1 - 1 = m := by omega
         simp only [h_sub1, h_sub2] at ih1 ih2
         rw [ih1, ih2]
         ring
       _ = (fibonacci (m + 1) + fibonacci m) * (fibonacci n)
         + (fibonacci (m + 2) + fibonacci (m + 1)) * (fibonacci (n + 1)) := by ring
       _ = (fibonacci (m + 2)) * (fibonacci n)
         + (fibonacci (m + 3)) * (fibonacci (n + 1)) := by rfl
       _ = fibonacci (3 + m - 1) * fibonacci n
         + fibonacci (3 + m) * fibonacci (1 + n) := by
         have ih1 : m + 2 = 3 + m - 1 := by omega
         simp only [ih1]; congr 1; ring_nf;

theorem fibonacci_gcd (n m : ℕ) :
  Nat.gcd (fibonacci n) (fibonacci m) = fibonacci (Nat.gcd n m) := by
  sorry
