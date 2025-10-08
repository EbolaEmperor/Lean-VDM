import Mathlib
open BigOperators Finset

namespace Fibobacci

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | (n+2) => fib (n+1) + fib n

noncomputable def φ : ℝ := (1 + √5) / 2
noncomputable def ψ : ℝ := (1 - √5) / 2

lemma φ_relation : φ + 1 = φ ^ 2 := by
  simp only [φ]; ring_nf; simp; ring_nf

lemma ψ_relation : ψ + 1 = ψ ^ 2 := by
  simp only [ψ]; ring_nf; simp; ring_nf

theorem fib_formula (n : ℕ) :
  fib n = (φ^n - ψ^n) / √5 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      simp only [fib, φ, ψ]
      simp
    | 1 =>
      simp only [fib, φ, ψ]
      ring_nf; simp
    | n + 2 =>
      calc ↑(fib (n + 2))
        = ↑(fib (n + 1)) + ↑(fib n) := by rw [fib]; simp;
      _ = ((φ^(n+1) - ψ^(n+1)) / √5) + ((φ^n - ψ^n) / √5) := by
        rw [ih n (by omega), ih (n + 1) (by omega)];
      _ = ((φ + 1) * φ^n - (ψ + 1) * ψ^n) / √5 := by ring;
      _ = (φ^(n+2) - ψ^(n+2)) / √5 := by
        simp only [φ_relation, ψ_relation]; ring

lemma fib_gt_0 (n : ℕ) (hn : n ≥ 1) :
  fib n > 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [fib]
    | succ n' =>
      rw [fib]
      have : fib (n' + 1) > 0 := ih (by omega)
      linarith

theorem fib_incr (n : ℕ) :
  fib n ≤ fib (n + 1) := by
  match n with
  | 0 => simp [fib]
  | 1 => simp [fib]
  | n + 2 =>  exact Nat.le.intro rfl

theorem fib_sum_eq_succ_sub_1 (n : ℕ) :
  ∑ i ∈ range n, fib i = (fib (n + 1)) - 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      calc ∑ i ∈ range (n + 1), fib i
         = (fib n) + ∑ i ∈ range n, fib i := by
            exact sum_range_succ_comm fib n
       _ = (fib n) + ((fib (n + 1)) - 1) := by simp [ih];
       _ = (fib (n + 2)) - 1 := by
           rw [fib]; ring_nf;
           refine Eq.symm (Nat.add_sub_assoc ?_ (fib n))
           apply fib_gt_0; omega

theorem fib_even_iff_n_mod_3_eq_0 (n : ℕ) :
  Even (fib n) ↔ n % 3 = 0 := by

  have h_period_succ (k : ℕ) : (fib (k + 3)) % 2 = (fib k) % 2 := by
    calc fib (k + 3) % 2
      = (fib (k + 2) + fib (k + 1)) % 2 := by rw [fib]
    _ = (fib k + 2 * fib (k + 1)) % 2 := by rw [fib]; ring_nf
    _ = fib k % 2 := by exact
      Nat.add_mul_mod_self_left (fib k) 2 (fib (k + 1))

  have h_period (k : ℕ) : (fib k) % 2 = (fib (k % 3)) % 2 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | k + 3 =>
        calc fib (k + 3) % 2
           = fib k % 2 := by simp [h_period_succ]
         _ = fib (k % 3) % 2 := by simp [ih]
         _ = fib ((k + 3) % 3) % 2 := by
             congr 2; exact Eq.symm (Nat.add_mod_right k 3)

  constructor
  · intro h_even
    by_contra h_not_mod3
    have h_mod_cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
    cases h_mod_cases with
    | inl h1 =>
      have : fib n % 2 = 1 := by rw [h_period, h1]; rfl
      rw [Nat.even_iff.mp h_even] at this
      norm_num at this
    | inr h2 =>
      have : fib n % 2 = 1 := by rw [h_period, h2]; rfl
      rw [Nat.even_iff.mp h_even] at this
      norm_num at this

  · intro h_mod3
    have : fib n % 2 = 0 := by simp [h_period, h_mod3]; rfl
    exact Nat.even_iff.mpr this

theorem fib_coprime (n : ℕ) :
  Nat.gcd (fib n) (fib (n + 1)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc Nat.gcd (fib (n + 1)) (fib (n + 2))
       = Nat.gcd (fib (n + 1)) (fib (n + 2) - fib (n + 1)) := by
          refine Eq.symm (Nat.gcd_sub_self_right ?_)
          apply fib_incr
     _ = Nat.gcd (fib (n + 1)) (fib n) := by
          congr; exact Eq.symm (Nat.eq_sub_of_add_eq' rfl)
     _ = 1 := by exact Nat.coprime_comm.mp ih

theorem fib_naddm (n m : ℕ) (hm : m ≥ 1) :
  fib (n + m) = (fib (m - 1)) * (fib n)
              + (fib m) * (fib (n + 1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => omega
    | 1 => ring_nf; simp [fib]
    | 2 => ring_nf; simp [fib];
           calc fib (2 + n)
              = fib (n + 2) := by ring_nf;
            _ = fib (n + 1) + fib n := by rfl
           ring_nf;
    | m + 3 =>
      ring_nf
      calc fib (3 + n + m)
         = fib (n + m + 3) := by ring_nf
       _ = fib (n + m + 2) + fib (n + m + 1) := by rfl
       _ = (fib (m + 1)) * (fib n)
         + (fib (m + 2)) * (fib (n + 1))
         + (fib m) * (fib n)
         + (fib (m + 1)) * (fib (n + 1)) := by
         have h1 : n + m + 2 = n + (m + 2) := by ring
         have h2 : n + m + 1 = n + (m + 1) := by ring
         rw [h1, h2]
         have ih1 := ih (m + 2) (by omega) (by omega)
         have ih2 := ih (m + 1) (by omega) (by omega)
         have h_sub1 : m + 2 - 1 = m + 1 := by omega
         have h_sub2 : m + 1 - 1 = m := by omega
         simp only [h_sub1, h_sub2] at ih1 ih2
         rw [ih1, ih2]; ring_nf;
       _ = (fib (m + 1) + fib m) * (fib n)
         + (fib (m + 2) + fib (m + 1)) * (fib (n + 1)) := by ring
       _ = (fib (m + 2)) * (fib n)
         + (fib (m + 3)) * (fib (n + 1)) := by rfl
       _ = fib (3 + m - 1) * fib n
         + fib (3 + m) * fib (1 + n) := by
         have ih1 : m + 2 = 3 + m - 1 := by omega
         simp only [ih1]; congr 1; ring_nf;

lemma fib_gcd_n_geq_m (n : ℕ) :
  ∀ m : ℕ, n ≥ m → Nat.gcd (fib n) (fib m) = fib (Nat.gcd n m) := by
  induction n using Nat.strong_induction_on with
  | h n' ih =>
    match n' with
    | 0 =>
      intro m hm;
      rw [fib]; simp
    | n' + 1 =>
      let n := n' + 1
      intro m hnm
      by_cases hm : m < n
      · -- n ≥ 1 and m < n
        have decomp_fib_n :
          fib n = (fib (n - m - 1)) * (fib m)
                + (fib (n - m)) * (fib (m + 1)) := by
          have : fib n = fib (m + (n - m)) := by congr; omega
          rw [this]; apply fib_naddm m (n - m) (by omega)
        calc Nat.gcd (fib n) (fib m)
          = Nat.gcd ((fib (n - m - 1)) * (fib m)
          + (fib (n - m)) * (fib (m + 1))) (fib m) := by simp [decomp_fib_n];
        _ = Nat.gcd ((fib (n - m)) * (fib (m + 1))) (fib m) := by
          refine Nat.gcd_mul_right_add_left (fib m) (fib (n - m) * fib (m + 1))
                (fib (n - m - 1))
        _ = Nat.gcd (fib (n - m)) (fib m) := by
          refine Nat.gcd_mul_left_left_of_gcd_eq_one ?_
          simp only [Nat.gcd_comm, fib_coprime]
        _ = fib (Nat.gcd (n - m) m) := by
          by_cases hh : m ≥ n - m
          · rw [Nat.gcd_comm, ih m (by omega) (n - m) hh, Nat.gcd_comm]
          · by_cases hm0 : m ≥ 1
            · apply ih (n - m) (by omega) m (by linarith)
            · have : m = 0 := by exact Nat.eq_zero_of_not_pos hm0
              rw [this]; simp [fib];
        _ = fib (Nat.gcd n m) := by
          congr 1; exact Nat.gcd_sub_self_left hnm
      · have : n' + 1 = m := by omega
        rw [this]; simp [Nat.gcd_self]

theorem fib_gcd (n m : ℕ) :
  Nat.gcd (fib n) (fib m) = fib (Nat.gcd n m) := by
  by_cases hnm : n ≥ m
  · rw [fib_gcd_n_geq_m n m hnm]
  · have hmn : m ≥ n := by omega
    rw [Nat.gcd_comm, fib_gcd_n_geq_m m n hmn, Nat.gcd_comm]

example : Nat.gcd (fib 2022) (fib 2025) = 2 := by
  simp [fib_gcd]; rfl;

end Fibobacci
