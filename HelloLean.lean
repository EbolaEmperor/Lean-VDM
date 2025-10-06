import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by
  intro ε ε_pos
  specialize hf ε ε_pos
  rcases hf with ⟨δ, δ_pos, hf⟩
  specialize hu δ δ_pos
  rcases hu with ⟨N, hu⟩
  use N
  intro n n_geqN
  specialize hu n n_geqN
  specialize hf (u n)
  apply hf hu
