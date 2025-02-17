import Mathlib

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

def id_map : ℝ² → ℝ × ℝ := fun x ↦ ⟨x 0, x 1⟩

example (X : Set ℝ²) : MeasureTheory.volume X = MeasureTheory.volume (id_map '' X) := by
  sorry
