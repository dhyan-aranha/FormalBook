import Mathlib
import FormalBook.sperner.segment_counting
import FormalBook.sperner.Triangle_corollary
import FormalBook.sperner.monsky_even

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


-- (X = ⋃ (Δ ∈ S), closed_hull Δ) ∧
-- (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, Δ₁ ≠ Δ₂ → Disjoint (open_hull Δ₁) (open_hull Δ₂))

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle),
      closed_hull unit_square = ⋃ (Δ ∈ S), closed_hull Δ ∧
      Set.PairwiseDisjoint S.toSet open_hull ∧
      ∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, MeasureTheory.volume (open_hull Δ₁) = MeasureTheory.volume (open_hull Δ₂) ∧
      S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by


  sorry
