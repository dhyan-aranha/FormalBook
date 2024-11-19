/-
Copyright 2024 the Amsterdam Lean seminar

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching,
Jan,
Maris Ozols,
Casper,
Pjotr Buys,
Giacomo,
Dion Leijnse,
Thijs,
Thomas Koopman,
Jonas van der Schaaf,
Dhyan,
Lenny Taelman.
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

open BigOperators

/-!
# One square and an odd number of triangles

## TODO
  - Monsky's Theorem
    - proof
      - Lemma 1
        - proof
      - Corollary
        - proof
      - Lemma 2
        - proof
          - (A)
          - (B)
  - Appendix: Extending valuations
    - definition
    - Theorem
      - proof
    - Lemma
      - proof
    - Claim
    - Zorn's Lemma
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

structure Triangle :=
  x : ℝ²
  y : ℝ²
  z : ℝ²

def closed_triangle (T : Triangle) : Set ℝ² :=
  { w | ∃ (α₁ α₂ α₃ : ℝ),
      0 ≤ α₁ ∧
      0 ≤ α₂ ∧
      0 ≤ α₃ ∧
      α₁ + α₂ + α₃ = 1 ∧
      w = (α₁) • (T.x) + (α₂) • (T.y) + (α₃) • (T.z)}

def open_triangle (T : Triangle) : Set ℝ² :=
  { w | ∃ (α₁ α₂ α₃ : ℝ),
      0 < α₁ ∧
      0 < α₂ ∧
      0 < α₃ ∧
      α₁ + α₂ + α₃ = 1 ∧
      w = (α₁) • (T.x) + (α₂) • (T.y) + (α₃) • (T.z)}

noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (- (T.x 1) * (T.y 0) + (T.x 0) * (T.y 1) + (T.x 1) * (T.z 0) - (T.y 1) * (T.z 0) - (T.x 0) * (T.z 1) + (T.y 0) * (T.z 1)) / 2

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_triangle T) ∧
  (Set.PairwiseDisjoint S open_triangle) ∧
  ∀ T₁ T₂, T₁ ∈ S → T₂ ∈ S → triangle_area T₁ = triangle_area T₂

def unit_square : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  sorry
