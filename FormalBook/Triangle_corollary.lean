
--This stuff is copy pasted from another file so I don't have rewrite definitions

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs
import Mathlib.Data.Real.Sign

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n


noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (- (T 0 1) * (T 1 0) + (T 0 0) * (T 1 1) + (T 0 1) * (T 2 0) - (T 1 1) * (T 2 0) - (T 0 0) * (T 2 1) + (T 1 0) * (T 2 1)) / 2

def is_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_hull T) ∧
  (Set.PairwiseDisjoint S open_hull)

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)




def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y


def Psquare : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

def unit_square1 : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}
def unit_square : Set ℝ²
  := closed_hull Psquare

def open_unit_square1 : Set ℝ² := {x : ℝ² | 0 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1}
def open_unit_square : Set ℝ²
  := open_hull Psquare


@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl
-- Copy pasted stuff ends here


--def unit_square : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

/-I think that the most important subpart of this corollary is to show that the volume/surface
of the triangles must add up to one. Since we "define" the volume of the triangle
to be this determinant, we have to somehow relate this to the actual volume.
So far, I have not seen any mathlib stuff about the volume of triangles.
However, I have seen a theorem stating that if you linear transform an object the volume will be
the original volume times the absolute value of the determinant.

As a consequence, I think it would make sense to first calculate the volume
of the triangle ((0,0),(1,0)(0,1)), which I will call the unit triangle,
and any other volume of triangles will follow.

For this, I think I should use the fact that the square can be divided into two 'similar' triangles.
However, it is slightly awkward, because if we divide a square up into open triangles, we are missing
a line of measure zero. -/


def unit_triangle : Triangle := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)

def open_unit_triangle := open_hull unit_triangle
def closed_unit_triangle := closed_hull unit_triangle

-- This is what we want to prove
theorem volume_open_unit_triangle : (MeasureTheory.volume open_unit_triangle).toReal = (1/2 : ℝ ) := by sorry

--We additionally want its flipped version

def flip_unit_triangle : Triangle  := fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0)
def open_flip_unit_triangle := open_hull flip_unit_triangle
def closed_flip_unit_triangle := closed_hull flip_unit_triangle

--Then additionally we have the diagonal
def diagonal_line : Segment := fun | 0 => (v 1 0) | 1 => (v 0 1)
def open_diagonal_line := open_hull diagonal_line

--We now want to show the open_unit_square is the disjoint union of these open triangles
--and the open diagonal

def union_of_open_triangles := open_unit_triangle  ∪ open_flip_unit_triangle

theorem aux (X Y : Type)(x y : X → Y):(∀ z : X, x z = y z) → x = y := by exact?

theorem open_unit_square_in_union : open_unit_square1 = union_of_open_triangles ∪  open_diagonal_line := by
  have hunit : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl
  have hdiag : diagonal_line = fun | 0 => (v 1 0) | 1 => (v 0 1) := by rfl
  ext x
  constructor
  · rintro ⟨ h,h1,h2, h3 ⟩
    have h7 := lt_trichotomy (x 0 +x 1) 1
    rcases h7 with (h4 | h5| h6)
    · left
      left
      use (fun | 0 => (1- x 0 - x 1) | 1 => x 0 | 2 => x 1)
      constructor
      · constructor
        · dsimp
          intro i
          fin_cases i <;> dsimp <;> linarith
        · rw[Fin.sum_univ_three]
          dsimp
          linarith
      · dsimp
        rw[Fin.sum_univ_three, hunit]
        simp
        ext i
        fin_cases i <;> simp
    · right
      use (fun | 0 => x 0 | 1 => x 1 )
      constructor
      · constructor
        · dsimp
          intro i
          fin_cases i <;> dsimp <;> linarith
        · rw[Fin.sum_univ_two]
          dsimp
          linarith
      · dsimp
        rw[Fin.sum_univ_two,hdiag]
        simp
        ext i
        fin_cases i <;> simp
    · left
      right

      sorry

  · sorry

theorem aux1 (a c : ℝ ): (a< c) ∨ (a = c) ∨ (a > c):= by exact lt_trichotomy a c



theorem open_unit_squares_are_same : open_unit_square = open_unit_square1 := by
  ext x
  constructor
  · rintro ⟨ a,⟨ ⟨ h2,h3⟩ ,h1⟩ ⟩
    have hp : Psquare = (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1) := by rfl
    rw[← h1]
    dsimp
    rw[Fin.sum_univ_four,hp] at *
    dsimp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h2 0 ,h2 1 ,h2 2, h2 3]
  · rintro ⟨ h,h1,h2, h3 ⟩


    sorry


theorem open_square_union_of : open_unit_square = union_of_open_triangles ∪  open_diagonal_line := by
  ext x
  constructor
  · rintro ⟨ a,⟨ ⟨ h2,h3⟩ ,h1⟩ ⟩


    sorry
  · sorry
