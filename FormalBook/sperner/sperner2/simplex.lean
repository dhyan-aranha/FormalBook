import Mathlib
import Mathlib.Tactic

/-!
# Simplices and Convex Hulls in ℝ²

This file defines simplices and convex hulls in the two-dimensional Euclidean space.

## Main definitions

* `closed_simplex n`  - The standard n-dimensional closed simplex
* `open_simplex n`    - The standard n-dimensional open simplex
* `convex_hull`       - The convex hull of vertices of a polygon
* `open_convex_hull`  - The relative interior of the convex hull
* `hull_boundary`     - The boundary of a convex hull

## Implementation notes

The `Fin n → ℝ²` type represents vertices of a polygon. When vertices define a proper
n-gon (i.e., no vertex lies within the convex hull of the others), `open_convex_hull` gives
the topological interior. Otherwise, `open_convex_hull` represents the relative interior of
the convex hull.

-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical
open Finset
open BigOperators

/-- `v x y` creates a point in the 2-dimensional Euclidean space ℝ² with coordinates (x, y).
This provides a convenient shorthand for constructing points without having to use the more verbose
function notation. -/
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl

@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


variable {n : ℕ}
variable {α : Fin n → ℝ}
variable {P : Fin n → ℝ²}


/-- `closed_simplex n` is the standard n-dimensional closed simplex in ℝⁿ,
defined as the set of points with non-negative coordinates that sum to 1. -/
def closed_simplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}

/-- `open_simplex n` is the standard n-dimensional open simplex in ℝⁿ,
defined as the set of points with strictly positive coordinates that sum to 1. -/
def open_simplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

variable (α) (P) in
/-- `affine_combo α f` computes the affine combination of points in `P` using weights from `α`.
This represents a point in ℝ² as a weighted sum of vertices. -/
noncomputable def affine_combo : ℝ² := ∑ i, α i • P i

variable (P) in
/-- `convex_hull P` is the convex hull of the vertices of a polygon defined by `f`.
It represents all points that can be expressed as convex combinations of the vertices. -/
def convex_hull : Set ℝ² := (affine_combo . P) '' closed_simplex n

variable (P) in
/-- `open_convex_hull f` is the relative interior of the convex hull of the polygon vertices
defined by `f`. This represents the topological interior only when the vertices form a proper
polygon (i.e., no vertex lies within the convex hull of the others). When all vertices are
identical, both `open_convex_hull f` and `convex_hull f` reduce to a singleton set containing
that vertex. -/
def open_convex_hull : Set ℝ² := (affine_combo . P) '' open_simplex n



/-- `simplex_vertex i` represents a corner (or vertex) of the standard simplex,
with a 1 at position i and 0 elsewhere. This corresponds to the unit vector e_i. -/
def simplex_vertex (i : Fin n) : Fin n → ℝ := fun j ↦ ite (i = j) 1 0

/-- Each vertex of the standard simplex belongs to the closed simplex. -/
lemma simplex_vertex_mem_closed_simplex {i : Fin n} : simplex_vertex i ∈ closed_simplex n :=
  ⟨fun j ↦ by by_cases h : i = j <;> simp [simplex_vertex, h], by simp [simplex_vertex]⟩

/-- A convex combination using coefficients from a simplex vertex selects the corresponding
point from the set of vertices. -/
@[simp]
lemma simplex_vertex_evaluates_to {i : Fin n} :
  affine_combo (simplex_vertex i) P = P i := by simp [affine_combo, simplex_vertex]

/-- Each vertex of a polygon belongs to the convex hull of the polygon's vertices. -/
@[simp]
lemma vertex_mem_convex_hull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ convex_hull P := by
  exact ⟨simplex_vertex i, simplex_vertex_mem_closed_simplex, simplex_vertex_evaluates_to⟩

/-- The open simplex is a subset of the closed simplex. This is because
any point with strictly positive coordinates also has non-negative coordinates. -/
lemma open_simplex_subset_closed_simplex {n : ℕ} : open_simplex n ⊆ closed_simplex n :=
  fun _ ⟨hαpos, hαsum⟩ ↦ ⟨fun i ↦ by linarith [hαpos i], hαsum⟩

/-- The open convex hull of a set of points is a subset of its convex hull. -/
lemma open_convex_hull_subset_convex_hull {n : ℕ} (P : Fin n → ℝ²) :
  open_convex_hull P ⊆ convex_hull P :=
  Set.image_mono open_simplex_subset_closed_simplex

/-- The 0-dimensional closed simplex is empty. -/
lemma closed_simplex_zero_is_empty : closed_simplex 0 = ∅ := by
  simp only [closed_simplex, IsEmpty.forall_iff, univ_eq_empty, sum_empty,
             zero_ne_one, and_false, Set.setOf_false]

/-- The 0-dimensional open simplex is empty. -/
lemma open_simplex_zero_is_empty : open_simplex 0 = ∅ :=
 closed_simplex_zero_is_empty |> subset_of_subset_of_eq open_simplex_subset_closed_simplex
 |> Set.subset_empty_iff.1






/-- When a function maps every vertex to the same point P, the convex hull
is just the singleton set containing P. -/
lemma convex_hull_constant_point {n : ℕ} {P : ℝ²} (hn : n ≠ 0) :
  convex_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext _
  constructor
  · intro ⟨_, hα, hαv⟩
    simp [←hαv, ←sum_smul, hα.2, one_smul, Set.mem_singleton_iff]
  · intro hv; rw [hv]
    exact vertex_mem_convex_hull (i := ⟨0, Nat.zero_lt_of_ne_zero hn⟩)

/-- If the convex hull of vertices is a singleton set {P}, then all vertices must equal P. -/
lemma convex_hull_singleton_implies_constant {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
  (hc : convex_hull f = {P}) : ∀ i, f i = P := by
  simp_rw [←Set.mem_singleton_iff, ←hc]
  exact fun i ↦ vertex_mem_convex_hull








/-- `hull_boundary P` represents the boundary of the convex hull of the polygon
with vertices P. It consists of all points that are in the convex hull but not
in its relative interior. For a proper polygon (where no vertex lies within the
convex hull of the others), this corresponds to the topological boundary. -/
def hull_boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² :=
  (convex_hull P) \ (open_convex_hull P)
