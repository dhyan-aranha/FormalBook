import Mathlib
import FormalBook.sperner.simplex_basic
import FormalBook.sperner.segment_triangle


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²


open Classical
open BigOperators
open Finset



noncomputable def segment_set (X : Finset ℝ²) : Finset Segment :=
    Finset.image (fun (a,b) ↦ to_segment a b) ((Finset.product X X).filter (fun (a,b) ↦ a ≠ b))

noncomputable def avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (segment_set X).filter (fun L ↦ Disjoint (closed_hull L) (A))
