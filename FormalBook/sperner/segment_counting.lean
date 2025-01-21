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

noncomputable def basic_avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (avoiding_segment_set X A).filter (fun L ↦ ∀ x ∈ X, x ∉ open_hull L)

def colin (u v w : ℝ²) : Prop := u ≠ w ∧ v ∈ open_hull (to_segment u w)

inductive Chain : ℝ² → ℝ² → Type
    | basic {u v : ℝ²}  : Chain u v
    | join {u v w : ℝ²} (hColineair : colin u v w) (C : Chain v w) : Chain u w

noncomputable def to_basic_segments {u v : ℝ²} : Chain u v → Finset Segment
    | Chain.basic              => {to_segment u v}
    | @Chain.join _ w _ _ C    => to_basic_segments C ∪ {to_segment u w}

noncomputable def reverse_chain {u v : ℝ²} (C : Chain u v) : Chain v u := sorry

noncomputable def chain_to_big_segment {u v : ℝ²} (_ : Chain u v) : Segment := to_segment u v

theorem segment_decomposition (X : Finset ℝ²) (A : Set ℝ²) {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) :
    ∃ (C : Chain (S 0) (S 1)), S = chain_to_big_segment C ∧
    (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
    = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by

    sorry
