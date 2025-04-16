import Mathlib
import FormalBook.sperner.segment_counting
import FormalBook.sperner.Triangle_corollary
import FormalBook.sperner.monsky_even

local notation "Triangle" => Fin 3 → (EuclideanSpace ℝ (Fin 2))

open Classical
open BigOperators

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle),
      closed_hull unit_square = ⋃ (Δ ∈ S), closed_hull Δ ∧
      Set.PairwiseDisjoint S.toSet open_hull ∧
      (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, MeasureTheory.volume (open_hull Δ₁) = MeasureTheory.volume (open_hull Δ₂)) ∧
      S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  constructor
  · -- Hard direction
    intro ⟨S, hCover, hDisjoint, hArea, hCard⟩
    refine ⟨?_,?_⟩
    · -- Add lemma in basic_definitions/covers that you cannot cover a nonempty thing by
      -- an empty cover
      sorry
    · by_contra hOdd
      rw [Nat.not_even_iff_odd] at hOdd
      have ⟨_,Γ,v,hv⟩ := valuation_on_reals
      have ⟨T,hTS,hTrainbow⟩ := monsky_rainbow v S ?_ ?_
      · apply no_odd_rainbow_triangle v T hTrainbow hv ?_
        · use n, hOdd
          rw [←hCard]
          refine equal_area_cover_implies_triangle_area_n S ?_ T hTS
          -- Refactor is_equal_area_cover to mean actually the hypotheses here
          sorry
        · -- This is open for now: valuation assigns 1 to 1/n for n odd.
          -- Should be in appendix somewhere.
          sorry
      · -- The formulatin of the statement that S is a 'disjoint cover'
        -- is different in "is_disjoint_cover" and the statemtn of this theorem
        -- we should refactor so that it is just one line.
        sorry
      · -- Similarly we should have a seperate lemma that says that for any "equal area cover"
        -- of the triangles all determinants are nonzero.
        sorry
  · -- Easy direction
    intro ⟨hnNonzero, hnEven⟩
    have ⟨S, hScover, hScard⟩  := monsky_easy_direction' hnEven hnNonzero
    use S
    -- monsky_easy_direction' should be changed so that the rest of this is one line
    -- To Do: Make area definitions combine better...
    refine ⟨hScover.1.1, hScover.1.2, ?_, hScard⟩
    intro T₁ hT₁ T₂ hT₂
    rw [volume_open_triangle', volume_open_triangle']
    have ⟨A,hA⟩ := hScover.2
    unfold triangle_area at hA
    rw [hA _ hT₁, hA _ hT₂]
