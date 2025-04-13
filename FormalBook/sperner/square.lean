import Mathlib
import Mathlib.Tactic
import FormalBook.sperner.simplex_basic
import FormalBook.sperner.segment_triangle
import FormalBook.sperner.miscellaneous
import FormalBook.sperner.basic_definitions


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


/-
  Basic properties about the unit square, i.e. the square with vertices 00, 10, 11, 01.
-/

def unit_square : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)


lemma closed_unit_square_eq : closed_hull unit_square = {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩ i
    rw [←hxα, ←hα.2]
    have hs : α 1 + α 2 ≤ α 0 + α 1 + α 2 + α 3 := by linarith [hα.1 0, hα.1 3]
    fin_cases i <;> simp [unit_square, Fin.sum_univ_four, Left.add_nonneg, v, hα.1, hs]
  · intro hx
    use fun
          | 0 => (1 - x 0 ) * (1 - x 1)
          | 1 => x 0 * (1 - x 1)
          | 2 => x 0 * x 1
          | 3 => (1 - x 0) * x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun i ↦ by fin_cases i <;> simp [hx 0, hx 1,  Left.mul_nonneg]
    · rw [Fin.sum_univ_four]; ring
    · ext i; fin_cases i <;> (simp [Fin.sum_univ_four, unit_square, v]; ring)



-- The open unit square is more or less the same
lemma open_unit_square_eq : open_hull unit_square = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩
    intro i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [unit_square, Fin.sum_univ_four, Left.add_pos,v , hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [unit_square, Fin.sum_univ_four, v]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    use fun
          | 0 => (1 - x 0 ) * (1 - x 1)
          | 1 => x 0 * (1 - x 1)
          | 2 => x 0 * x 1
          | 3 => (1 - x 0) * x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun i ↦ by fin_cases i <;> simp [hx 0, hx 1]
    · rw [Fin.sum_univ_four]; ring
    · ext i; fin_cases i <;> (simp [Fin.sum_univ_four, unit_square, v]; ring)


lemma element_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unit_square) :
    ∃ i, x i = 0 ∨ x i = 1 := by
  by_contra hxn; push_neg at hxn
  have hx₂ := boundary_in_closed hx
  rw [closed_unit_square_eq] at hx₂
  apply boundary_not_in_open hx
  rw [open_unit_square_eq]
  intro i
  constructor
  · exact lt_of_le_of_ne (hx₂ i).1 (hxn i).1.symm
  · exact lt_of_le_of_ne (hx₂ i).2 (hxn i).2

lemma boundary_unit_square_eq : boundary unit_square = { x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∃ i, x i = 0 ∨ x i = 1)} := by
  rw [Set.setOf_and, ←closed_unit_square_eq]
  ext
  refine ⟨fun hx ↦ ⟨boundary_sub_closed _ hx, element_in_boundary_square hx⟩,
          fun ⟨hc, ⟨i, hno⟩⟩ ↦ (Set.mem_diff _).mpr ⟨hc, ?_⟩⟩
  rw [open_unit_square_eq]
  exact fun hco ↦ by rcases hno <;> linarith [hco i]



lemma segment_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unit_square)
    : ∃ i, ∀ L, x ∈ open_hull L → closed_hull L ⊆ closed_hull unit_square → (seg_vec L) i = 0 := by
  by_contra hNonzero
  push_neg at hNonzero
  have ⟨i, hxi⟩ := element_in_boundary_square hx
  have ⟨L,hxL,hL, hvec⟩ := hNonzero i
  have ⟨δ,hδ, hδx⟩ := seg_dir_sub hxL
  cases' hxi with hxi hxi
  · specialize hδx (δ * (- Real.sign ((seg_vec L) i))) (by
      simp [abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unit_square_eq] at ht
    have ht₂ := (ht i).1
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]
  · specialize hδx (δ * (Real.sign ((seg_vec L) i))) (by
      simp [abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unit_square_eq] at ht
    have ht₂ := (ht i).2
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]


/- A version that states that the open_unit_square is open. -/
--The proof below is not as difficult as it seems, but I just needed a lot of explicit bounds because simp was not cooperating
lemma open_unit_square_open_dir {x : ℝ²} (y : ℝ²) (hx : x ∈ open_hull unit_square) :
    ∃ (ε : ℝ), ε > 0 ∧ ∀ (n : ℕ), x + (1 / (n : ℝ)) • (ε • y) ∈ open_hull unit_square := by
  simp_rw [open_unit_square_eq] at *
  -- The constant we will choose is of order 1/ y, so we have to make an exception for y =0
  by_cases h : ∀ i, (y  i= 0) -- this formulation was slightly easier for me
  · use 1
    have h1: y = 0
    . ext i; exact h i
    rw[h1]
    simp[hx]
  -- I would prefer to define the epsilon with an infinum over i, rather than doing it explicitly,
  -- but I could not find the right api to show this infinum is bigger than zero (as it is only a infinum over a finite index)
  · use ((1/(max |y 0| |y 1|))*(1/2) )* min (min (x 0) (1- x 0)) (min (x 1) (1 - x 1))
    have h2 : (max |y 0| |y 1|) > 0
    · push_neg at h
      rcases h with ⟨ i, h2⟩; fin_cases i
      · exact lt_sup_of_lt_left (abs_pos.mpr (h2))
      · exact lt_sup_of_lt_right (abs_pos.mpr h2)
    have h1: ∀ (i: Fin 2), 0 < (1- x i) := (fun i ↦  by linarith [hx i] )
    have h8: 0 <  (2* (|y 0| ⊔ |y 1|)) :=  (mul_pos (by norm_num) h2)
    have hxbound :  0 < x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))
    · apply lt_min <;> apply lt_min
      · exact (hx 0).1
      · exact h1 0
      · exact (hx 1).1
      · exact h1 1
    constructor
    · exact mul_pos (by simp[h2]) hxbound
    · have h3: ∀ i, |-y i| <  (2*(max |y 0| |y 1|))
      · intro i
        refine lt_mul_of_one_lt_of_le_of_pos (by norm_num) ?_ h2
        fin_cases i <;> simp
      have h4: ∀ i, x i ≥  (x 0 ⊓ (1 - x 0)) ⊓ (x 1 ⊓ (1 - x 1))
      · intro i; fin_cases i
        apply inf_le_of_left_le; apply inf_le_of_left_le; rfl
        apply inf_le_of_right_le; apply inf_le_of_left_le; rfl
      have h5 : ∀ i, 1 - x i ≥  (x 0 ⊓ (1 - x 0)) ⊓ (x 1 ⊓ (1 - x 1))
      · intro i; fin_cases i
        apply inf_le_of_left_le; apply inf_le_of_right_le; rfl
        apply inf_le_of_right_le; apply inf_le_of_right_le; rfl

      intro n i; simp only [one_div, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

      by_cases hn : ( n= 0) --mathematically, n should be at least 1, but because 1/ 0 = 0, the statement still holds for n = 0, but just requires a different proof
      · rw[hn]; simp[hx i]
      --for n≥ 1, the proof is as follows
      have hn4 : (n : ℝ ) ≥ 1 :=  Nat.one_le_cast.mpr ( Nat.one_le_iff_ne_zero.mpr hn)
      have h7: (1/(n: ℝ )) ≤  1 := by exact (div_le_one₀ (gt_of_ge_of_gt hn4 (by norm_num))).mpr hn4
      constructor
      · apply neg_lt_iff_pos_add.mp
        have h6: -((↑n)⁻¹ * ((|y 0| ⊔ |y 1|)⁻¹ * 2⁻¹ * (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) * y i)) =    ((-y i) / (2*(|y 0| ⊔ |y 1|))) * (1/n)* (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) := by ring
        rw[h6]
        refine  mul_lt_of_lt_one_of_le_of_pos ?_ (h4 i) hxbound
        refine  mul_lt_of_lt_one_of_le_of_pos ?_ (h7) (one_div_pos.mpr (gt_of_ge_of_gt hn4 (by norm_num)))
        apply Bound.div_lt_one_of_pos_of_lt h8 (lt_of_abs_lt (h3 i))

      · apply lt_tsub_iff_left.mp
        have h6: ((↑n)⁻¹ * ((|y 0| ⊔ |y 1|)⁻¹ * 2⁻¹ * (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) * y i)) =    ((y i) / (2*(|y 0| ⊔ |y 1|))) * (1/n)* (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) := by ring
        rw[h6]
        refine  mul_lt_of_lt_one_of_le_of_pos ?_ (h5 i) hxbound
        refine  mul_lt_of_lt_one_of_le_of_pos ?_ (h7) (one_div_pos.mpr (gt_of_ge_of_gt hn4 (by norm_num)))
        simp_rw[abs_neg] at h3
        apply Bound.div_lt_one_of_pos_of_lt h8 (lt_of_abs_lt (h3 i))






lemma el_boundary_square_triangle_dir {x : ℝ²} (hx : x ∈ boundary unit_square):
    ∃ σ ∈ ({-1,1} : Finset ℝ), ∀ (Δ : Triangle), (det Δ ≠ 0) →
    (closed_hull Δ ⊆ closed_hull unit_square) → (∃ i, x ∈ open_hull (Tside Δ i))
    → (∃ εΔ > 0, ∀ y, 0 < y → y ≤ εΔ → x + (σ * y) • (v 1 1) ∈ open_hull Δ) := by
    -- First we produce such triangle
    by_cases hΔ : ∃ Δ, (det Δ ≠ 0) ∧ (closed_hull Δ ⊆ closed_hull unit_square) ∧ (∃ i, x ∈ open_hull (Tside Δ i))
    · have ⟨Δ, hArea, hΔP, ⟨j,hSide⟩⟩ := hΔ
      have ⟨σ, hσ, ⟨δ,hδ, hδx⟩,_⟩  := seg_inter_open (y := v 1 1) hSide hArea ?_
      · use σ, hσ
        intro Δ' hArea' hΔ'P ⟨j',hSide'⟩
        have ⟨σ', hσ', ⟨δ',hδ', hδx'⟩, _⟩  := seg_inter_open (y := v 1 1) hSide' hArea' ?_
        · use δ', hδ'
          convert hδx' using 5
          rw [mul_smul, smul_comm]
          congr
          simp only [mem_insert, mem_singleton] at hσ hσ'
          have hσσ' : σ' = σ ∨ σ' = - σ := by
            cases' hσ with hσ hσ <;> cases' hσ' with hσ' hσ' <;> (rw [hσ, hσ']; simp)
          cases' hσσ' with hσσ' hσσ'
          · exact hσσ'.symm
          · exfalso
            specialize hδx (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
            specialize hδx' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
            rw [hσσ'] at hδx'
            have ⟨i, hL⟩ := segment_in_boundary_square hx
            specialize hL (fun | 0 => x + (δ ⊓ δ') • σ • v 1 1 | 1 => x + (δ ⊓ δ') • -σ • v 1 1) ?_ ?_
            · use fun | 0 => 1/2 | 1 => 1/2
              refine ⟨⟨?_,?_⟩,?_⟩
              · intro i
                fin_cases i <;> simp
              · simp; ring
              · ext i
                fin_cases i <;> (simp; ring)
            · apply closed_hull_convex
              intro i
              fin_cases i
              · exact hΔP (open_sub_closed _ hδx)
              · exact hΔ'P (open_sub_closed _ hδx')
            · unfold seg_vec at hL
              fin_cases i <;>(
                cases' hσ with hσ hσ <;>(
                  simp [hσ, neg_eq_zero] at hL
                  ring_nf at hL
                  try simp [neg_eq_zero,v] at hL
                  linarith [lt_min hδ hδ']
                  ))
        · apply aux_det₂
          · intro this
            rw [seg_vec_zero_iff] at this
            exact (nondegen_triangle_imp_nondegen_side j' hArea') this
          · have ⟨i,hi⟩ := segment_in_boundary_square hx
            exact ⟨i, hi _ hSide' (subset_trans closed_side_sub' hΔ'P)⟩
      · apply aux_det₂
        · intro this
          rw [seg_vec_zero_iff] at this
          exact (nondegen_triangle_imp_nondegen_side j hArea) this
        · have ⟨i,hi⟩ := segment_in_boundary_square hx
          exact ⟨i, hi _ hSide (subset_trans closed_side_sub' hΔP)⟩
    · push_neg at hΔ
      use (1 : ℝ), by simp
      intro Δ hArea hΔP ⟨i,hSide⟩
      exact False.elim (hΔ Δ hArea hΔP i hSide)

lemma boundary_leave_dir {x : ℝ²} (hx : x ∈ boundary unit_square) :
    ∃ σ ∈ ({1, -1} : Finset ℝ), ∀ ε > 0, x + (σ * ε) • (v 1 1) ∉ closed_hull unit_square := by
  by_contra h_contra
  push_neg at h_contra
  have ⟨ε₁, hε₁pos, hx₁⟩ := h_contra 1 (by simp)
  have ⟨ε₂, hε₂pos, hx₂⟩ := h_contra (-1) (by simp)
  have ⟨i, hi⟩ := segment_in_boundary_square hx
  specialize hi (segment_around_x x (v 1 1) ε₁ ε₂) ?_ ?_
  · exact open_hull_segment_around hε₁pos hε₂pos
  · apply closed_hull_convex
    intro i
    fin_cases i <;> simpa only [to_segment]
  · simp [segment_around_x, seg_vec, to_segment, v] at hi
    fin_cases i <;> (simp_all; linarith)

lemma segment_triangle_pairing_int
    (S : Finset Triangle)
    (hCover : is_disjoint_cover (closed_hull unit_square) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0)
    (L : Segment)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ open_hull unit_square)
    (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 2 := by
  -- We first take an element from open_hull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- A useful statement:
  have hU : ∀ Δ ∈ S, x ∉ open_hull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (open_sub_closed _ (hLunit hLx)) hU ?_
  · -- Now it should follow that the closed hull of L is contained in the closed hull of Tside Δ i
    have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
    -- We take a vector y that is not in the direction of any side.
    have ⟨y,hy⟩ := perp_vec_exists (Finset.biUnion S (fun Δ ↦ image (fun i ↦ Tside Δ i) (univ))) ?_
    · -- Specialize to the Δᵢ
      have yΔi := hy (Tside Δ i) (by rw [mem_biUnion]; exact ⟨Δ,hΔ,by rw [mem_image]; exact ⟨i, mem_univ _,rfl⟩⟩)
      -- Use this to show that there is a direction of y to move in which does not intersect Δ
      have ⟨σ, hσ, ⟨δ, hδ, hain⟩, haout⟩ := seg_inter_open hxi (hArea Δ hΔ) yΔi
      -- We have an epsilon such that x + (1/n) ε • - σ • y lies inside the open triangle for all n ∈ ℕ
      have ⟨ε,hεPos, hn⟩ := open_unit_square_open_dir (- σ • y) (hLunit hLx)
      -- This gives a map from ℕ to S assigning to each such ℕ a triangle that contains it.
      have hfS : ∀ n : ℕ, ∃ T ∈ S, x + (1 / (n : ℝ)) • ε • -σ • y ∈ closed_hull T := by
        intro n
        have this := (open_sub_closed _ (hn n))
        rw [hCover.1, Set.mem_iUnion₂] at this
        have ⟨T,hT,hT'⟩ := this
        exact ⟨T,hT,hT'⟩
      choose f hfS hfCl using hfS
      -- This means that there is a triangle with infinitely many vectors of the form x + (1 / (n : ℝ)) • ε • -σ • y
      have ⟨Δ', hΔ', hΔ'Inf⟩ := finset_infinite_pigeonhole hfS
      -- First we prove that Δ' ≠ Δ
      have ⟨l,hl,hlZ⟩ := infinite_distinct_el hΔ'Inf 0
      have hMemΔ' := hfCl l
      rw [hl] at hMemΔ'
      have hΔneq : Δ' ≠ Δ := by
        by_contra hΔeq
        rw [hΔeq] at hMemΔ'
        apply haout ((1/ (l : ℝ) * ε)) (by field_simp)
        convert hMemΔ' using 2
        simp [mul_smul]
      -- Then we prove that x ∈ closed_hull Δ'
      have hxΔ' := closed_triangle_is_closed_dir (x := x) (y := ε • -σ • y) (hArea Δ' hΔ') (by
        refine Set.Infinite.mono ?_ hΔ'Inf
        intro m _
        have _ := hfCl m
        simp_all
        )
      -- This means that x lies in some side of Δ'
      have ⟨i',hi'⟩ := el_in_boundary_imp_side (hArea Δ' hΔ') (Set.mem_diff_of_mem hxΔ' (fun d ↦ hU Δ' hΔ' d)) (fun i ht ↦ hv Δ' hΔ' i (by rwa [←ht]))
      -- This again means that L lies completely in Tside Δ' i
      have hLΔ' := seg_sub_side (hArea Δ' hΔ') hLx hi' (hInt Δ' hΔ') (hv Δ' hΔ')
      -- We now have our two elements that should give the cardinality 2.
      rw [card_eq_two]
      use Δ', Δ, hΔneq
      ext Δ''
      constructor
      · -- The hard part of the proof continues here.
        -- We have to show that if there is a third triangle that it intersects one of the triangles.
        intro hΔ''
        rw [mem_filter] at hΔ''
        have ⟨hΔ'', hLΔ''⟩ := hΔ''
        have ⟨i'',hi''⟩ := el_in_boundary_imp_side (hArea Δ'' hΔ'') (hLΔ'' (open_sub_closed _ hLx)) (fun i ht ↦ hv Δ'' hΔ'' i (by rwa [←ht]))
        -- We define σ' and σ''
        have yΔi' := hy (Tside Δ' i') (by rw [mem_biUnion]; exact ⟨Δ',hΔ',by rw [mem_image]; exact ⟨i', mem_univ _,rfl⟩⟩)
        have ⟨σ', hσ', ⟨δ',hδ', hain'⟩, haout'⟩ := seg_inter_open hi' (hArea Δ' hΔ') yΔi'
        have yΔi'' := hy (Tside Δ'' i'') (by rw [mem_biUnion]; exact ⟨Δ'',hΔ'',by rw [mem_image]; exact ⟨i'', mem_univ _,rfl⟩⟩)
        have ⟨σ'', hσ'', ⟨δ'',hδ'', hain''⟩, haout''⟩ := seg_inter_open hi'' (hArea Δ'' hΔ'') yΔi''
        -- First we show that σ ≠ σ' The following argument is repeated
        -- three times and could use its own lemma
        have σneq : σ ≠ σ' := by
          intro σeq
          rw [σeq] at hain
          specialize hain (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
          specialize hain' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
          exact hΔneq (is_cover_open_el_imp_eq hCover.2 hΔ' hΔ hain' hain)
        have σ''mem : σ'' = σ ∨ σ'' = σ' := by
          simp only [mem_insert, mem_singleton] at hσ hσ' hσ''
          cases' hσ with t t <;> cases' hσ' with t' t' <;> cases' hσ'' with t'' t'' <;> (
            rw [t,t',t'']
            rw [t,t'] at σneq
            tauto)
        cases' σ''mem with h h
        · have hl : Δ'' = Δ := by
            by_contra hneq
            rw [h] at hain''
            specialize hain (min δ δ'') (lt_min hδ hδ'') (min_le_left δ δ'')
            specialize hain'' (min δ δ'') (lt_min hδ hδ'') (min_le_right δ δ'')
            exact hneq (is_cover_open_el_imp_eq hCover.2 hΔ'' hΔ hain'' hain)
          simp only [hl, mem_insert, mem_singleton, or_true]
        · have hl : Δ'' = Δ' := by
            by_contra hneq
            rw [h] at hain''
            specialize hain' (min δ' δ'') (lt_min hδ' hδ'') (min_le_left δ' δ'')
            specialize hain'' (min δ' δ'') (lt_min hδ' hδ'') (min_le_right δ' δ'')
            exact hneq (is_cover_open_el_imp_eq hCover.2 hΔ'' hΔ' hain'' hain')
          simp only [hl, mem_insert, mem_singleton, true_or]
      · intro hΔ''; simp at hΔ''
        cases' hΔ'' with hΔ'' hΔ'' <;> (rw [hΔ'']; simp)
        · exact ⟨hΔ', fun _ a ↦ (side_in_boundary (hArea Δ' hΔ') i') (hLΔ' a)⟩
        · exact ⟨hΔ, fun _ a ↦ (side_in_boundary (hArea Δ hΔ) i) (hLΔ a)⟩
    · intro L hL
      simp_rw [mem_biUnion, mem_image] at hL
      have ⟨T,TS,i',_,hTL⟩ := hL
      rw [←hTL]
      exact nondegen_triangle_imp_nondegen_side _ (hArea T TS)
  · intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx


lemma segment_triangle_pairing_boundary (S : Finset Triangle) (hCover : is_disjoint_cover (closed_hull unit_square) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ boundary unit_square) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 1 := by
  -- We first take an element from open_hull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- The point x is not in any open triangle:
  have hU : ∀ Δ ∈ S, x ∉ open_hull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- The point x is also not a vertex of any triangle
  have hxNvtx : ∀ (i : Fin 3), ∀ Δ ∈ S, x ≠ Δ i := by
    intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (boundary_sub_closed unit_square (hLunit hLx)) hU hxNvtx
  -- The closed hull of L is contained in the closed hull of Tside Δ i
  have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
  -- We will prove that Δ is the only triangle containing L in its boundary
  refine card_eq_one.mpr ⟨Δ,?_⟩
  simp_rw [eq_singleton_iff_unique_mem, mem_filter]
  constructor
  · exact ⟨hΔ, subset_trans hLΔ (side_in_boundary (hArea Δ hΔ) i)⟩
  · intro Δ' ⟨hΔ',hΔ'sub⟩
    -- There is a side i' such that
    have ⟨i',hi'⟩ := segment_in_boundary_imp_in_side (hArea Δ' hΔ') hΔ'sub
    -- Pick the direction for which the vector (1,1) points into the square
    have ⟨σ, hσval, hσ⟩ := el_boundary_square_triangle_dir (hLunit hLx)
    -- Specialize to the triangles Δ and Δ'
    have ⟨ε, hε, hεΔ⟩ := hσ Δ (hArea Δ hΔ) (is_cover_sub hCover.1 Δ hΔ) ⟨i,hxi⟩
    have ⟨ε', hε', hεΔ'⟩ := hσ Δ' (hArea Δ' hΔ') (is_cover_sub hCover.1 Δ' hΔ') ⟨i',open_segment_sub' hi' hL hLx⟩
    specialize hεΔ (min ε ε') (lt_min hε hε') (min_le_left ε ε')
    specialize hεΔ' (min ε ε') (lt_min hε hε') (min_le_right ε ε')
    exact is_cover_open_el_imp_eq hCover.2 hΔ' hΔ hεΔ' hεΔ




-- In this part we show that the the faces of the unit square are faces in the sense of convex
-- geometry. (see: https://en.wikipedia.org/wiki/Convex_set#Face_of_a_convex_set)
-- there are many sorries introduced here but nearly all of them are repeated arguments of what has
-- already been written.

noncomputable def top_face: Segment := fun | 0 => v 0 1 | 1 => v 1 1

noncomputable def bottom_face: Segment := fun | 0 => v 0 0 | 1 => v 1 0

noncomputable def left_face: Segment := fun | 0 => v 0 1 | 1 => v 0 0

noncomputable def right_face: Segment := fun | 0 => v 1 0 | 1 => v 1 1

def square_boundary_big : Fin 4 → Segment := fun
  | 0 => (fun | 0 => v 0 0 | 1 => v 1 0)
  | 1 => (fun | 0 => v 1 0 | 1 => v 1 1)
  | 2 => (fun | 0 => v 1 1 | 1 => v 0 1)
  | 3 => (fun | 0 => v 0 1 | 1 => v 0 0)

noncomputable def square_boundary_big_set : Finset Segment :=
   @Finset.biUnion (Fin 4) Segment _ ⊤ (fun i ↦ {square_boundary_big i})

lemma square_boundary_big_corners : ∀ i, ∀ j, ∃ k,
    square_boundary_big i j = unit_square k := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨0,rfl⟩

lemma square_boundary_big_injective : square_boundary_big.Injective := by
  intro i j hij
  have h₀ := congrFun hij 0
  fin_cases i <;> fin_cases j <;> simp_all [square_boundary_big, v] <;>
    (
      have g₀ := congrFun h₀ 0
      have g₁ := congrFun h₀ 1
      simp_all [v]
    )

lemma square_boundary_sides_nonDegen (i : Fin 4) : square_boundary_big i 0 ≠ square_boundary_big i 1 := by
  intro h_contra
  have h₀ := congrFun h_contra 0
  have h₁ := congrFun h_contra 1
  fin_cases i <;> (simp_all [square_boundary_big])




def boundary_line : Fin 4 → Fin 2 := fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1
def boundary_constant : Fin 4 → ℝ := fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0

@[simp]
lemma boundary_line_rw {i : Fin 4}
  : boundary_line i = (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) i := rfl

@[simp]
lemma boundary_constant_rw {i : Fin 4}
  : boundary_constant i = (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) i := rfl


lemma square_boundary_big_eq (i : Fin 4) :
    closed_hull (square_boundary_big i)
    = {x | 0 ≤ x (boundary_line i) ∧ x (boundary_line i) ≤ 1 ∧ x (boundary_line i + 1) = boundary_constant i} := by
  ext x; constructor
  · intro ⟨_, hα, hαx⟩
    simp_rw [Fin.sum_univ_two, simplex_closed_sub_fin2 hα 1] at hαx
    fin_cases i <;>
    simp [←hαx, square_boundary_big, simplex_co_leq_1 hα, hα.1]
  · intro ⟨hx₀, hx₁, hxr⟩
    fin_cases i
    rw [←reverse_segment_closed_hull]
    rotate_left
    rw [←reverse_segment_closed_hull]
    all_goals(
    convert linear_co_closed _ (real_to_fin_2_closed hx₀ hx₁)
    ext k; fin_cases k <;>
    all_goals simp_all [linear_combination,real_to_fin_2,reverse_segment,square_boundary_big,to_segment,v])


lemma square_boundary_in_boundary (i : Fin 4) :
    closed_hull (square_boundary_big i) ⊆ boundary unit_square := by
  rw [square_boundary_big_eq, boundary_unit_square_eq]
  exact fun _ ⟨_, _, _⟩ ↦
    ⟨fun j ↦ by fin_cases i <;> fin_cases j <;> simp_all, ⟨boundary_line i + 1, by fin_cases i <;> simp_all⟩⟩

lemma boundary_in_square_boundary {x : ℝ²} (hx : x ∈ boundary unit_square) :
    ∃ i, x ∈ closed_hull (square_boundary_big i) := by
  rw [boundary_unit_square_eq] at hx
  have ⟨j, hj⟩ := hx.2
  fin_cases j <;> cases' hj with hj hj
  use 3; rotate_left; use 1; rotate_left; use 0; rotate_left; use 2
  all_goals simp_all [square_boundary_big_eq]


lemma square_boundary_is_union_sides
    : boundary unit_square = ⋃ i, closed_hull (square_boundary_big i) := by
  ext x
  refine ⟨fun hx ↦ Set.mem_iUnion.mpr (boundary_in_square_boundary hx), ?_⟩
  intro ⟨S, ⟨i, hi⟩ , hxS⟩
  rw [←hi] at hxS
  exact square_boundary_in_boundary _ hxS


lemma square_boundary_big_inter_seg_aux₁ {a b c d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hd : 0 ≤ d) (habcd : a*b + c*d = 0) : b = 0 ∧ d = 0 := by
  rw [add_eq_zero_iff_of_nonneg
      ((mul_nonneg_iff_of_pos_left ha).mpr hb) ((mul_nonneg_iff_of_pos_left hc).mpr hd)] at habcd
  exact ⟨
    (mul_eq_zero_iff_left (ne_of_lt ha).symm).mp habcd.1,
    (mul_eq_zero_iff_left (ne_of_lt hc).symm).mp habcd.2⟩


lemma square_boundary_big_inter_seg_aux₂ {a b c d : ℝ} (hac : a + c = 1) (ha : 0 < a) (hb : b ≤ 1)
    (hc : 0 < c) (hd : d ≤ 1) (habcd : a*b + c*d = 1) : b = 1 ∧ d = 1 := by
  rw [←(sub_eq_zero), ←(sub_eq_zero (a := d)), ←neg_eq_zero, ←neg_eq_zero (a := d -1)]
  refine square_boundary_big_inter_seg_aux₁ (a := a) (c := c) ha ?_ hc ?_ ?_  <;>
  linarith


lemma square_boundary_big_inter_seg {S : Segment} {x : ℝ²} {i : Fin 4} (hx : x ∈ open_hull S)
    (hxi : x ∈ closed_hull (square_boundary_big i)) (hS : closed_hull S ⊆ closed_hull unit_square) :
    closed_hull S ⊆ closed_hull (square_boundary_big i) := by
  apply closed_hull_convex
  intro j
  have hS := fun k ↦ hS (corner_in_closed_hull (P := S) (i := k))
  have hS₀ := hS 0; have hS₁ := hS 1;
  rw [square_boundary_big_eq, closed_unit_square_eq] at *
  have ⟨α, hα, hαx⟩ := hx
  simp_rw [←hαx, Fin.sum_univ_two] at hxi
  have hαsum : α 0 + α 1 = 1 := by convert hα.2; exact (Fin.sum_univ_two α).symm
  clear hαx
  -- Unfortunately I couldn't get the simp to close it all, so there is a nonterminating simp here.
  fin_cases i <;> fin_cases j <;> simp_all
  · exact (square_boundary_big_inter_seg_aux₁ (hα.1 0) (hS 0 1).1 (hα.1 1) (hS 1 1).1 hxi.2.2).1
  · exact (square_boundary_big_inter_seg_aux₁ (hα.1 0) (hS 0 1).1 (hα.1 1) (hS 1 1).1 hxi.2.2).2
  · exact (square_boundary_big_inter_seg_aux₂ hαsum (hα.1 0) (hS 0 0).2 (hα.1 1) (hS 1 0).2 hxi.2.2).1
  · exact (square_boundary_big_inter_seg_aux₂ hαsum (hα.1 0) (hS 0 0).2 (hα.1 1) (hS 1 0).2 hxi.2.2).2
  · exact (square_boundary_big_inter_seg_aux₂ hαsum (hα.1 0) (hS 0 1).2 (hα.1 1) (hS 1 1).2 hxi.2.2).1
  · exact (square_boundary_big_inter_seg_aux₂ hαsum (hα.1 0) (hS 0 1).2 (hα.1 1) (hS 1 1).2 hxi.2.2).2
  · exact (square_boundary_big_inter_seg_aux₁ (hα.1 0) (hS 0 0).1 (hα.1 1) (hS 1 0).1 hxi.2.2).1
  · exact (square_boundary_big_inter_seg_aux₁ (hα.1 0) (hS 0 0).1 (hα.1 1) (hS 1 0).1 hxi.2.2).2


lemma square_boundary_pairwise_inter {i : Fin 4} :
    closed_hull (square_boundary_big (i - 1)) ∩ closed_hull (square_boundary_big i) = {unit_square i} := by
  rw [square_boundary_big_eq, square_boundary_big_eq]
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · intro h
    ext j
    fin_cases i <;> fin_cases j <;> simp_all [square_boundary_big, unit_square]
  · intro h; rw [h]
    fin_cases i <;> simp [square_boundary_big, unit_square]


lemma square_corner_in_boundary {i : Fin 4} :
    unit_square i ∈ closed_hull (square_boundary_big i):= by
  rw [←Set.singleton_subset_iff, ←square_boundary_pairwise_inter]
  exact Set.inter_subset_right

lemma square_corner_in_boundary' {i : Fin 4} :
    unit_square i ∈ closed_hull (square_boundary_big (i-1)):= by
  rw [←Set.singleton_subset_iff, ←square_boundary_pairwise_inter]
  exact Set.inter_subset_left

lemma segment_through_corner {S : Segment} {i : Fin 4} (hx : unit_square i ∈ open_hull S)
    (hS : closed_hull S ⊆ closed_hull unit_square) : closed_hull S = {unit_square i} := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · rw [←square_boundary_pairwise_inter, Set.subset_inter_iff]
    exact ⟨ square_boundary_big_inter_seg hx square_corner_in_boundary' hS ,
            square_boundary_big_inter_seg hx square_corner_in_boundary hS⟩
  · rw [Set.singleton_subset_iff]
    exact open_sub_closed _ hx


lemma cover_imples_corner_in_triangle
    {S : Finset Triangle}
    (hCover : is_cover (closed_hull unit_square) S.toSet) :
    ∀ i, ∃ T ∈ S, ∃ j, unit_square i = T j := by
  by_contra h_contra; push_neg at h_contra
  have ⟨c, hc⟩ := h_contra
  have ⟨T, hTsub, hT⟩ := is_cover_includes hCover (corner_in_closed_hull (i := c))
  specialize hc T hTsub
  have ⟨L, hLnTtriv, hOpen, hCsub⟩ := triangle_direction_sub hT hc
  apply hLnTtriv
  have hS := segment_through_corner hOpen (fun _ y ↦ (is_cover_sub hCover _ hTsub) (hCsub y))
  rw [closed_hull_constant_rev hS 0, closed_hull_constant_rev hS 1]



lemma convex_faces {x y p : ℝ²} (i : Fin 4) (hpiface : p ∈ closed_hull (square_boundary_big i))
(hp : p ∈ open_hull (to_segment x y)) (hx: x ∈ closed_hull unit_square) (hy: y ∈  closed_hull unit_square) :
x ∈ closed_hull (square_boundary_big i) ∧ y ∈ closed_hull (square_boundary_big i) := by

have hr : ∃ (r : ℝ ), 0 < r ∧ r < 1 ∧ p = (1 - r) • x + r • y := by
  rw [open_segment_interval_im, seg_vec] at hp
  simp only [Fin.isValue, Set.mem_image, Set.mem_Ioo] at hp
  obtain ⟨r, hr1, hr2⟩ := hp
  use r
  constructor
  · exact hr1.1
  constructor
  · exact hr1.2
  rw [to_segment, to_segment] at hr2
  rw [← hr2]
  module
rcases hr with ⟨r, hr1, hr2, hr3⟩
have hp1 : p 1 = (1 - r) * x 1 + r * y 1 := by
  rw [hr3]
  simp only [Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
have hp0 : p 0 = (1 - r) * x 0 + r * y 0 := by
  rw [hr3]
  simp only [Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
have hp1r : (1 -r) > 0 := by linarith
fin_cases i
· simp only [Fin.isValue, Fin.zero_eta] at *
  have hp1' : p 1 = 0 := by
    unfold square_boundary_big at hpiface
    simp at hpiface
    unfold closed_hull at hpiface
    simp at hpiface
    rcases hpiface with ⟨α, hα, hpα⟩
    rw [←hpα]
    simp
  have hx1 : x 1 = 0 := by
    by_contra hcontra
    rw [hp1'] at hp1
    have hx' : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 1
    have hy' : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 1
    have hp1'' : -(1-r) * x 1 = r  * y 1 := by
      linarith
    by_cases hx1 : x 1 = 0
    · contradiction
    · have hxpos : 0 < x 1 := by
        rcases hx' with ⟨hx'1, hx'2⟩
        by_contra hcontra
        rw [le_iff_lt_or_eq] at hx'1
        cases' hx'1 with p q
        linarith
        rw [q] at hx1
        contradiction
      have hypos : y 1 ≥ 0 := by
        apply hy'.1
      have hneg : -(1-r) * x 1 < 0 := by
        have h2 : -(1-r) < 0 := by linarith [hp1r]
        exact mul_neg_of_neg_of_pos h2 hxpos
      have hpos : r * y 1 ≥  0 := by
        exact mul_nonneg (by linarith) hypos
      have hneg' : -(1 - r) * x 1 ≥ 0 := by
        rw [hp1'']; apply hpos
      linarith
  have hy1 : y 1 = 0 := by
    rw [hp1', hx1] at hp1
    simp at hp1
    by_contra hcontra
    by_cases hrcontra : r = 0
    · linarith
    · subst hr3
      simp_all only [gt_iff_lt, sub_pos, Fin.isValue, or_self]
constructor
  · unfold square_boundary_big
    have hx' : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
        rw [closed_unit_square_eq] at hx
        apply hx 0
    simp
    have hxface : (1- x 0) • v 0 0 + x 0 • v 1 0 = x := by
    ext i
    fin_cases i
      · simp
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, add_zero]
      apply hx1.symm
  unfold closed_hull
    simp
  use fun | 0 => 1 - x 0 | 1 => x 0
  refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · simp [hx'.2]
    · simp [hx'.1]
  · simp only [Fin.isValue, Fin.sum_univ_two, sub_add_cancel]
    simp only [Fin.isValue]
    apply hxface
  · unfold square_boundary_big
    have hy' : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      apply hy 0
    simp
    have hxface : (1- y 0) • v 0 0 + y 0 • v 1 0 = y := by
    ext i
    fin_cases i
      · simp
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, add_zero]
      apply hy1.symm
  unfold closed_hull
    simp
  use fun | 0 => 1 - y 0 | 1 => y 0
  refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · simp [hy'.2]
    · simp [hy'.1]
    · simp only [Fin.isValue, Fin.sum_univ_two, sub_add_cancel]
    simp only [Fin.isValue]
    apply hxface

· simp at *
  have hp0' : p 0 = 1 := by
    unfold square_boundary_big at hpiface
    simp at hpiface
    unfold closed_hull at hpiface
    simp at hpiface
    rcases hpiface with ⟨α, hα, hpα⟩
    unfold closed_simplex at hα
    rcases hα with ⟨hα, hpα'⟩
    rw [←hpα']
    have hpα'' : α 0 • v 1 0 0 + α 1 • v 1 1 0 = p 0 := by
      exact congrArg (fun v => v 0) hpα
    simp at hpα''
    simp only [Fin.isValue, Fin.sum_univ_two]
    apply hpα''.symm
  have hx1 : x 0 = 1 := by
    have hx' : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 0
    have hy' : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 0
    by_contra hcontra
    rw [hp0'] at hp0
    have hx1' : (1-r) * x 0 <  (1-r) * 1 := by
      have h2 : (1-r) > 0 := by linarith [hp1r]
      have hx01 : x 0 < 1 := by
        rcases hx' with ⟨hx'1, hx'2⟩
        rw [le_iff_lt_or_eq] at hx'2
        by_contra hcontra'
        cases' hx'2 with p q
        contradiction
        contradiction
      exact mul_lt_mul_of_pos_left hx01 h2
    have hx1'' : 1 < (1-r) * 1 + r * y 0 := by
      linarith
    simp only [mul_one, Fin.isValue] at hx1''
    have hx1''' : 0  <  -r  + r * y 0 := by
      linarith
    have hx1'''': 0 < r * (-1 + y 0) := by
      linarith
    rw[mul_pos_iff_of_pos_left hr1] at hx1''''
    have hy0 : 1 < y 0 := by
      linarith
    rcases hy' with ⟨hy'1, hy'2⟩
    rw [le_iff_lt_or_eq] at hy'2
    cases' hy'2 with p q
    · linarith
    · linarith
  have hy1 : y 0 = 1 := by
    rw [hx1, hp0'] at hp0
    simp only [mul_one, Fin.isValue] at hp0
    have hy1' : 0 = - r + r * y 0 := by
      linarith
    have hy1'' : 0 = r * (-1 + y 0) := by
      linarith
    rw [eq_comm, mul_eq_zero] at hy1''
    rcases hy1'' with h | h
    · linarith
    · linarith
  constructor
  · unfold square_boundary_big
    have hx' : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 1
    simp
    have hxface : (1- x 1) • v 1 0 + x 1 • v 1 1 = x := by
      ext i
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, v₀_val, smul_eq_mul,
        mul_one, sub_add_cancel]
        apply hx1.symm
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, mul_one, zero_add]
    unfold closed_hull
    simp
    use fun | 0 => 1 - x 1 | 1 => x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · simp [hx'.2]
    · simp [hx'.1]
    · simp only [Fin.isValue, Fin.sum_univ_two, sub_add_cancel]
    simp only [Fin.isValue]
    apply hxface
  · unfold square_boundary_big
    have hy' : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 1
    simp
    have hxface : (1- y 1) • v 1 0 + y 1 • v 1 1 = y := by
      ext i
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, v₀_val, smul_eq_mul,
        mul_one, sub_add_cancel]
        apply hy1.symm
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, mul_one, zero_add]
    unfold closed_hull
    simp
    use fun | 0 => 1 - y 1 | 1 => y 1
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · simp [hy'.2]
    · simp [hy'.1]
    · simp only [Fin.isValue, Fin.sum_univ_two, sub_add_cancel]
    simp only [Fin.isValue]
    apply hxface

· simp at *
  have hp1' : p 1 = 1 := by
    unfold square_boundary_big at hpiface
    simp at hpiface
    unfold closed_hull at hpiface
    simp at hpiface
    rcases hpiface with ⟨α, hα, hpα⟩
    rcases hα with ⟨hα, hpα'⟩
    simp at hpα'
    rw [←hpα]
    simp only [Fin.isValue, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul, mul_one]
    apply hpα'
  have hx0 : x 1 = 1 := by
    have hx' : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 1
    have hy' : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 1
    by_contra hcontra
    rw [hp1'] at hp1
    have hx0' : (1-r) * x 1 < (1-r) * 1 := by
      have h2 : (1-r) > 0 := by linarith [hp1r]
      have hx01 : x 1 < 1 := by
        rcases hx' with ⟨hx'1, hx'2⟩
        rw [le_iff_lt_or_eq] at hx'2
        by_contra hcontra'
        cases' hx'2 with p q
        contradiction
        contradiction
      exact mul_lt_mul_of_pos_left hx01 h2
    have hx0'' : 1 < (1-r) * 1 + r * y 1 := by
      linarith
    simp only [mul_one, Fin.isValue] at hx0''
    have hx0''' : 0 < -r + r * y 1 := by
      linarith
    have hx0'''' : 0 < r * (-1 + y 1) := by
      linarith
    rw [mul_pos_iff_of_pos_left hr1] at hx0''''
    rw [le_iff_lt_or_eq] at hy'
    cases' hy' with p q
    linarith
  have hy0 : y 1 = 1 := by
    rw [hx0, hp1'] at hp1
    simp only [mul_one, Fin.isValue] at hp1
    have hy0' : 0 = - r + r * y 1 := by
      linarith
    have hy0'' : 0 = r * (-1 + y 1) := by
      linarith
    rw [eq_comm, mul_eq_zero] at hy0''
    rcases hy0'' with h | h
    · linarith
    · linarith
  constructor
  · unfold square_boundary_big
    have hx' : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 0
    simp
    have hxface : (1- x 0) • v 0 1 + x 0 • v 1 1 = x := by
      ext i
      fin_cases i
      · simp
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_one, sub_add_cancel]
        apply hx0.symm
    unfold closed_hull
    simp
    use fun | 0 => x 0 | 1 => 1 - x 0
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · linarith
    · simp
      apply hx'.2
    · simp
    simp only [Fin.isValue]
    have hxface' :  (1 - x 0) • v 0 1 + x 0 • v 1 1 =   x 0 • v 1 1 + (1 - x 0) • v 0 1  := by
      module
    rw [hxface'] at hxface
    apply hxface
  · unfold square_boundary_big
    have hy' : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 0
    simp
    have hxface : (1- y 0) • v 0 1 + y 0 • v 1 1 = y := by
      ext i
      fin_cases i
      · simp
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_one, sub_add_cancel]
        apply hy0.symm
    unfold closed_hull
    simp
    use fun | 0 => y 0 | 1 => 1 - y 0
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · linarith
    · simp
      apply hy'.2
    · simp only [Fin.isValue, Fin.sum_univ_two, add_sub_cancel]
    simp only [Fin.isValue]
    have hxface' :  (1 - y 0) • v 0 1 + y 0 • v 1 1 =   y 0 • v 1 1 + (1 - y 0) • v 0 1  := by
      module
    rw [hxface'] at hxface
    apply hxface

· simp at *
  have hp0' : p 0 = 0 := by
    unfold square_boundary_big at hpiface
    simp at hpiface
    unfold closed_hull at hpiface
    simp at hpiface
    rcases hpiface with ⟨α, hα, hpα⟩
    rcases hα with ⟨hα, hpα'⟩
    rw [←hpα]
    simp
  have hx0 : x 0 = 0 := by
    rw [hp0'] at hp0
    have hx' : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 0
    have hy' : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 0
    by_contra hcontra
    have hp0'' : -(1-r) * x 0 = r  * y 0 := by
      linarith
    by_cases hx1 : x 0 = 0
    · contradiction
    · have hxpos : 0 < x 0 := by
        rcases hx' with ⟨hx'1, hx'2⟩
        by_contra hcontra
        rw [le_iff_lt_or_eq] at hx'1
        cases' hx'1 with p q
        linarith
        rw [q] at hx1
        contradiction
      have hypos : y 0 ≥ 0 := by
        apply hy'.1
      have hneg : -(1-r) * x 0 < 0 := by
        have h2 : -(1-r) < 0 := by linarith [hp1r]
        exact mul_neg_of_neg_of_pos h2 hxpos
      have hpos : r * y 0 ≥  0 := by
        exact mul_nonneg (by linarith) hypos
      have hneg' : -(1 - r) * x 0 ≥ 0 := by
        rw [hp0'']; apply hpos
      linarith

  have hy0 : y 0 = 0 := by
    rw [hp0', hx0] at hp0
    simp at hp0
    by_contra hcontra
    by_cases hrcontra : r = 0
    · linarith
    · subst hr3
      simp_all only [gt_iff_lt, sub_pos, Fin.isValue, or_self]
  constructor
  · unfold square_boundary_big
    have hx' : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hx
      exact hx 1
    simp
    have hxface : (1- x 1) • v 0 0 + x 1 • v 0 1 = x := by
      ext i
      fin_cases i
      · simp
        apply hx0.symm
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, mul_one, zero_add]
    unfold closed_hull
    simp
    use fun | 0 => x 1 | 1 => 1 - x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · linarith
    · simp only [Fin.isValue, sub_nonneg]
      apply hx'.2
    · simp only [Fin.isValue, Fin.sum_univ_two, add_sub_cancel]
    simp only [Fin.isValue]
    have hxface' :  (1 - x 1) • v 0 0 + x 1 • v 0 1 =   x 1 • v 0 1 + (1 - x 1) • v 0 0  := by
      module
    rw [hxface'] at hxface
    apply hxface

  · unfold square_boundary_big
    have hy' : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      rw [closed_unit_square_eq] at hy
      exact hy 1
    simp
    have hxface : (1- y 1) • v 0 0 + y 1 • v 0 1 = y := by
      ext i
      fin_cases i
      · simp
        apply hy0.symm
      · simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, v₁_val, smul_eq_mul,
        mul_zero, mul_one, zero_add]
    unfold closed_hull
    simp
    use fun | 0 => y 1 | 1 => 1 - y 1
    refine ⟨⟨?_,?_⟩,?_⟩
    intro i
    fin_cases i
    · linarith
    · simp only [Fin.isValue, sub_nonneg]
      apply hy'.2
    · simp only [Fin.isValue, Fin.sum_univ_two, add_sub_cancel]
    simp only [Fin.isValue]
    have hxface' :  (1 - y 1) • v 0 0 + y 1 • v 0 1 =   y 1 • v 0 1 + (1 - y 1) • v 0 0 := by
      module
    rw [hxface'] at hxface
    apply hxface

lemma convex_faces' {x y p : ℝ²} (i : Fin 4) (hpiface : p ∈ closed_hull (square_boundary_big i))
(hp : p ∈ open_hull (to_segment x y)) (hx: x ∈ closed_hull unit_square) (hy: y ∈  closed_hull unit_square) :
closed_hull (to_segment x y) ⊆ closed_hull (square_boundary_big i) := by
  apply closed_hull_convex
  intro j
  fin_cases j
  · exact (convex_faces i hpiface hp hx hy).1
  · exact (convex_faces i hpiface hp hx hy).2

lemma convex_faces'' {p : ℝ²} { L : Segment} (i : Fin 4) (hpiface : p ∈ closed_hull (square_boundary_big i))
(hp : p ∈ open_hull L) (hx: L 0 ∈ closed_hull unit_square) (hy: L 1 ∈  closed_hull unit_square) :
closed_hull L ⊆ closed_hull (square_boundary_big i) := by
  apply closed_hull_convex
  intro j
  fin_cases j
  · exact (convex_faces i hpiface hp hx hy).1
  · exact (convex_faces i hpiface hp hx hy).2


lemma bottom_face_convex {x y p : ℝ²} (hpface : p ∈  closed_hull bottom_face) (hp : p ∈ open_hull (to_segment x y))
 (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) : x ∈ closed_hull bottom_face ∧
y ∈ closed_hull bottom_face := by sorry

lemma bottom_face_convex₂ {x y p : ℝ²} (hpface : p ∈  closed_hull bottom_face) (hp : p ∈ open_hull (to_segment x y))
  (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) :
  closed_hull (to_segment x y) ⊆ closed_hull bottom_face := by sorry

lemma left_face_convex {x y p : ℝ²} (hpface : p ∈  closed_hull left_face) (hp : p ∈ open_hull (to_segment x y))
 (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) : x ∈ closed_hull left_face ∧
y ∈ closed_hull left_face := by sorry

lemma left_face_convex₂ {x y p : ℝ²} (hpface : p ∈  closed_hull left_face) (hp : p ∈ open_hull (to_segment x y))
  (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) :
  closed_hull (to_segment x y) ⊆ closed_hull left_face := by sorry

lemma right_face_convex {x y p : ℝ²} (hpface : p ∈  closed_hull right_face) (hp : p ∈ open_hull (to_segment x y))
 (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) : x ∈ closed_hull right_face ∧
y ∈ closed_hull right_face := by sorry

lemma right_face_convex₂ {x y p : ℝ²} (hpface : p ∈  closed_hull right_face) (hp : p ∈ open_hull (to_segment x y))
  (hx: x ∈ closed_hull unit_square) (hy : y ∈ closed_hull unit_square) :
  closed_hull (to_segment x y) ⊆ closed_hull right_face := by sorry


-- lemma boundary_description : boundary unit_square = { x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∃ i, x i = 0 ∨ x i = 1)} := by
--   unfold boundary
--   rw[closed_unit_square_eq, open_unit_square_eq]
--   ext x
--   simp only [Set.mem_diff, Set.mem_setOf_eq, not_forall, not_and, not_lt, and_congr_right_iff]
--   intro h
--   constructor
--   · rintro ⟨ i, h1⟩
--     use i
--     by_cases h2: x i = 0
--     · left; exact h2
--     · right; exact le_antisymm (h i).2 (h1 (lt_of_le_of_ne (h i).1 fun a ↦ h2 (id (Eq.symm a))))
--   · rintro ⟨ i, (h1|h1)⟩
--     · use i; intro h2; exfalso; exact (ne_of_lt h2 h1.symm)
--     · use i; intro _; exact le_of_eq h1.symm

lemma closed_unit_square_eq_weak (x : ℝ²): x ∈ closed_hull unit_square → (∀ i, 0 ≤ x i ∧ x i ≤ 1):= by
  rw[closed_unit_square_eq]
  exact (fun h ↦ h)

lemma boundary_union_of_faces : closed_hull top_face ∪ closed_hull bottom_face ∪
closed_hull left_face ∪ closed_hull right_face = boundary unit_square := by
  unfold top_face bottom_face left_face right_face
  rw[boundary_unit_square_eq]
  ext x
  constructor
  --Because of the definition of these faces, I think it is difficult not to do a lot of case distinctions
  · rintro (((h|h)|h)|h)
    --The proofs consist firstly on showing that for any element is between 0 and 1, I wanted to use the convexity of polynomials, but it was too much hassle to match the numbers
    --The second part is pretty streamlined in terms of efficiency I think
    · rcases h with ⟨a , ha, hx⟩
      have ha1 := simplex_co_leq_1 ha
      rcases ha with ⟨ha2, ha3⟩; simp only [Fin.sum_univ_two, Fin.isValue] at ha3
      rw[← hx]
      constructor
      · intro i; fin_cases i <;> simp[ha1, ha2, ha3]
      · use 1; right
        simp[ha3]
    · rcases h with ⟨a , ha, hx⟩
      have ha1 := simplex_co_leq_1 ha
      rcases ha with ⟨ha2, ha3⟩; simp only [Fin.sum_univ_two, Fin.isValue] at ha3
      rw[← hx]
      constructor
      · intro i; fin_cases i <;> simp[ha1, ha2, ha3]
      · use 1; left
        simp[ha3]
    · rcases h with ⟨a , ha, hx⟩
      have ha1 := simplex_co_leq_1 ha
      rcases ha with ⟨ha2, ha3⟩; simp only [Fin.sum_univ_two, Fin.isValue] at ha3
      rw[← hx]
      constructor
      · intro i; fin_cases i <;> simp[ha1, ha2, ha3]
      · use 0; left
        simp[ha3]
    · rcases h with ⟨a , ha, hx⟩
      have ha1 := simplex_co_leq_1 ha
      rcases ha with ⟨ha2, ha3⟩; simp only [Fin.sum_univ_two, Fin.isValue] at ha3
      rw[← hx]
      constructor
      · intro i; fin_cases i <;> simp[ha1, ha2, ha3]
      · use 0; right
        simp[ha3]
  · rintro ⟨ h, ⟨ i, (h1|h1)⟩⟩ <;> have h2 :∀ (i: Fin 2), 0 ≤ (1- x i) ∧ (1- x i) ≤ 1 := (fun i ↦ ⟨by linarith[h i], by linarith[h i]⟩ )  <;> fin_cases i
    · left; right
      refine ⟨ real_to_fin_2 (x 1), real_to_fin_2_closed (h 1).1 (h 1).2 ,?_⟩
      dsimp at h1
      simp only [real_to_fin_2, Fin.isValue, Fin.sum_univ_two] ; ext i ; fin_cases i<;> simp[h1]
    · left; left; right
      refine ⟨ real_to_fin_2 (1- x 0), real_to_fin_2_closed (h2 0).1 (h2 0).2 ,?_⟩
      dsimp at h1
      simp only [real_to_fin_2, Fin.isValue, Fin.sum_univ_two] ; ext i ; fin_cases i<;> simp[h1]
    · right
      refine ⟨ real_to_fin_2 (1 - x 1), real_to_fin_2_closed (h2 1).1 (h2 1).2 ,?_⟩
      dsimp at h1
      simp only [real_to_fin_2, Fin.isValue, Fin.sum_univ_two] ; ext i ; fin_cases i<;> simp[h1]
    · left; left; left
      refine ⟨ real_to_fin_2 (1-x 0), real_to_fin_2_closed (h2 0).1 (h2 0).2 ,?_⟩
      dsimp at h1
      simp only [real_to_fin_2, Fin.isValue, Fin.sum_univ_two] ; ext i ; fin_cases i<;> simp[h1]

lemma boundary_union_of_faces' : ⋃ i : Fin 4, closed_hull (square_boundary_big i) = boundary unit_square
:= by exact square_boundary_is_union_sides.symm

lemma line_in_boundary {x : ℝ²} {L : Segment} (hL: closed_hull L ⊆ closed_hull unit_square)
(hboundary: x ∈ open_hull L ∩ boundary unit_square) : closed_hull L ⊆ boundary unit_square := by

rw [← boundary_union_of_faces'] at hboundary
by_cases hbound : x ∈ closed_hull (square_boundary_big 0) ∨ x ∈ closed_hull (square_boundary_big 1) ∨
  x ∈ closed_hull (square_boundary_big 2) ∨ x ∈ closed_hull (square_boundary_big 3)

rcases hbound with hbound0 | hbound1 | hbound2 | hbound3

· have hL0 : closed_hull L ⊆ closed_hull (square_boundary_big 0) := by
    apply convex_faces' 0 hbound0 hboundary.1
    apply hL
    apply corner_in_closed_hull
    apply hL
    apply corner_in_closed_hull
  have hbound' : closed_hull (square_boundary_big 0) ⊆ boundary unit_square := by
    rw [← boundary_union_of_faces']
    intro x hx
    simp only [Set.mem_iUnion]
    use 0
  exact subset_trans hL0 hbound'

· have hL1 : closed_hull L ⊆ closed_hull (square_boundary_big 1) := by
    apply convex_faces' 1 hbound1 hboundary.1
    apply hL
    apply corner_in_closed_hull
    apply hL
    apply corner_in_closed_hull
  have hbound' : closed_hull (square_boundary_big 1) ⊆ boundary unit_square := by
    rw [← boundary_union_of_faces']
    intro x hx
    simp only [Set.mem_iUnion]
    use 1
  exact subset_trans hL1 hbound'

· have hL2 : closed_hull L ⊆ closed_hull (square_boundary_big 2) := by
    apply convex_faces' 2 hbound2 hboundary.1
    apply hL
    apply corner_in_closed_hull
    apply hL
    apply corner_in_closed_hull
  have hbound' : closed_hull (square_boundary_big 2) ⊆ boundary unit_square := by
    rw [← boundary_union_of_faces']
    intro x hx
    simp only [Set.mem_iUnion]
    use 2
  exact subset_trans hL2 hbound'

· have hL3 : closed_hull L ⊆ closed_hull (square_boundary_big 3) := by
    apply convex_faces' 3 hbound3 hboundary.1
    apply hL
    apply corner_in_closed_hull
    apply hL
    apply corner_in_closed_hull
  have hbound' : closed_hull (square_boundary_big 3) ⊆ boundary unit_square := by
    rw [← boundary_union_of_faces']
    intro x hx
    simp only [Set.mem_iUnion]
    use 3
  exact subset_trans hL3 hbound'

simp_all only [Set.mem_inter_iff, Set.mem_iUnion, not_or]
rcases hboundary with ⟨hx, hy⟩
rcases hy with ⟨i, h1⟩
fin_cases i
· simp_all only [Fin.zero_eta]
· simp_all only [Fin.mk_one]
· simp_all
· simp_all


lemma unit_square_is_convex {x y : ℝ²} (hx : x ∈ closed_hull unit_square) (hy : y ∈ closed_hull
unit_square) : closed_hull (to_segment x y) ⊆ closed_hull unit_square := by
  have h: ∀ i, to_segment x y i ∈ closed_hull unit_square
  · intro i; fin_cases i
    exact hx; exact hy
  apply closed_hull_convex h

lemma unit_square_is_convex' {S : Segment} (hS : closed_hull S ⊆ boundary unit_square) :
    ∃ i : Fin 4, closed_hull S ⊆ closed_hull (square_boundary_big i) := by
  have hSi : ∀ i, S i ∈ closed_hull unit_square := (fun i↦ boundary_in_closed (hS corner_in_closed_hull))
  rw[← boundary_union_of_faces'] at hS
  rcases open_seg_nonempty S with ⟨ x, h⟩
  rcases hS (open_sub_closed S h) with ⟨ y, ⟨⟨i,h1 ⟩ , h2  ⟩⟩
  rw[← h1] at h2
  exact ⟨ i, convex_faces'' i h2 h (hSi 0) (hSi 1)⟩

lemma unit_square_is_convex_open {S : Segment} (hS : closed_hull S ⊆ boundary unit_square)
    (hNondegen : S 0 ≠ S 1) :
    ∃ i : Fin 4, open_hull S ⊆ open_hull (square_boundary_big i) := by
  apply unit_square_is_convex' at hS
  rcases hS with ⟨ i, hS⟩
  exact ⟨ i, open_segment_sub' hS hNondegen⟩

lemma square_boundary_segments_in_boundary : ∀ i : Fin 4, closed_hull (square_boundary_big i) ⊆
    boundary unit_square := by
  rw[← boundary_union_of_faces]
  intro i; fin_cases i <;> dsimp
  · apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_right
    exact Eq.subset (congrArg closed_hull rfl)
  · apply Set.subset_union_of_subset_right
    exact Eq.subset (congrArg closed_hull rfl)
  · apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_left
    have h1: square_boundary_big 2 = reverse_segment top_face := by rfl
    rw[h1,reverse_segment_closed_hull ]
  · apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_right
    exact Eq.subset (congrArg closed_hull rfl)
