import Mathlib
import FormalBook.sperner.simplex_basic
import FormalBook.sperner.segment_triangle
import FormalBook.sperner.basic_definitions
import FormalBook.sperner.Rainbow_triangles
import FormalBook.sperner.square


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


inductive Chain : ℝ² → ℝ² → Type
    | basic {u v : ℝ²}  : Chain u v
    | join {u v w : ℝ²} (hCollineair : colin u v w) (C : Chain v w) : Chain u w

noncomputable def to_basic_segments {u v : ℝ²} : Chain u v → Finset Segment
    | Chain.basic              => {to_segment u v}
    | @Chain.join _ w _ _ C    => to_basic_segments C ∪ {to_segment u w}

noncomputable def glue_chains {u v w : ℝ²} (hCollinear : colin u v w) : Chain u v → Chain v w → Chain u w
    | Chain.basic, C      => Chain.join hCollinear C
    | Chain.join h C', C  => Chain.join ⟨hCollinear.1, interior_left_trans h.2 hCollinear.2⟩ (glue_chains (sub_collinear_right hCollinear h.2) C' C)

noncomputable def reverse_chain {u v : ℝ²} : Chain u v → Chain v u
    | Chain.basic           => Chain.basic
    | @Chain.join _ x _ h C => glue_chains (colin_reverse h) (reverse_chain C) (@Chain.basic x u)

noncomputable def chain_to_big_segment {u v : ℝ²} (_ : Chain u v) : Segment := to_segment u v


lemma chain_to_big_segment_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w) : chain_to_big_segment (glue_chains h CL CR) = to_segment u w := by

  sorry

lemma basic_segments_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : reverse_chain (glue_chains h CL CR)
    = glue_chains (colin_reverse h) (reverse_chain CR) (reverse_chain CL) := by

  sorry

lemma reverse_chain_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : to_basic_segments (glue_chains h CL CR) = to_basic_segments CL ∪ to_basic_segments CR := by

  sorry



lemma segment_set_vertex {X : Finset ℝ²} {S : Segment}
  (hS : S ∈ segment_set X) : ∀ i, S i ∈ X := by
  simp only [segment_set, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨a, b, ⟨⟨⟨ha,hb⟩ ,h₁⟩,h₂⟩⟩ := hS
  rw [←h₂]
  intro i; fin_cases i <;> (simp [to_segment]; assumption)

lemma avoiding_segment_set_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) : S ∈ segment_set X :=
  mem_of_mem_filter S hS

lemma basic_avoiding_segment_set_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basic_avoiding_segment_set X A) : S ∈ segment_set X :=
  avoiding_segment_set_sub (A := A) (mem_of_mem_filter S hS)

lemma segment_set_vertex_distinct {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ segment_set X) : S 0 ≠ S 1 := by
  simp only [segment_set, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨_, _, ⟨⟨_,_⟩ ,h₂⟩⟩ := hS
  rw [←h₂]
  simpa [to_segment]

lemma basic_avoiding_segment_set_reverse {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basic_avoiding_segment_set X A)
    : reverse_segment S ∈ basic_avoiding_segment_set X A := by
  sorry

lemma avoiding_segment_set_sub_left {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ open_hull S)
    : to_segment (S 0) x ∈ avoiding_segment_set X A := by
  sorry

lemma avoiding_segment_set_sub_right {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ open_hull S)
    : to_segment x (S 1) ∈ avoiding_segment_set X A := by
  sorry



theorem segment_decomposition (A : Set ℝ²) (X : Finset ℝ²) {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) :
    ∃ (C : Chain (S 0) (S 1)),
    S = chain_to_big_segment C ∧
    (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
    = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by
  --let PX : Finset ℝ² := Finset.filter (fun p ↦ p ∈ open_hull S) X
  have hn : ∀ n, ∀ S, (Finset.filter (fun p ↦ p ∈ open_hull S) X ).card = n →
    S ∈ avoiding_segment_set X A → ∃ (C : Chain (S 0) (S 1)),
    S = chain_to_big_segment C ∧
    (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
    = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro N hm S Scard hS
    have hSboundary := boundary_seg (segment_set_vertex_distinct (avoiding_segment_set_sub hS))
    by_cases hN : N = 0
    · use @Chain.basic (S 0) (S 1)
      simp only [chain_to_big_segment, Fin.isValue, segment_rfl,
        to_basic_segments, reverse_chain, true_and]
      simp [hN, filter_eq_empty_iff] at Scard
      ext L
      simp only [mem_filter, Fin.isValue, mem_union, mem_singleton]
      constructor
      · intro ⟨hL, hLS⟩
        have hLi : ∀ i, L i ∈ boundary S := by
          intro i
          simp only [boundary, Set.mem_diff]
          refine ⟨hLS (corner_in_closed_hull),?_⟩
          apply Scard
          exact segment_set_vertex (basic_avoiding_segment_set_sub hL) i
        have hLdif := segment_set_vertex_distinct (basic_avoiding_segment_set_sub hL)
        simp [hSboundary] at hLi
        have ⟨i₀, hL₀⟩ := hLi 0
        have ⟨i₁, hL₁⟩ := hLi 1
        rw [←hL₀, ←hL₁] at hLdif
        have hi₀₁ : i₁ = (fun | 0 => 1 | 1 => 0) i₀  := by
          fin_cases i₀ <;> fin_cases i₁ <;> simp_all
        rw [hi₀₁] at hL₁
        fin_cases i₀
        · left
          exact List.ofFn_inj.mp (by simp [←hL₁, ←hL₀])
        · right
          exact List.ofFn_inj.mp (by simp [to_segment, ←hL₁, ←hL₀])
      · rintro (hL | hL) <;> rw [hL]
        · refine ⟨?_, fun _ a ↦ a⟩
          simp only [basic_avoiding_segment_set, mem_filter]
          exact ⟨hS,Scard⟩
        · rw [←reverse_segment]
          refine ⟨?_, by rw [reverse_segment_closed_hull]⟩
          apply basic_avoiding_segment_set_reverse
          simp only [basic_avoiding_segment_set, mem_filter]
          exact ⟨hS,Scard⟩
    · have hEl : Finset.Nonempty (filter (fun p ↦ p ∈ open_hull S) X) := by
        rw [← Finset.card_pos, Scard]
        exact Nat.zero_lt_of_ne_zero hN
      have ⟨x, hx⟩ := hEl
      let Sleft := to_segment (S 0) x
      let Sright := to_segment x (S 1)
      have hSlefti : ∀ i, Sleft i ∈ closed_hull S := by
        rw [mem_filter] at hx
        intro i; fin_cases i
        · convert (corner_in_closed_hull (i := 0) (P := S)) using 1
        · convert open_sub_closed _ hx.2
      have hSrighti : ∀ i, Sright i ∈ closed_hull S := by
        rw [mem_filter] at hx
        intro i; fin_cases i
        · convert open_sub_closed _ hx.2
        · convert (corner_in_closed_hull (i := 1) (P := S)) using 1
      have hcolin : colin (S 0) x (S 1) := by
        rw [mem_filter] at hx
        exact ⟨segment_set_vertex_distinct (avoiding_segment_set_sub hS), hx.2⟩
      have Sleftcard : (filter (fun p ↦ p ∈ open_hull Sleft) X).card < N := by
        rw [←Scard]
        refine card_lt_card ⟨?_,?_⟩
        · intro t ht
          simp only [mem_filter] at *
          refine ⟨ht.1, (open_segment_sub hSlefti ?_) ht.2⟩
          convert (middle_not_boundary_colin hcolin).1 using 1
        · rw [@not_subset]
          use x, hx
          intro hcontra
          rw [mem_filter] at hcontra
          refine (boundary_not_in_open ?_) hcontra.2

          sorry
      have Srightcard : (filter (fun p ↦ p ∈ open_hull Sright) X).card < N :=
        sorry
      rw [mem_filter] at hx
      have ⟨CL,hSCL,hLSegUnion⟩ :=
        hm (filter (fun p ↦ p ∈ open_hull Sleft) X).card Sleftcard Sleft rfl
        (avoiding_segment_set_sub_left hS hx.1 hx.2)
      have ⟨CR,hSCR,hRSegUnion⟩ :=
        hm (filter (fun p ↦ p ∈ open_hull Sright) X).card Srightcard Sright rfl
        (avoiding_segment_set_sub_right hS hx.1 hx.2)
      use glue_chains hcolin CL CR
      have haux_set {A₁ A₂ A₃ A₄ : Finset (Fin 2 → ℝ²)}
        : (A₁ ∪ A₃) ∪ (A₄ ∪ A₂) = (A₁ ∪ A₂) ∪ (A₃ ∪ A₄) := by
        sorry
      simp only [chain_to_big_segment_glue, segment_rfl, reverse_chain_glue,
          basic_segments_glue, true_and, haux_set,
          ←hLSegUnion, ←hRSegUnion]
      ext L
      simp [basic_avoiding_segment_set]
      constructor
      · intro ⟨h , hLS⟩
        -- Split wether L ⊆ Sleft or L ⊆ Sright
        cases' colin_sub hcolin (by convert hLS; exact segment_rfl) (h.2 x hx.1) with hLleft hLright
        · left
          exact ⟨h,hLleft⟩
        · right
          exact ⟨h,hLright⟩
      · rintro (hL | hR)
        · refine ⟨hL.1, subset_trans hL.2 (closed_hull_convex hSlefti)⟩
        · refine ⟨hR.1, subset_trans hR.2 (closed_hull_convex hSrighti)⟩
  exact hn (Finset.filter (fun p ↦ p ∈ open_hull S) X ).card _ (rfl) hS



def color : ℝ² → Fin 3 := sorry -- can use the construction using valuations here

def red : Fin 3 := 0
def blue : Fin 3 := 1
def green : Fin 3 := 2


-- The following function determines whether a segment is purple. We want to sum the value
-- of this function over all segments, so we let it take values in ℕ
noncomputable def isPurple : Segment → ℕ :=
    fun S ↦ if ( (color (S 0) = red ∧ color (S 1) = blue) ∨ (color (S 0) = blue ∧ color (S 1) = red)) then 1 else 0

noncomputable def isRainbow : Triangle → ℕ :=
    fun T ↦ if (Function.Surjective (color ∘ T)) then 1 else 0

-- The segment covered by a chain is purple if and only if an odd number of its basic
-- segments are purple.
lemma purple_parity {u v : ℝ²} (C : Chain u v) : ∑ T ∈ to_basic_segments C, isPurple T % 2
    = isPurple (chain_to_big_segment C) := by
  sorry -- can probably be proven by induction


noncomputable def triangulation_points (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ {T 0, T 1, T 2})

noncomputable def triangulation_points₂ (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ (Finset.image (fun i ↦ T i) Finset.univ))

-- The union of the interiors of the triangles of a triangulation
noncomputable def triangulation_avoiding_set (Δ : Finset Triangle) : Set ℝ² :=
    ⋃ (T ∈ Δ), open_hull T

noncomputable def triangulation_basic_segments (Δ : Finset Triangle) : Finset Segment :=
  basic_avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

noncomputable def triangulation_all_segments (Δ : Finset Triangle) : Finset Segment :=
  avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

noncomputable def purple_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (S ∈ triangulation_basic_segments Δ), isPurple S

noncomputable def rainbow_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (T ∈ Δ), isRainbow T

noncomputable def rainbow_triangles (Δ : Finset Triangle) : Finset Triangle :=
  {T ∈ Δ | isRainbow T = 1}

noncomputable def is_triangulation (Δ : Finset Triangle) : Prop :=
  is_cover {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} Δ.toSet


theorem segment_sum_odd (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    purple_sum Δ % 4 = 2 := by
  sorry


theorem segment_sum_rainbow_triangle (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    rainbow_sum Δ = 2 * (rainbow_triangles Δ).card := by
  sorry


theorem rainbow_sum_is_purple_sum (Δ : Finset Triangle) : rainbow_sum Δ = purple_sum Δ := by
  sorry --


theorem monsky_rainbow (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    ∃ T ∈ Δ, isRainbow T = 1 := by
  sorry -- easy, follows from above


-- Old stuff from Lenny
/- section noncomputable

def color : ℝ² → Fin 3 := sorry

def red : Fin 3 := 0
def blue : Fin 3 := 1
def green : Fin 3 := 2

lemma no_three_colors_on_a_line (L : Segment) :
    ∃ i : Fin 3, ∀ P ∈ closed_hull L, color P ≠ i := sorry

lemma color00 : color (v 0 0) = red := sorry
lemma color01 : color (v 0 1) = blue := sorry
lemma color10 : color (v 1 0) = green := sorry
lemma color11 : color (v 1 1) = blue := sorry


/-
  Define incidence relation between segments and triangles
-/

def side (T : Triangle) (i : Fin 3) : Segment :=
  fun | 0 => T ((i + 1) % 3) | 1 => T ((i - 1) % 3)

def segment_on_side (L : Segment) (T : Triangle)  : Prop :=
  ∃ i : Fin 3, closed_hull L ⊆ closed_hull (side T i)


/-
  A segment is purple if it runs from 0 to 1 or 1 to 0
-/

def IsPurple (L : Segment) : Prop :=
  (color (L 0) = red ∧ color (L 1) = blue) ∨ (color (L 0) = blue ∧ color (L 1) = red)


/-
  Parity of number of purple basic segments on a segment
-/

noncomputable def purple_segments (X : SegmentSet) (L : Segment) :=
  {S ∈ X | IsPurple S ∧ closed_hull S ⊆ closed_hull L}

lemma purple_segments_parity (X : SegmentSet) (hX : complete_segment_set X)
  (L : X) (hL : IsPurple L) :
  (purple_segments X L.val).card % 2 = 1 := sorry

lemma grey_segments_parity (X : SegmentSet) (hX : complete_segment_set X)
  (L : X) (hL : ¬ IsPurple L) :
  (purple_segments X L.val).card % 2 = 0 := sorry



/-
  Now we assume given a dissection S. Write X for the set of all segments in the dissection
-/

variable (S : Finset Triangle) (hS : is_cover unit_square S)

def X : SegmentSet := sorry
lemma hX : complete_segment_set X := sorry
def B := {  L : X | basis_segment X L }

/-
  For any triangle in the dissection, the number of purple segments on its boundary
  is odd iff the triangle is rainbow
  TODO: probably should be 2 mod 4, given that segments are counted with
  both orientations
-/

def IsRainbow (T : Triangle) : Prop := Function.Surjective (color ∘ T)

lemma purple_odd_iff_rainbow (T : S) :
  (purple_segments X (side T 0)).card + (purple_segments X (side T 1)).card +
  (purple_segments X (side T 2)).card % 2 = 1 ↔ IsRainbow T := sorry


/-
  Main goal for our group:
-/

theorem monsky_rainbow  :
    ∃ T ∈ S, IsRainbow T := sorry
-/
