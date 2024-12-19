
--This stuff is copy pasted from another file so I don't have rewrite definitions
import Mathlib
-- import Mathlib.Tactic
-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Order.Defs
-- import Mathlib.Data.Real.Sign
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

lemma closed_simplex_def (n : ℕ ): (closed_simplex n) = {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1} := by rfl
lemma open_simplex_def (n : ℕ ): (open_simplex n) = {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1} := by rfl

def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n

lemma closed_hull_def {n : ℕ} (f : Fin n → ℝ²) : closed_hull f = (fun α ↦ ∑ i, α i • f i) '' closed_simplex n := by rfl
lemma open_hull_def {n : ℕ} (f : Fin n → ℝ²) : open_hull f = (fun α ↦ ∑ i, α i • f i) '' open_simplex n := by rfl

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
a line of measure zero (this is outdated now).

Let us first show that we if we apply a linear transformation to a polygon, the volume will
be the absolute value of the determeninant times the original volume. -/



def unit_triangle : Triangle := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def unit_segment : Segment := fun | 0 => (v 0 0) | 1 => (v 1 0)
lemma unit_triangle_def : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl
lemma unit_segment_def : unit_segment = fun | 0 => (v 0 0) | 1 => (v 1 0)  := by rfl

def open_unit_triangle := open_hull unit_triangle
def closed_unit_triangle := closed_hull unit_triangle

--first the statement that for a polygon P and a linear map L,  L( open hull P) = open hull (L P),
--starting with an elementary used to prove it

lemma lincom_commutes ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ}(a : Fin n → ℝ)(f : Fin n → ℝ²): ∑ i : Fin n, a i • L (f i)  =L (∑ i : Fin n, (a i) • (f i)) := by
  rw[  map_sum L (fun i ↦  a i • f i) univ]
  apply Fintype.sum_congr
  exact fun i ↦ Eq.symm (LinearMap.CompatibleSMul.map_smul L (a i) (f i))


theorem open_hull_lin_trans ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ }(f : (Fin n → ℝ²)) : open_hull (L ∘ f ) = Set.image L (open_hull f) := by
  rw[open_hull_def, open_hull_def, ← Set.image_comp] -- for some reason repeat rw does not work here
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (⇑L ∘ fun a ↦ ∑ i : Fin n, a i • f i) a = L  (∑ i : Fin n, a i • f i) :=by rfl
      rw[ h3, ← lincom_commutes L a f, h2]
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (fun α ↦ ∑ i : Fin n, α i • (⇑L ∘ f) i) a =  (∑ i : Fin n, a i • L (f i)) := by rfl
      rw[ h3, lincom_commutes L a f, h2]

--Now do something similar for translations (I really hope this matches with Leans stuff)
def translation (a : ℝ²) : (ℝ² → ℝ²) := fun x ↦ x + a

theorem aux_for_translation {n : ℕ }{f: Fin n → ℝ²}{a : Fin n → ℝ }{b : ℝ² }(h1 : a ∈ open_simplex n):   ∑ i : Fin n, a i • (f i + b) =  ∑ i : Fin n, a i • f i + b := by
  rcases h1 with ⟨_, h3⟩
  have h4: b = ∑ i : Fin n, a i • b
  rw[← sum_smul, h3, one_smul]
  nth_rewrite 2 [h4]
  rw[← sum_add_distrib]
  apply Fintype.sum_congr
  exact fun i ↦ DistribSMul.smul_add (a i) (f i) b


--Most of the proof now gets copied
theorem translation_commutes {n : ℕ }(f : (Fin n → ℝ²)) (b : ℝ²) : open_hull ( (translation b) ∘ f) = Set.image (translation b) (open_hull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  rw[open_hull_def, open_hull_def, ← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[← aux_for_translation h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[ aux_for_translation h1]⟩

--These maps tell us hows to transform from the unit triangle to the an arbitrary triangle
def matrix_transform ( T : Triangle) : Matrix (Fin 2) (Fin 2) ℝ :=![ ![T 1 0 - T 0 0, T 2 0 - T 0 0], ![T 1 1 - T 0 1, T 2 1 - T 0 1]]
def linear_transform (T : Triangle) := Matrix.toLin' (matrix_transform T)
def triangle_translation (T : Triangle) := translation (T 0)

--This theorem tells us that these maps indeed do the trick, combined with translation_commutes and open_hull_lin_trans
theorem unit_triangle_to_triangle (T : Triangle): Set.image (triangle_translation T) (Set.image (linear_transform T) (open_hull unit_triangle)) = open_hull T:= by
  have h1 : triangle_translation T = translation (T 0) := by rfl
  let f : (Fin 3 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
  have hunit_triangle : unit_triangle = f :=by rfl
  rw[hunit_triangle, h1]
  have h2 : open_hull (linear_transform T ∘ f )= ⇑(linear_transform T) '' open_hull f
  exact open_hull_lin_trans (linear_transform T) f
  rw[← h2]
  --rw[← open_hull_lin_trans (linear_transform T) f] Why doesnt this work!??
  rw[← translation_commutes]
  apply congrArg
  --This part of the proof says that the linear transformation and translation of the unit triangle give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;> simp[translation,linear_transform, f, matrix_transform, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail  ]

theorem area_lin_map ( L : ℝ² →ₗ[ℝ ]  ℝ²) (A : Set ℝ²) : MeasureTheory.volume (Set.image L A) = (ENNReal.ofReal (abs ( LinearMap.det L ))) * (MeasureTheory.volume (A)) := by
  exact MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume L A


--This is some garbage that is not working yet (I want it to be like the above)
 theorem area_translation (a : ℝ²)(A : Set ℝ²) :  MeasureTheory.volume (Set.image (fun x ↦ a + x ) A) = MeasureTheory.volume (A) :=   by sorry
  -- MeasureTheory.volume.IsAddLeftInvariant
--   sorry
-- variable (a b : (Fin 2) → ℝ)(G : Type) [AddGroup G] [TopologicalSpace G] [TopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]  (K₀ : TopologicalSpace.PositiveCompacts G)
-- #check MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure K₀
--#check map_add_left_eq_self

-- This is what we want to prove
theorem volume_open_unit_triangle : (MeasureTheory.volume open_unit_triangle).toReal = (1/2 : ℝ ) := by sorry



theorem volume_open_triangle ( T : Triangle ) : (MeasureTheory.volume (open_hull T)).toReal = triangle_area (T : Triangle) := by
  sorry

def point0 : (Fin 2 → ℝ ) := fun | 0 => 0 | 1 => 0
def point1 : (Fin 2 → ℝ ) := fun | 0 => 1 | 1 => 0

theorem closed_unit_segment_is_box : (closed_hull unit_segment) = Set.Icc point0 point1 := by
  have hunit_segment : unit_segment = fun | 0 => (v 0 0) | 1 => (v 1 0) := by rfl
  have hp0 : point0 = fun | 0 => 0 | 1 => 0 := by rfl
  have hp1 : point1 = fun | 0 => 1 | 1 => 0 := by rfl
  ext x
  constructor
  · rintro ⟨ a ,⟨ h1,h3⟩  , h2⟩
    rw[hunit_segment] at h2
    simp at *
    rw[← h2]
    constructor
    · intro i
      rw[hp0]
      fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
    · intro i -- this part is directly copied except there is hp1 instead of hp0
      rw[hp1]
      fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
  · rintro ⟨ h1, h2⟩
    use (fun | 0 =>  (1 - x 0) | 1 => x 0)
    rw[hp0,hp1] at *
    dsimp at *
    constructor
    · specialize h1 0
      specialize h2 0
      dsimp at *
      constructor
      · intro i
        fin_cases i <;> dsimp <;> linarith[h1, h1]
      · simp
    · ext i
      rw[hunit_segment]
      fin_cases i
      · simp
      · simp
        specialize h1 1
        specialize h2 1
        dsimp at *
        linarith



--#check MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))
--#check EuclideanSpace.volume_preserving_measurableEquiv
--#check Set.Icc point0 point1

theorem volume_closed_unit_segment : (MeasureTheory.volume (closed_hull unit_segment)).toReal = 0 := by
  -- This first part is essentially showing 0 = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
  have h0 : ∏ i : (Fin 2), (point1 i - point0 i) = 0
  rw[ Fin.prod_univ_two]
  unfold point0 point1
  linarith
  rw[ ← h0]
  have h1: point0 ≤ point1
  intro i
  fin_cases i <;> dsimp <;> rw[ point0, point1] ; linarith
  rw[ ← Real.volume_Icc_pi_toReal h1]
  -- Now I try to show (MeasureTheory.volume (closed_hull unit_segment)).toReal = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
  -- But the left-hand side Measuretheory.volume is not the same as the right-hand side
  have h2 : MeasureTheory.Measure.map (⇑(EuclideanSpace.measurableEquiv (Fin 2))) MeasureTheory.volume  (Set.Icc point0 point1) = MeasureTheory.volume (Set.Icc point0 point1)
  rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]
  rw[ ← h2]
  rw[ closed_unit_segment_is_box] --This is the theorem stating closed_hull unit_segment = Set.Icc point0 point1
  sorry
  --rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]





theorem volume_closed_segment (L : Segment) : (MeasureTheory.volume (closed_hull L)).toReal = 0 := by
  sorry

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




theorem open_unit_square1_is_union : open_unit_square1 = union_of_open_triangles ∪  open_diagonal_line := by
  have hunit : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl
  have hdiag : diagonal_line = fun | 0 => (v 1 0) | 1 => (v 0 1) := by rfl
  have hflipunit: flip_unit_triangle = fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0) := by rfl
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
      use (fun | 0 => (x 0 + x 1 -1) | 1 => 1 - x 0 | 2 => 1- x 1)
      constructor
      · constructor
        · dsimp
          intro i
          fin_cases i <;> dsimp <;> linarith
        · rw[Fin.sum_univ_three]
          dsimp
          linarith
      · dsimp
        rw[Fin.sum_univ_three, hflipunit]
        simp
        ext i
        fin_cases i <;> simp
  · intro h
    cases' h  with h1 h2
    cases' h1 with h1 h3
    · rcases h1 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
      rw[← h6]
      dsimp
      rw[Fin.sum_univ_three,hunit] at *
      dsimp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
    · rcases h3 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
      rw[← h6]
      dsimp
      rw[Fin.sum_univ_three,hflipunit] at *
      dsimp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
    · rcases h2 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
      rw[← h6]
      dsimp
      rw[Fin.sum_univ_two,hdiag] at *
      dsimp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]




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
  · sorry



theorem open_square_union_of : open_unit_square = union_of_open_triangles ∪  open_diagonal_line := by
  rw[ open_unit_squares_are_same]
  exact open_unit_square1_is_union
