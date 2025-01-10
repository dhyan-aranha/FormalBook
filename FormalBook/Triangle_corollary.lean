
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

--def open_unit_triangle := open_hull unit_triangle
--def closed_unit_triangle := closed_hull unit_triangle

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

theorem closed_hull_lin_trans ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ }(f : (Fin n → ℝ²)) : closed_hull (L ∘ f ) = Set.image L (closed_hull f) := by
  rw[closed_hull_def, closed_hull_def, ← Set.image_comp] -- for some reason repeat rw does not work here
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

theorem aux_for_translation_closed {n : ℕ }{f: Fin n → ℝ²}{a : Fin n → ℝ }{b : ℝ² }(h1 : a ∈ closed_simplex n):   ∑ i : Fin n, a i • (f i + b) =  ∑ i : Fin n, a i • f i + b := by
  rcases h1 with ⟨_, h3⟩
  have h4: b = ∑ i : Fin n, a i • b
  rw[← sum_smul, h3, one_smul]
  nth_rewrite 2 [h4]
  rw[← sum_add_distrib]
  apply Fintype.sum_congr
  exact fun i ↦ DistribSMul.smul_add (a i) (f i) b


--Most of the proof now gets copied
theorem translation_commutes_closed {n : ℕ }(f : (Fin n → ℝ²)) (b : ℝ²) : closed_hull ( (translation b) ∘ f) = Set.image (translation b) (closed_hull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  rw[closed_hull_def, closed_hull_def, ← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[← aux_for_translation_closed h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[ aux_for_translation_closed h1]⟩

--These maps tell us hows to transform from the unit triangle to the an arbitrary triangle
noncomputable def our_basis : Basis (Fin 2) ℝ ℝ² :=  PiLp.basisFun 2 ℝ (Fin 2)
noncomputable def basis_transform (T: Triangle ) : (Fin 2 → ℝ²) := (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0)) --I think I was forced to use this definition to ensure it is the correct type
noncomputable def linear_transform (T : Triangle) := our_basis.constr ℝ (basis_transform T)
-- def matrix_transform ( T : Triangle) : Matrix (Fin 2) (Fin 2) ℝ :=![ ![T 1 0 - T 0 0, T 2 0 - T 0 0], ![T 1 1 - T 0 1, T 2 1 - T 0 1]]
-- def linear_transform1 (T : Triangle)  := Matrix.toLin' (matrix_transform T) --Have to specify type or else it well think it to be for the non euclidean space
def triangle_translation (T : Triangle) := translation (T 0)
theorem our_basis_def : our_basis = PiLp.basisFun 2 ℝ (Fin 2) := by rfl
theorem basis_transform_def (T: Triangle) : basis_transform T =  (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0)) := by rfl
theorem linear_transform_def (T : Triangle) : linear_transform T =  our_basis.constr ℝ (basis_transform T) := by rfl
theorem triangle_translation_def (T : Triangle ): triangle_translation T =  translation (T 0) := by rfl

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
  fin_cases i <;> fin_cases j <;>  simp[translation, linear_transform, basis_transform,f, our_basis]



theorem area_lin_map ( L : ℝ² →ₗ[ℝ ]  ℝ²) (A : Set ℝ²) : MeasureTheory.volume (Set.image L A) = (ENNReal.ofReal (abs ( LinearMap.det L ))) * (MeasureTheory.volume (A)) := by
  exact MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume L A


--This is some garbage that is not working yet (I want it to be like the above)
 theorem area_translation (a : ℝ²)(A : Set ℝ²) :  MeasureTheory.volume (Set.image (translation a) A) = MeasureTheory.volume (A) :=   by sorry



-- This is what we want to prove

-- I think it is easiest for now to leave this in ENNReal
theorem volume_open_unit_triangle : (MeasureTheory.volume (open_hull unit_triangle)) = 1/2 := by sorry





theorem volume_open_triangle ( T : Triangle ) : (MeasureTheory.volume (open_hull T)).toReal = triangle_area (T : Triangle) := by
  rw[← unit_triangle_to_triangle T ,triangle_translation_def]
  rw[ area_translation, area_lin_map, volume_open_unit_triangle]
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform T ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform T))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_def, basis_transform_def, our_basis_def, triangle_area ]
  repeat rw[LinearMap.toMatrix_apply]
  simp
  ring_nf


def y_axis : Submodule ℝ ℝ² := Submodule.span ℝ (Set.range unit_segment )
theorem y_axis_def :  y_axis = Submodule.span ℝ (Set.range unit_segment ) := by rfl


theorem closed_unit_segment_subset : closed_hull unit_segment ⊆ y_axis := by
  intro x
  rintro ⟨  a ,⟨ h1,h3⟩  , h2⟩
  rw[y_axis]
  --this is to get rid of the annoying coercion
  have h :(x ∈ (Submodule.span ℝ (Set.range unit_segment))) →  x ∈ ↑(Submodule.span ℝ (Set.range unit_segment))
  intro h1
  exact h1
  apply h

  rw[ mem_span_range_iff_exists_fun]
  use a

-- theorem Ennreal_zero_real_zero (A : ENNReal) :  (A = 0) → A.toReal = 0 := by
--   intro h
--   rw[h]
--   rw [ENNReal.zero_toReal]

--This argument can probably be a lot cleaner
theorem volume_closed_unit_segment : MeasureTheory.volume (closed_hull unit_segment) = 0 := by
  apply MeasureTheory.measure_mono_null (closed_unit_segment_subset )
  apply MeasureTheory.Measure.addHaar_submodule
  intro h
  have h3 : (fun | 0 => 0 | 1 => 1) ∉ y_axis
  intro h1
  rw[y_axis] at h1
  rw[ mem_span_range_iff_exists_fun] at h1
  cases' h1 with c h1
  rw[Fin.sum_univ_two, unit_segment_def] at h1
  simp at h1
  apply congrFun at h1
  specialize h1 1
  dsimp at h1
  have h2 : c 0 * 0 + c 1 * 0 = 0
  linarith
  rw[h2] at h1
  apply zero_ne_one at h1
  exact h1
  rw[h] at h3
  apply h3
  trivial


noncomputable def basis_transform_segment (L: Segment ) : (Fin 2 → ℝ²) := (fun | 0 => (L 1 - L 0) | 1 => 0)
noncomputable def linear_transform_segment (L : Segment) := our_basis.constr ℝ (basis_transform_segment L)

def segment_translation (L : Segment) := translation (L 0)
theorem basis_transform_segment_def (L : Segment)  : basis_transform_segment L =  (fun | 0 => (L 1 - L 0) | 1 => 0) := by rfl
theorem linear_transform_segment_def (L : Segment) : linear_transform_segment L =  our_basis.constr ℝ (basis_transform_segment L) := by rfl
theorem segment_translation_def (L : Segment) : segment_translation L =  translation (L 0) := by rfl

theorem unit_segment_to_segment ( L : Segment) : Set.image (segment_translation L) (Set.image (linear_transform_segment L) (closed_hull unit_segment)) = closed_hull L := by
  have h1 : segment_translation L = translation (L 0) := by rfl
  let f : (Fin 2 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0)
  have hunit_segment : unit_segment = f :=by rfl
  rw[hunit_segment, h1]
  have h2 : closed_hull (linear_transform_segment L ∘ f )= ⇑(linear_transform_segment L) '' closed_hull f
  exact closed_hull_lin_trans (linear_transform_segment L) f
  rw[← h2]
  --rw[← open_hull_lin_trans (linear_transform T) f] Why doesnt this work!??
  rw[← translation_commutes_closed]
  apply congrArg
  --This part of the proof says that the linear transformation and translation of the unit triangle give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;> simp[translation, linear_transform_segment, basis_transform_segment,f, our_basis]


theorem volume_closed_segment( L : Segment ) : (MeasureTheory.volume (closed_hull L)).toReal = 0 := by
  rw[←  unit_segment_to_segment L ,segment_translation_def]
  rw[ area_translation, area_lin_map, volume_closed_unit_segment]
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform_segment L ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform_segment L))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_segment_def, basis_transform_segment_def, our_basis_def ]
  repeat rw[LinearMap.toMatrix_apply]
  simp


-- def point0 : (Fin 2 → ℝ ) := fun | 0 => 0 | 1 => 0
-- def point1 : (Fin 2 → ℝ ) := fun | 0 => 1 | 1 => 0

-- theorem closed_unit_segment_is_box : (closed_hull unit_segment) = Set.Icc point0 point1 := by
--   have hunit_segment : unit_segment = fun | 0 => (v 0 0) | 1 => (v 1 0) := by rfl
--   have hp0 : point0 = fun | 0 => 0 | 1 => 0 := by rfl
--   have hp1 : point1 = fun | 0 => 1 | 1 => 0 := by rfl
--   ext x
--   constructor
--   · rintro ⟨ a ,⟨ h1,h3⟩  , h2⟩
--     rw[hunit_segment] at h2
--     simp at *
--     rw[← h2]
--     constructor
--     · intro i
--       rw[hp0]
--       fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
--     · intro i -- this part is directly copied except there is hp1 instead of hp0
--       rw[hp1]
--       fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
--   · rintro ⟨ h1, h2⟩
--     use (fun | 0 =>  (1 - x 0) | 1 => x 0)
--     rw[hp0,hp1] at *
--     dsimp at *
--     constructor
--     · specialize h1 0
--       specialize h2 0
--       dsimp at *
--       constructor
--       · intro i
--         fin_cases i <;> dsimp <;> linarith[h1, h1]
--       · simp
--     · ext i
--       rw[hunit_segment]
--       fin_cases i
--       · simp
--       · simp
--         specialize h1 1
--         specialize h2 1
--         dsimp at *
--         linarith



--#check MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))
--#check EuclideanSpace.volume_preserving_measurableEquiv
--#check Set.Icc point0 point1



-- theorem volume_closed_unit_segment : (MeasureTheory.volume (closed_hull unit_segment)).toReal = 0 := by
--   -- This first part is essentially showing 0 = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
--   have h0 : ∏ i : (Fin 2), (point1 i - point0 i) = 0
--   rw[ Fin.prod_univ_two]
--   unfold point0 point1
--   linarith
--   rw[ ← h0]
--   have h1: point0 ≤ point1
--   intro i
--   fin_cases i <;> dsimp <;> rw[ point0, point1] ; linarith
--   rw[ ← Real.volume_Icc_pi_toReal h1]
--   -- Now I try to show (MeasureTheory.volume (closed_hull unit_segment)).toReal = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
--   -- But the left-hand side Measuretheory.volume is not the same as the right-hand side
--   have h2 : MeasureTheory.Measure.map (⇑(EuclideanSpace.measurableEquiv (Fin 2))) MeasureTheory.volume  (Set.Icc point0 point1) = MeasureTheory.volume (Set.Icc point0 point1)
--   rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]
--   rw[ ← h2]
--   rw[ closed_unit_segment_is_box] --This is the theorem stating closed_hull unit_segment = Set.Icc point0 point1
--   sorry
--   --rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]


-- theorem segment_subset_affine_space (L : Segment) : closed_hull L ⊆ line[ℝ, (L 0), (L 1)] := by
--   intro x
--   rintro ⟨  a ,⟨ h1,h3⟩  , h2⟩
--   use L 0
--   constructor
--   · left
--     rfl
--   · use a 1 • (L 1 - L 0)
--     constructor
--     · apply mem_vectorSpan_pair_rev.mpr
--       use a 1
--       rfl
--     · dsimp at * -- I thought this could done by some linarith or simp, but it seems I have to do it by hand
--       rw[Fin.sum_univ_two] at h2 h3
--       have h4 : L 0 = (1: ℝ ) • L 0 := Eq.symm (MulAction.one_smul (L 0))
--       nth_rewrite 2 [h4]
--       rw[← h3,← h2 ,smul_sub (a 1) (L 1) (L 0), Module.add_smul (a 0) (a 1) (L 0)]
--       have h5: a 1 •  L 1 - a 1 • L 0 = a 1 • L 1 + (- a 1) • L 0
--       simp
--       exact rfl
--       rw[h5]
--       have h6: a 1 • L 1 + -a 1 • L 0 + (a 0 • L 0 + a 1 • L 0) = a 1 • L 1 + (-a 1 • L 0 + a 0 • L 0 + a 1 • L 0)
--       rw[add_assoc]
--       nth_rewrite 2 [← add_assoc]
--       rfl
--       rw[h6]
--       simp
--       rw[add_comm]



-- lemma equality_implies_subset (A B : Type) (f g : A → B): f = g → (∀ x, f x = g x)    := by
--   exact fun a x ↦ congrFun a x

-- #check vadd_left_mem_affineSpan_pair.mp
-- theorem volume_closed_segment (L : Segment) : (MeasureTheory.volume (closed_hull L)).toReal = 0 := by
--   apply Ennreal_zero_real_zero
--   apply MeasureTheory.measure_mono_null (segment_subset_affine_space L )
--   apply MeasureTheory.Measure.addHaar_affineSubspace
--   apply lt_top_iff_ne_top.mp
--   apply (AffineSubspace.lt_iff_le_and_exists (affineSpan ℝ {L 0, L 1}) ⊤).mpr
--   constructor
--   · exact fun ⦃a⦄ a ↦ trivial
--   · by_cases hL : L 0 ≠ L 1
--     · let a : ℝ² := (fun | 0 => - (L 1 - L 0) 1 | 1 => (L 1 - L 0) 0 )
--       have ha : a = (fun | 0 => - (L 1 - L 0) 1 | 1 => (L 1 - L 0) 0 ) := by rfl
--       use  a +ᵥ L 0
--       constructor
--       · trivial
--       · intro h
--         apply vadd_left_mem_affineSpan_pair.mp at h
--         cases' h with r h
--         rw[ha] at h
--         dsimp at h
--         apply fun a x ↦ congrFun a x at h
--         have h1 := h 0
--         have h2 := h 1
--         simp at *

--     · sorry
--         --rw[ha]


--     --use vadd_left_mem_affineSpan_pair



--We additionally want its flipped version

-- def flip_unit_triangle : Triangle  := fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0)
-- def open_flip_unit_triangle := open_hull flip_unit_triangle
-- def closed_flip_unit_triangle := closed_hull flip_unit_triangle

-- --Then additionally we have the diagonal
-- def diagonal_line : Segment := fun | 0 => (v 1 0) | 1 => (v 0 1)
-- def open_diagonal_line := open_hull diagonal_line

-- --We now want to show the open_unit_square is the disjoint union of these open triangles
-- --and the open diagonal


-- def union_of_open_triangles := open_unit_triangle  ∪ open_flip_unit_triangle




-- theorem open_unit_square1_is_union : open_unit_square1 = union_of_open_triangles ∪  open_diagonal_line := by
--   have hunit : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl
--   have hdiag : diagonal_line = fun | 0 => (v 1 0) | 1 => (v 0 1) := by rfl
--   have hflipunit: flip_unit_triangle = fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0) := by rfl
--   ext x
--   constructor
--   · rintro ⟨ h,h1,h2, h3 ⟩
--     have h7 := lt_trichotomy (x 0 +x 1) 1
--     rcases h7 with (h4 | h5| h6)
--     · left
--       left
--       use (fun | 0 => (1- x 0 - x 1) | 1 => x 0 | 2 => x 1)
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_three]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_three, hunit]
--         simp
--         ext i
--         fin_cases i <;> simp
--     · right
--       use (fun | 0 => x 0 | 1 => x 1 )
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_two]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_two,hdiag]
--         simp
--         ext i
--         fin_cases i <;> simp
--     · left
--       right
--       use (fun | 0 => (x 0 + x 1 -1) | 1 => 1 - x 0 | 2 => 1- x 1)
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_three]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_three, hflipunit]
--         simp
--         ext i
--         fin_cases i <;> simp
--   · intro h
--     cases' h  with h1 h2
--     cases' h1 with h1 h3
--     · rcases h1 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_three,hunit] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
--     · rcases h3 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_three,hflipunit] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
--     · rcases h2 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_two,hdiag] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]




-- theorem open_unit_squares_are_same : open_unit_square = open_unit_square1 := by
--   ext x
--   constructor
--   · rintro ⟨ a,⟨ ⟨ h2,h3⟩ ,h1⟩ ⟩
--     have hp : Psquare = (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1) := by rfl
--     rw[← h1]
--     dsimp
--     rw[Fin.sum_univ_four,hp] at *
--     dsimp
--     refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h2 0 ,h2 1 ,h2 2, h2 3]
--   · sorry



-- theorem open_square_union_of : open_unit_square = union_of_open_triangles ∪  open_diagonal_line := by
--   rw[ open_unit_squares_are_same]
--   exact open_unit_square1_is_union
