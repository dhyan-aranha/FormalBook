import Mathlib.Tactic
import FormalBook.Appendix
-- import FormalBook.sperner

/-!
# One square and an odd number of triangles
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Classical
open Finset

-- First we define the inductive type Color, which will be the target type of the coloring
-- function. The coloring function will take a point in ℝ² and return a color from Color (eg. Red
-- Blue or Green).

inductive Color
| Red
| Green
| Blue

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation ℝ Γ₀)

-- Now we define the coloring function as it appears in the Book.

def coloring : (X : ℝ²) → Color
| X => if v (X 0) < v 1 ∧ v (X 1) < v 1 then Color.Red
  else if v (X 0) < v (X 1) ∧ v (X 1) ≥ v 1 then Color.Green
  else Color.Blue

-- The next three lemmas below reverse the coloring function.
-- Namely, for a given color they return inequalities describing the region with this color.
-- They will be of use in the proof of the lemma on the boundedness of the determinant.

lemma green_region (X : ℝ²) : (coloring v X = Color.Green) → v (X 0) < v (X 1) ∧ v (X 1) ≥ v (1) := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1 h2
  rw [v.map_one]
  exact h2

lemma red_region (X : ℝ²) : (coloring v X = Color.Red) → v (X 0) < v 1 ∧ v (X 1) < v 1 := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1
  rw [v.map_one]
  exact h1

lemma blue_region (X : ℝ²) : (coloring v X = Color.Blue) → v (X 0) ≥ v (1) ∧ v (X 0) ≥ v (X 1) := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1 h2
  rw [v.map_one]
  -- Apply De Morgan's law
  rw [Decidable.not_and_iff_or_not] at h1 h2
  -- Get rid of negations
  rw [not_lt, not_lt] at h1
  rw [not_lt, not_le] at h2
  -- Split h1 into cases
  cases' h1 with p q
  constructor
  · apply p
  · cases' h2 with m n
    apply m
    have q' : v (X 1) ≤ 1 := by
      exact le_of_lt n
    apply le_trans q' p
  -- Split h2 into cases
  cases' h2 with a b
  constructor
  · apply le_trans q a
  · exact a
  -- No more cases left
  rw [← not_lt] at q
  contradiction

-- Record our definition of a rainbow triangle

def rainbow_triangle (T : Fin 3 → ℝ²) : Prop := Function.Surjective (coloring v ∘ T)

-- We need a few inequalities that will be used in the proof of the main lemma.
-- These are just bounds on valuations of terms that appear in the
-- determinant expression that captures the area of a triangle.

lemma valuation_bounds
  (X Y Z : ℝ²)
  (hb : coloring v X = Color.Blue)
  (hg : coloring v Y = Color.Green)
  (hr : coloring v Z = Color.Red) :
  v (X 0 * Y 1) ≥ 1 ∧
  v (X 1 * Z 0) < v (X 0 * Y 1) ∧
  v (Y 0 * Z 1) < v (X 0 * Y 1) ∧
  v (X 0 * Y 1) > v (-(Y 1 * Z 0)) ∧
  v (X 0 * Y 1) > v (-(X 1 * Y 0)) ∧
  v (X 0 * Y 1) > v (-(X 0 * Z 1)) := by

  -- Get rid of all minus signs
  repeat rw [Valuation.map_neg]
  -- Apply multiplicativity of v everywhere
  repeat rw [v.map_mul]

  -- Trivial bounds from the coloring
  have hx0 : v (X 0) ≥ v 1 := (blue_region v X hb).1
  have hy1 : v (Y 1) ≥ v 1 := (green_region v Y hg).2
  have hz0 : v (Z 0) < v 1 := (red_region v Z hr).1
  have hz1 : v (Z 1) < v 1 := (red_region v Z hr).2
  have hxx : v (X 1) ≤ v (X 0) := (blue_region v X hb).2
  have hyy : v (Y 0) < v (Y 1) := (green_region v Y hg).1
  -- Replace v 1 by 1
  simp_all only [map_one]
  -- We won't need the coloring hypotheses anymore
  clear hb hg hr

  -- Non-negativity bounds
  have x0_gt_zero : v (X 0) > 0 := gt_of_ge_of_gt hx0 zero_lt_one
  have y1_gt_zero : v (Y 1) > 0 := gt_of_ge_of_gt hy1 zero_lt_one

  -- v (X 0) * v (Y 1) ≥ 1
  constructor
  exact Right.one_le_mul hx0 hy1

  -- v (X 1) * v (Z 0) < v (X 0) * v (Y 1)
  constructor
  apply mul_lt_mul'
  exact hxx
  exact gt_of_ge_of_gt hy1 hz0
  exact zero_le'
  exact x0_gt_zero

  -- v (Y 0) * v (Z 1) < v (X 0) * v (Y 1)
  constructor
  rw [mul_comm (v (X 0)) (v (Y 1))]
  apply mul_lt_mul''
  exact hyy
  exact gt_of_ge_of_gt hx0 hz1
  exact zero_le'
  exact zero_le'

  -- v (X 0) * v (Y 1) > v (Y 1) * v (Z 0)
  constructor
  rw [mul_comm (v (X 0)) (v (Y 1))]
  apply mul_lt_mul'
  apply refl
  exact gt_of_ge_of_gt hx0 hz0
  exact zero_le'
  exact y1_gt_zero

  -- v (X 0) * v (Y 1) > v (X 1) * v (Y 0)
  constructor
  apply mul_lt_mul' hxx hyy
  apply zero_le'
  exact x0_gt_zero

  -- v (X 0) * v (Y 1) > v (X 0) * v (Z 1)
  apply mul_lt_mul'
  apply refl
  exact gt_of_ge_of_gt hy1 hz1
  exact zero_le'
  exact x0_gt_zero

--The next definition and lemma relate things to matrices more like in the book.
--But they are not needed.

def Color_matrix (X Y Z : ℝ²): Matrix (Fin 3) (Fin 3) ℝ :=
![![X 0, X 1, 1], ![Y 0, Y 1, 1], ![Z 0, Z 1, 1]]

lemma det_of_Color_matrix (X Y Z : ℝ²) :
  Matrix.det (Color_matrix X Y Z) =
   (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) := by
rw [Matrix.det_fin_three, Color_matrix]
simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
     Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
     Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.tail_val',
     Matrix.head_val', Matrix.head_fin_const, mul_one, one_mul]
ring_nf

-- Valuation of a sum of six variables is equal to the valuation of the largest of them
lemma valuation_max
  {A a₁ a₂ a₃ a₄ a₅ : ℝ}
  (h1 : v (A) > v (a₁))
  (h2 : v (A) > v (a₂))
  (h3 : v (A) > v (a₃))
  (h4 : v (A) > v (a₄))
  (h5 : v (A) > v (a₅)) :
  v (A + a₁ + a₂ + a₃ + a₄ + a₅) = v (A) := by
  -- move brackets to the right
  repeat rw [add_assoc]
  -- Now just write the function representing the proof term directly.
  -- exact map_add_eq_of_lt_left v <| map_add_lt v h1 <| map_add_lt v h2 h3
  apply Valuation.map_add_eq_of_lt_left
  repeat (
    apply Valuation.map_add_lt v _ _
    assumption
  )
  assumption

-- This is the first main lemma of Chapter 22

lemma bounded_det
  (X Y Z : ℝ²)
  (hb : coloring v X = Color.Blue)
  (hg : coloring v Y = Color.Green)
  (hr : coloring v Z = Color.Red) :
  v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) ≥ 1 := by
  -- Change minus signs to plus signs
  repeat rw [sub_eq_add_neg]
  -- Establish all required assumptions for the lemma
  rcases (valuation_bounds v X Y Z hb hg hr) with ⟨h0, ⟨h1, ⟨h2, ⟨h3, ⟨h4,h5⟩⟩⟩⟩⟩
  -- Use the above lemma
  rw [valuation_max v h1 h2 h3 h4 h5]
  -- Change the inequality to v (X 0 * Y 1) ≥ 1
  exact h0

-- We now prove that for any line segment in ℝ² contains at most 2 colors.

lemma det_triv_triangle (X Y : ℝ² ) : det (fun | 0 => X | 1 => X | 2 => Y) = 0 := by
  simp [det]

lemma Lhull_equals_Thull (L:Segment) :
closed_hull L = closed_hull (fun | 0 => L 0 | 1 => L 0 | 2 => L 1: Fin 3 → ℝ²) := by

ext x
constructor
intro ⟨α, hα, hαx⟩
use fun | 0 => 0 | 1 => α 0| 2 => α 1
refine ⟨⟨?_,?_⟩, ?_⟩
intro i;  fin_cases i <;> simp [hα.1]
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three];
intro ⟨α, hα, hαx⟩
use fun | 0  => α 0 + α 1| 1 => α 2
refine ⟨⟨?_,?_⟩, ?_⟩
intro i; fin_cases i <;> (simp; linarith [hα.1 0, hα.1 1, hα.1 2])
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three, add_smul]



theorem no_Color_lines (L : Segment) {Γ₀ : Type} (locg : LinearOrderedCommGroupWithZero Γ₀)
(v : Valuation ℝ Γ₀) : ∃ c : Color, ∀ P ∈ closed_hull L, coloring v P ≠ c := by

by_contra h
push_neg at h
have hr : ∃ z ∈ closed_hull L , coloring v z = Color.Red := by
  apply h
have hb : ∃ x ∈ closed_hull L , coloring v x = Color.Blue := by
  apply h
have hg : ∃ y ∈ closed_hull L , coloring v y = Color.Green := by
  apply h
rcases hr with ⟨z, hz, hzr⟩
rcases hb with ⟨x, hx, hxb⟩
rcases hg with ⟨y, hy, hyg⟩
let Tseg : Fin 3 → ℝ² := fun | 0 => L 0 | 1 => L 0 | 2 => L 1
have hTseg : det Tseg = 0 := det_triv_triangle (L 0) (L 1)
have rain1: det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  rw [Lhull_equals_Thull L] at hx hy hz
  exact det_0_triangle_imp_triv hTseg x y z hx hy hz
have vrain1 : v (det (fun | 0 => x | 1 => y | 2 => z)) = v 0 := by
  rw [rain1]
rw [v.map_zero] at vrain1
have rain2: v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  have h_det : det (fun | 0 => x | 1 => y | 2 => z) =
    (x 0 * y 1 + x 1 * z 0 + y 0 * z 1 - y 1 * z 0 - x 1 * y 0 - x 0 * z 1) := by
    simp [det]
    ring_nf
  rw [h_det]
  apply bounded_det
  exact hxb
  exact hyg
  exact hzr
have contra: v (det (fun | 0 => x | 1 => y | 2 => z)) = 0 ∧
v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  exact ⟨vrain1, rain2⟩
have ⟨h1, h2⟩ := contra
have h3 : (0 : Γ₀) ≥ 1 := by
  rw [h1] at h2
  exact h2
exact not_le_of_gt (zero_lt_one) h3

-- We show next that the coloring of (0,0) is red, (0,1) is green and (1,0) is blue.

lemma red00 : coloring v ![0,0] = Color.Red := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

lemma green01 : coloring v  ![0, 1] = Color.Green := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

lemma blue10 : coloring v ![1,0] = Color.Blue := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

--TODO: Show that the area of a Color triangle cannot be zero or 1/n for n odd (here we will
-- need the fact that v(1/2) > 1).
