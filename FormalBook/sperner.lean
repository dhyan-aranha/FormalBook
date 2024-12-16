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




/- Should we doe this or not? -/
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y


def Psquare : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

def unit_square : Set ℝ²
  := closed_hull Psquare

def open_unit_square : Set ℝ²
  := open_hull Psquare


theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  sorry




@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


/- These two triangles dissect the square and have equal area.-/
def Δ₀  : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

/- Corner of the standard simplex.-/
def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

/- Such a corner is actually a member of the simplex-/
lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} :
    simplex_vertex i ∈ closed_simplex n := by
  unfold simplex_vertex
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp_all, by simp⟩


@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by
  unfold simplex_vertex; simp

lemma vertex_mem_closed {n : ℕ} {i : Fin n} {f : Fin n → ℝ²} :
    f i ∈ ((fun α ↦ ∑ i, α i • f i) '' closed_simplex n) :=
  ⟨simplex_vertex i, ⟨simplex_vertex_in_simplex, by simp⟩⟩


lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext v
  constructor
  · intro ⟨α, hα,hαv⟩
    simp [←sum_smul, hα.2] at hαv
    exact hαv.symm
  · intro hv
    rw [hv]
    exact vertex_mem_closed (i := ⟨0,Nat.zero_lt_of_ne_zero hn⟩)






noncomputable def vertex_set {n : ℕ} (P : Fin n → ℝ²) : Finset ℝ² :=
    image P univ



lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closed_simplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closed_simplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push_neg at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero _ (fun _ ↦ rfl)
  linarith



lemma simplex_co_leq_1 {n : ℕ} {α : Fin n → ℝ}
    (h₁ : α ∈ closed_simplex n) : ∀ i, α i ≤ 1 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨i,hi⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1   < α i             := hi
    _   = ∑ k ∈ {i}, α k  := (sum_singleton _ _).symm
    _   ≤ ∑ k, α k        := sum_le_univ_sum_of_nonneg h₁.1
    _   = 1               := h₁.2



/- Vertex set of polygon P₁ lies inside the closed hull of polygon P₂ implies
    the closed hull of P₁ lies inside the closed hull of P₂. -/
lemma closed_hull_convex {n₁ n₂ : ℕ} {P₁ : Fin n₁ → ℝ²} {P₂ : Fin n₂ → ℝ²}
  (h : ∀ i, P₁ i ∈ closed_hull P₂) :
  closed_hull P₁ ⊆ closed_hull P₂ := by
  intro p ⟨β, hβ, hβp⟩
  use fun i ↦ ∑ k, (β k) * (choose (h k) i)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact fun _ ↦ Fintype.sum_nonneg fun _ ↦ mul_nonneg (hβ.1 _) ((choose_spec (h _)).1.1 _)
  · simp_rw [sum_comm (γ := Fin n₂), ←mul_sum, (choose_spec (h _)).1.2, mul_one]
    exact hβ.2
  · simp_rw [sum_smul, mul_smul, sum_comm (γ := Fin n₂), ←smul_sum, (choose_spec (h _)).2]
    exact hβp




/- A basic lemma about sums that I want to use but that I cannot find.-/
lemma sum_if_comp {α β : Type} [Fintype α] [AddCommMonoid β] (f : α → β) (i : α) :
    ∑ k, (if k = i then 0 else f k) = ∑ k ∈ {i}ᶜ, f k := by
  rw [←sum_add_sum_compl {i}, add_comm, ←add_zero (∑ k ∈ {i}ᶜ, f k)]
  congr 1
  · exact sum_ite_of_false (fun _ hk₁ hk₂ ↦ by simp at hk₁; exact hk₁ hk₂) _ _
  · simp


/- Basic lemmas about signs. -/
lemma sign_mul_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  by_cases hb₀ : 0 < b
  · rw [Real.sign_of_pos hb₀, Real.sign_of_pos (mul_pos ha hb₀)]
  · by_cases hb₁ : b < 0
    · rw [Real.sign_of_neg hb₁, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb₁)]
    · simp [(by linarith : b = 0)]

lemma sign_pos' {a : ℝ} (h : Real.sign a = 1) : 0 < a := by
  by_contra hnonpos; simp at hnonpos
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_neg (lt_of_le_of_ne hnonpos h0 )] at h
    linarith

lemma sign_neg' {a : ℝ} (h : Real.sign a = -1) : a < 0 := by
  by_contra hnonneg; simp at hnonneg
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_pos (lt_of_le_of_ne hnonneg ?_)] at h
    linarith
    exact fun a_1 ↦ h0 (id (Eq.symm a_1)) -- very strange

lemma sign_div_pos {a b : ℝ} (hb₀ : b ≠ 0) (hs : Real.sign a = Real.sign b) :
    0 < a / b := by
  cases' Real.sign_apply_eq_of_ne_zero _ hb₀ with hbs hbs <;> rw [hbs] at hs
  · exact div_pos_of_neg_of_neg (sign_neg' hs) (sign_neg' hbs)
  · exact div_pos (sign_pos' hs) (sign_pos' hbs)

example {a b : ℝ} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a / b := by
  exact div_pos h₁ h₂

/- Proofs of these helper things are ugly-/
lemma mul_cancel {a b c : ℝ} (h : a ≠ 0) (h2: a * b = a * c) :
        b = c := by simp_all only [ne_eq, mul_eq_mul_left_iff, or_false]

lemma smul_cancel {a : ℝ} {b c : ℝ²} (h₁ : a ≠ 0) (h₂: a • b = a • c)
    : b = c := by
  refine PiLp.ext ?_
  intro i
  rw [PiLp.ext_iff] at h₂
  have l := h₂ i
  simp [PiLp.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, h₁] at l
  assumption


/-
  Given a v ∈ ℝ² inside a closed triangle that is not one of its vertices
  there exists a (non-trivial) segment L with v in its interior and
  L inside the closed triangle. This statement is true even if the triangle
  is degenerate.
-/
lemma non_vtx_imp_seg (T : Triangle) (v : ℝ²) (h₁ : v ∉ vertex_set T) (h₂ : v ∈ closed_hull T) :
    ∃ (L : Segment), L 0 ≠ L 1 ∧ closed_hull L ⊆ closed_hull T ∧ v ∈ open_hull L := by
  have ⟨α, hα, hvα⟩ := h₂; dsimp at hvα
  have ⟨i,hi⟩ := simplex_exists_co_pos hα
  have hneq : α i ≠ 1 := by
    intro hcontra
    refine h₁ (mem_image.mpr ⟨i, by simp, ?_⟩)
    rw [←hvα, ←sum_add_sum_compl {i} fun k ↦ α k • T k, ←add_zero (T i)]
    congr
    · rw [sum_singleton, hcontra, one_smul]
    · refine (sum_eq_zero ?_).symm
      intro k hk; simp at hk
      rw [simplex_co_eq_1 hα hcontra k hk, zero_smul]
  have heq : v - α i • T i = (1 - α i) • ∑ k ∈ {i}ᶜ, (α k / (1 - α i)) • T k := by
    simp [smul_sum, smul_smul, mul_div_cancel₀ _ (sub_ne_zero_of_ne hneq.symm),
      sub_eq_iff_eq_add', ←hvα, ←sum_add_sum_compl {i} fun k ↦ α k • T k]
  use fun | 0 => T i | 1 => ∑ k ∈ {i}ᶜ, ((α k) / (1 - α i)) • T k
  dsimp
  refine ⟨?_,?_,?_⟩
  · intro hTi
    refine h₁ (mem_image.mpr ⟨i, by simp, ?_⟩)
    have hcontra := congrArg (HSMul.hSMul (1 - α i)) hTi
    simp only [sub_smul, one_smul, ← heq, sub_eq_iff_eq_add', add_sub_cancel] at hcontra
    exact hcontra
  · apply closed_hull_convex
    intro k; fin_cases k
    exact vertex_mem_closed
    use fun j ↦ if j = i then 0 else (α j) / (1 - α i)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro j
      by_cases h : j = i <;> simp_all
      exact div_nonneg (hα.1 j) (sub_nonneg_of_le (simplex_co_leq_1 hα i))
    · convert sum_if_comp (fun j ↦ (α j /  (1 - α i))) i
      apply mul_left_cancel₀ (sub_ne_zero_of_ne hneq.symm)
      simp [mul_sum, mul_div_cancel₀ _ (sub_ne_zero_of_ne hneq.symm),sub_eq_iff_eq_add']
      convert hα.2.symm
      rw [←(sum_add_sum_compl {i} fun k ↦ α k)]
      convert add_right_cancel_iff.mpr (sum_singleton _ _).symm
      exact AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd ℝ -- This feels strange
    · simp
      convert sum_if_comp (fun j ↦ (α j /  (1 - α i)) • T j) i
  · use fun | 0 => α i | 1 => 1 - α i
    refine ⟨⟨?_, by simp⟩,?_⟩
    · intro k
      fin_cases k <;> simp
      · linarith
      · exact lt_of_le_of_ne (simplex_co_leq_1 hα _) hneq
    · simp [←heq]

/-
  There is no non-trivial segment going through (0,0) of the unit square.
  This should imply the same statement for the other corners of the square without too much work.
-/
/-
This lemma is now broken because the definition of unit_square changed.

lemma no_segment_through_origin_square {L : Segment} (h₁ : L 0 ≠ L 1)
    (h₂ : closed_hull L ⊆ unit_square) : v 0 0 ∉ open_hull L := by
  have hNonzero : ∃ i j, L i j ≠ 0 := by
    by_contra hcontra; push_neg at hcontra
    exact h₁ (PiLp.ext fun i ↦ (by rw [hcontra 0 i, hcontra 1 i]))
  have ⟨i,j,hNonzero⟩ := hNonzero
  intro ⟨α,hα,hαv⟩
  have hLpos : ∀ l k, 0 ≤ L l k := by
    intro l k
    have ⟨_,_,_,_⟩ := h₂ (vertex_mem_closed (i := l))
    fin_cases k <;> assumption
  rw [←lt_self_iff_false (0 : ℝ)]
  calc
    0 < α i * L i j             := mul_pos (hα.1 i) (lt_of_le_of_ne (hLpos i j) (hNonzero.symm))
    _ = ∑ k ∈ {i}, α k * L k j  := by simp
    _ ≤ ∑ k, α k * L k j        := sum_le_univ_sum_of_nonneg (fun k ↦ (mul_nonneg_iff_of_pos_left (hα.1 k)).mpr (hLpos k j))
    _ ≤ (v 0 0) j               := by rw [←hαv]; simp
    _ = 0                       := by fin_cases j <;> simp

-/

/-
  Some stuff about bijections Fin 3 → Fin 3.
  This might be useful to brute force things later.
-/

def σ : Fin 6 → (Fin 3 → Fin 3) := fun
| 0 => (fun | 0 => 0 | 1 => 1 | 2 => 2)
| 1 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
| 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)
| 3 => (fun | 0 => 1 | 1 => 2 | 2 => 0)
| 4 => (fun | 0 => 2 | 1 => 0 | 2 => 1)
| 5 => (fun | 0 => 2 | 1 => 1 | 2 => 0)

def b_sign : Fin 6 → ℝ := fun
  | 0 => 1 | 1 => -1 | 2 => -1 | 3 => 1 | 4 => 1 | 5 => -1

def b_inv : Fin 6 → Fin 6 := fun
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5

def last_index : Fin 3 → Fin 3 → Fin 3 := fun
  | 0 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
  | 1 => (fun | 0 => 2 | 1 => 1 | 2 => 0)
  | 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)


lemma last_index_diff {i j : Fin 3} (hij : i ≠ j) :
    i ≠ last_index i j ∧ j ≠ last_index i j := by
  fin_cases i <;> fin_cases j <;> tauto

lemma last_index_comp {i j : Fin 3} (hij : i ≠ j) :
    ({i,j} : Finset (Fin 3))ᶜ = {last_index i j} := by
  fin_cases i <;> fin_cases j <;> tauto

lemma bijection_right_inv
    : ∀ b, (σ b) ∘ (σ (b_inv b)) = id := by
  intro b; funext x
  fin_cases b <;> fin_cases x <;> rfl

lemma bijection_left_inv
    : ∀ b, (σ (b_inv b)) ∘ (σ b) = id := by
  intro b; funext x
  fin_cases b <;> fin_cases x <;> rfl

lemma fun_in_bijections {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ b, σ b = (fun | 0 => i | 1 => j | 2 => k)  := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (tauto)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

lemma sign_non_zero : ∀ b, b_sign b ≠ 0 := by
  intro b; fin_cases b <;> simp [b_sign]


lemma bijection_sum_right {α : Type} [AddCommMonoid α] (f : Fin 3 → α) (b : Fin 6)
    : ∑ i, (f ∘ σ b) i = ∑ i, f i := by
  fin_cases b <;> simp [σ,Fin.sum_univ_three, add_comm, add_assoc,add_left_comm]


/- Given i j map to the bijection that maps i to 0, j to 1 and last to 2 -/
def normalize_map : Fin 3 → Fin 3 → (Fin 3 → Fin 3) := fun
  | 0 => (fun | 0 => σ 0 | 1 => σ 0 | 2 => σ 1)
  | 1 => (fun | 0 => σ 2 | 1 => σ 0 | 2 => σ 4)
  | 2 => (fun | 0 => σ 3 | 1 => σ 5 | 2 => σ 0)


lemma normalize_val_i {i j : Fin 3} (hij : i ≠ j) : normalize_map i j i = 0 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, σ]; try tauto)

lemma normalize_val_j {i j : Fin 3} (hij : i ≠ j) : normalize_map i j j = 1 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, σ]; try tauto)

lemma normalize_val_k {i j : Fin 3} (hij : i ≠ j) : normalize_map i j (last_index i j) = 2 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, last_index, σ]; try tauto)





/-
  Better I think to just define the determinant.
-/

def det (T : Triangle) : ℝ
  := (T 0 1 - T 1 1) * (T 2 0) + (T 1 0 - T 0 0) * (T 2 1) + ((T 0 0) * (T 1 1) - (T 1 0) * (T 0 1))

lemma linear_combination_det_last {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => y | 2 => (∑ i, α i • P i)) =
  ∑ i, (α i * det (fun | 0 => x | 1 => y | 2 => (P i))) := by
  simp [det, left_distrib, sum_add_distrib, sum_apply _, mul_sum, ←sum_mul, hα]
  congr <;> (ext; ring)

lemma det_perm {T : Triangle} (b : Fin 6) :
    det T = (b_sign b) *  det (T ∘ (σ b)) := by
  fin_cases b <;> (simp_all [det, b_sign, σ]; try ring)

lemma det_zero_perm {T : Triangle} (hT  : det T = 0) :
    ∀ i j k, det (fun | 0 => T i | 1 => T j | 2 => T k) = 0 := by
  intro i j k
  by_cases hij : i = j
  · simp [det, hij]
  · by_cases hik : i = k
    · simp [det, hik]; ring
    · by_cases hjk : j = k
      · simp [det, hjk]; ring
      · have ⟨b, hb⟩ := fun_in_bijections hij hik hjk
        rw [det_perm b] at hT
        convert eq_zero_of_ne_zero_of_mul_left_eq_zero (sign_non_zero b) hT
        split <;> simp [hb]

lemma det_zero_01 {T : Triangle} (h01 : T 0 = T 1) :
    det T = 0 := by simp [det, h01]

lemma det_zero_02 {T : Triangle} (h02 : T 0 = T 2) :
    det T = 0 := by simp [det, h02]; ring

lemma det_zero_12 {T : Triangle} (h12 : T 1 = T 2) :
    det T = 0 := by simp [det, h12]; ring

/- Doing it with bijections here doesn't really seem to gain anything. -/
lemma linear_combination_det_middle {n : ℕ} {x z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => (∑ i, α i • P i) | 2 => z) =
  ∑ i, (α i * det (fun | 0 => x | 1 => (P i) | 2 => z)) := by
  convert linear_combination_det_last (y := x) (P := P) (x := z) hα using 1
  · convert det_perm 4
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 4
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl

lemma linear_combination_det_first {n : ℕ} {y z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => (∑ i, α i • P i) | 1 => y | 2 => z) =
  ∑ i, (α i * det (fun | 0 => (P i) | 1 => y | 2 => z)) := by
  convert linear_combination_det_last (y := z) (P := P) (x := y) hα using 1
  · convert det_perm 3
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 3
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl



lemma det_0_triangle_imp_triv {T : Triangle} (hT : det T = 0) :
    ∀ x y z, x ∈ closed_hull T → y ∈ closed_hull T → z ∈ closed_hull T →
      det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  intro x y z ⟨_, ⟨_, hαx⟩ , hx⟩ ⟨_, ⟨_, hαy⟩ , hy⟩ ⟨_, ⟨_, hαz⟩ , hz⟩
  simp [←hx, ← hy, ←hz, linear_combination_det_first hαx,
    linear_combination_det_middle hαy, linear_combination_det_last hαz, det_zero_perm hT]


def sign_seg (L : Segment) (v : ℝ²) : ℝ := det (fun | 0 => L 0 | 1 => L 1 | 2 => v)


lemma sign_seg_mem_zero (L : Segment) {v : ℝ²} (hv : v ∈ closed_hull L) :
    sign_seg L v = 0 := by
  sorry





lemma open_triangle_sign_det {T : Triangle} {i j : Fin 3} (hij : i ≠ j) :
    ∀ v ∈ open_hull T,
    Real.sign (sign_seg (fun | 0 => T i | 1 => T j) v) =
    Real.sign (det (fun | 0 => T i | 1 => T j | 2 => T (last_index i j))) := by
  intro v ⟨α,⟨hαpos,hα⟩ ,hαv⟩
  rw [←hαv, sign_seg, linear_combination_det_last hα, ←sum_add_sum_compl {i,j},
      sum_pair hij, det_zero_02, det_zero_12, last_index_comp hij]
  simp [sign_mul_pos (hαpos _)]
  all_goals rfl





def Tside (T : Triangle) : Fin 3 → Segment := fun
  | 0 => (fun | 0 => T 1 | 1 => T 2)
  | 1 => (fun | 0 => T 2 | 1 => T 0)
  | 2 => (fun | 0 => T 0 | 1 => T 1)

noncomputable def Tco (T : Triangle) (x : ℝ²) : Fin 3 → ℝ :=
  fun i ↦ (sign_seg (Tside T i) x) / det T

lemma Tco_sum {T : Triangle} (hdet : det T ≠ 0) (x : ℝ²) : ∑ i, Tco T x i = 1 := by
  apply mul_cancel hdet
  simp_rw [mul_sum, Tco, Fin.sum_univ_three, mul_div_cancel₀ _ hdet, sign_seg, det, Tside]
  ring

lemma Tco_linear {n : ℕ} {T : Triangle} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) (k : Fin 3): Tco T (∑ i, (α i) • (P i)) k =  ∑ i, α i * Tco T (P i) k := by
  fin_cases k <;> (
  simp [Tco, sign_seg, linear_combination_det_last hα,sum_div]
  congr; funext _; ring)

lemma Tco_basis_diag {T : Triangle} (hdet : det T ≠ 0) {i : Fin 3} :
    Tco T (T i) i = 1 := by
  fin_cases i<;>(
    apply mul_cancel hdet
    simp [Tco, mul_div_cancel₀ _ hdet]
    simp [sign_seg,det, Tside]
  ) <;> ring

lemma Tco_basis_off_diag {T : Triangle} {i j: Fin 3} (hij : i ≠ j) :
    Tco T (T i) j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals (try tauto)
  all_goals (
    simp [Tco]; left
    simp [sign_seg, det, Tside]; ring)

lemma Tco_sum_val {T : Triangle} (hdet : det T ≠ 0) {α : Fin 3 → ℝ} (hα : ∑i, α i = 1) (k : Fin 3) :
    Tco T (∑ i, (α i) • (T i)) k = α k := by
  rw [Tco_linear hα, Fin.sum_univ_three]
  fin_cases k <;> simp [Tco_basis_diag hdet, Tco_basis_off_diag]

lemma Tco_sum_self {T : Triangle} (hdet : det T ≠ 0) (x : ℝ²) :
    ∑ i, (Tco T x i) • (T i) = x := by
  apply smul_cancel hdet
  simp [smul_sum, smul_smul, Fin.sum_univ_three, mul_div_cancel₀ _ hdet, Tco]
  simp [sign_seg, det, Tside]
  exact PiLp.ext (fun i ↦ by fin_cases i <;> (simp; ring))

lemma closed_triangle_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} :
    x ∈ closed_hull T ↔ ∀ i, 0 ≤ Tco T x i := by
  constructor
  · exact fun ⟨α,hα,hαx⟩ ↦ by simp_rw [←hαx, Tco_sum_val hdet hα.2]; exact hα.1
  · exact fun hco ↦ ⟨Tco T x, ⟨hco, Tco_sum hdet x⟩, Tco_sum_self hdet x⟩

lemma open_triangle_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} :
    x ∈ open_hull T ↔ ∀ i, 0 < Tco T x i := by
  constructor
  · exact fun ⟨α,hα,hαx⟩ ↦ by simp_rw [←hαx, Tco_sum_val hdet hα.2]; exact hα.1
  · exact fun hco ↦ ⟨Tco T x, ⟨hco, Tco_sum hdet x⟩, Tco_sum_self hdet x⟩


def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closed_hull P) \ (open_hull P)

lemma boundary_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) :
    x ∈ boundary T ↔ ∃ i, Tco T x i = 0 := by
  constructor
  · intro hxB
    by_contra hAll
    push_neg at hAll
    apply ((Set.mem_diff _).mp hxB).2
    rw [open_triangle_iff hdet]
    rw [closed_triangle_iff hdet] at hx
    exact fun i ↦ lt_of_le_of_ne (hx i) (hAll i).symm
  · intro ⟨i,hi⟩
    rw [boundary, Set.mem_diff]
    refine ⟨hx,?_⟩
    intro hxOpen
    rw [open_triangle_iff hdet] at hxOpen
    linarith [hi, hxOpen i]



lemma mem_closed_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3)  :
    Tco T x i = 0 ↔ x ∈ closed_hull (Tside T i) := by
  sorry

lemma mem_open_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3) :
    Tco T x i = 0 ∧ ∀ j, j ≠ i → 0 < Tco T x j ↔ x ∈ open_hull (Tside T i) := by
  sorry

lemma boundary_is_union_sides {T : Triangle} (hdet : det T ≠ 0)
    : boundary T = ⋃ i, closed_hull (Tside T i) := by
  sorry

lemma segment_in_boundary_imp_in_side {T : Triangle} {L : Segment} (hdet : det T ≠ 0)
    (hL : closed_hull L ⊆ boundary T) : ∃ i, closed_hull L ⊆ closed_hull (Tside T i) := by
  sorry




-- Might not be necessary
def normal_vec (L : Segment) : ℝ² := fun | 0 => L 0 1 - L 1 1 | 1 => L 1 0 - L 0 0

def product_seg (L : Segment) (x : ℝ²) : ℝ := (x 0) * (L 0 1 - L 1 1) + (x 1) * (L 1 0 - L 0 0)

def reverse (L : Segment) : Segment := fun | 0 => L 1 | 1 => L 0

lemma formula_sign_seg (L : Segment) (x y : ℝ²) (a : ℝ) :
    sign_seg L (x + a • y) = (sign_seg L x) + a * (product_seg L y) := by
  simp [sign_seg, product_seg, det]; ring











def boundary_unit_square : Set ℝ² := unit_square \ open_unit_square

lemma segment_triangle_pairing_int (S : Finset Triangle) (hCover : is_cover unit_square S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ open_hull Psquare) (hv : ∀ i, ∀ Δ ∈ S, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 2 := sorry

lemma segment_triangle_pairing_boundary (S : Finset Triangle) (hCover : is_cover unit_square S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ boundary Psquare) (hv : ∀ i, ∀ Δ ∈ S, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 1 := sorry





/-
  Dions stuff

  For a collection of segments, we define the collection of basis segments.
  Next, we define what it means for a collection of segments to be complete,
  and we show that any segment in a complete collection is a union of basis segments.
-/

local notation "SegmentSet" => Finset Segment

variable (X : SegmentSet)

-- A basic segment is a segment that does not properly contain another segment
def IsBasic (S : Segment) : Prop :=
  S ∈ X ∧ ∀ T : X, closed_hull T.val ⊆ closed_hull S → closed_hull T.val = closed_hull S

-- A SegmentSet is complete if for any inclusions of segements, the closure of the complement
-- of a segment is also in the SegmentSet
def HasComplements : Prop :=
  ∀ S T : X, closed_hull S.val ⊂ closed_hull T.val → ∃ S' : X,
  (closed_hull T.val = closed_hull S.val ∪ closed_hull S'.val ∧
  ∃ p : ℝ², closed_hull S.val ∩ closed_hull S'.val = {p})

-- A decomposition of a segment is a collection of segments covering it
def IsCovering (S : Segment) (C : Finset Segment) : Prop :=
  closed_hull S = ⋃ (T ∈ C), closed_hull T

-- A SegmentSet is splitting if every segment is the union of the basic segments it contains.
def IsSplitting : Prop :=
  ∀ S ∈ X, ∃ C : Finset Segment, IsCovering S C ∧ ∀ T ∈ C, IsBasic X T

-- A SegmentSet is NonDegenerate if each segment is nondegenerate, meaning its not a point
def NonDegenerateSet : Prop :=
  ∀ S ∈ X, S 0 ≠ S 1

noncomputable def segment_midpoint (S : Segment) : ℝ² := ((1 : ℝ ) / (2 : ℝ)) • (S 0 + S 1)

-- Example: if X : Segment_Set is a singleton, its only member is a basis segment
lemma singleton_has_basis (S : Segment) : IsBasic (singleton S) S  := by
  refine ⟨mem_singleton.mpr rfl, ?_⟩
  intro T
  exact fun _ ↦ congrArg closed_hull (Set.mem_singleton_iff.1 (Set.mem_toFinset.mp T.2))

lemma smul_cancel' (a : ℝ) {b c : ℝ²} : a • b ≠ a • c → b ≠ c := by
  intro h
  exact fun a_1 ↦ h (congrArg (HSMul.hSMul a) a_1)


lemma downward_set_non_degenerate {Y : SegmentSet} (S : Segment) (h : S ∈ Y)
    (hND : NonDegenerateSet Y) : NonDegenerateSet {T ∈ Y | closed_hull T ⊆ closed_hull S} := by
  intro S₁ hS₁
  have h₁ : S₁ ∈ Y := mem_of_mem_filter S₁ hS₁
  exact hND S₁ h₁

lemma downward_set_complete {Y : SegmentSet} (S : Segment) (h : S ∈ Y)
    (hYCompl : HasComplements Y) : HasComplements {T ∈ Y | closed_hull T ⊆ closed_hull S} := by
  intro T T₁ hTT₁
  cases' hYCompl ⟨T.val, by aesop⟩ ⟨T₁.val, by aesop⟩ hTT₁ with S' hS'
  use ⟨S'.val, by aesop⟩

lemma downward_set_basic {Y : SegmentSet} {S T : Segment} (h : S ∈ Y)
    (hTS : closed_hull T ⊆ closed_hull S)
    (hbas : IsBasic {T' ∈ Y | closed_hull T' ⊆ closed_hull S} T) :
    IsBasic Y T := by
  refine ⟨mem_of_mem_filter T hbas.1, ?_⟩
  intro T₁ hT₁
  have h₁ : T₁.val ∈ filter (fun T' ↦ closed_hull T' ⊆ closed_hull S) Y := by
    rw [mem_filter]
    exact ⟨T₁.prop, by tauto⟩
  exact hbas.2 ⟨T₁.val, h₁⟩ hT₁

theorem complete_is_splitting: ∀ (X : SegmentSet), HasComplements X ∧ NonDegenerateSet X → IsSplitting X := by
  apply Finset.strongInduction
  intro Y hY hYCompl S hSY
  let YS : Finset Segment := {T ∈ Y | closed_hull T ⊆ closed_hull S}
  have hYSsubY : YS ⊆ Y := filter_subset (fun T ↦ closed_hull T ⊆ closed_hull S) Y
  have hSinYS : S ∈ YS := by
    rw [mem_filter]
    exact ⟨hSY, by rfl⟩
  have hYSComp : HasComplements YS ∧ NonDegenerateSet YS := by
    refine ⟨downward_set_complete S hSY hYCompl.1, ?_⟩
    intro S₁ hS₁
    exact downward_set_non_degenerate S hSY hYCompl.2 S₁ hS₁
  cases' ssubset_or_eq_of_subset hYSsubY with hstrict heq
  · -- Apply induction hypothesis
    specialize hY YS hstrict hYSComp
    rcases hY S hSinYS with ⟨C, ⟨hl, hr⟩⟩
    use C
    refine ⟨hl, ?_⟩
    intro T hT
    -- now need to prove that T is actually in YS to apply h.right
    have hTS : ↑T ∈ YS := by
      have hTinS : closed_hull T ⊆ closed_hull S := by
        calc closed_hull T ⊆ ⋃ (T ∈ C), closed_hull T := by exact Set.subset_biUnion_of_mem hT
          _ = closed_hull S := by rw [← hl]
      rw [mem_filter]
      exact ⟨hYSsubY (hr T hT).1, hTinS⟩
    refine ⟨hYSsubY (hr T hT).1, ?_⟩
    intro T' hT2
    have hT' : T'.val ∈ YS := by
      rw [mem_filter] at *
      exact ⟨T'.2, by tauto⟩
    exact (hr T hT).2 ⟨T'.val, hT'⟩ hT2
  · -- if S is basic, we are done. If not, choose something in S and use completeness to
    -- apply the induction hypothesis to two smaller sets.
    by_cases hSBasic : (IsBasic Y S)
    · use {S}
      refine ⟨Eq.symm (set_biUnion_singleton S closed_hull), ?_⟩
      intro T hT
      rw [mem_singleton] at hT
      rw [hT]
      exact hSBasic
    · -- Then need to take a complement of T and apply induction hypothesis to the two subsets
      -- of elements contained in T or its complement.
      have hT : ∃ T ∈ Y, closed_hull T ⊂ closed_hull S := by
        unfold IsBasic at hSBasic
        rw [Decidable.not_and_iff_or_not] at hSBasic
        cases' hSBasic with hl hr
        · tauto
        · rw [Decidable.not_forall] at hr
          cases' hr with T hT
          use T
          refine ⟨coe_mem T, ?_⟩
          rw [Mathlib.Tactic.PushNeg.not_implies_eq, ← Set.ssubset_iff_subset_ne] at hT
          exact hT
      cases' hT with T₁ hT₁
      have hComp : closed_hull T₁ ⊂ closed_hull S → ∃ S' : Y,
          (closed_hull S = closed_hull T₁ ∪ closed_hull S'.val ∧
          ∃ p : ℝ², closed_hull T₁ ∩ closed_hull S'.val = {p}) := hYCompl.1 ⟨T₁, hT₁.1⟩ ⟨S, hSY⟩
      specialize hComp hT₁.2
      cases' hComp with T₂ hT₂
      let YT₁ : Finset Segment := {U ∈ Y | closed_hull U ⊆ closed_hull T₁}
      let YT₂ : Finset Segment := {U ∈ Y | closed_hull U ⊆ closed_hull T₂.val}
      have hYTCompl : HasComplements YT₁ := downward_set_complete T₁ hT₁.1 hYCompl.1
      have hYT'Compl : HasComplements YT₂ := downward_set_complete T₂ T₂.prop hYCompl.1
      have hYTStrict : YT₁ ⊂ Y := by
        rw [ssubset_iff_subset_ne]
        refine ⟨filter_subset (fun U ↦ closed_hull U ⊆ closed_hull T₁) Y, ?_⟩
        intro h
        have h₂ : T₂.val ∉ YT₁ := by
          by_contra h'
          rw [mem_filter] at h'
          apply ssubset_irrefl (closed_hull S)
          calc closed_hull S = closed_hull T₁ ∪ closed_hull T₂.val := hT₂.1
            _⊆ closed_hull T₁ ∪ closed_hull T₁ := by exact Set.union_subset_union_right (closed_hull T₁) h'.2
            _= closed_hull T₁ := Set.union_eq_self_of_subset_left fun ⦃a⦄ a ↦ a
            _⊂ closed_hull S := hT₁.2
        rw [h] at h₂
        exact h₂ T₂.prop
      have hYT'Strict : YT₂ ⊂ Y := by
        rw [ssubset_iff_subset_ne]
        refine ⟨filter_subset (fun U ↦ closed_hull U ⊆ closed_hull T₂.val) Y, ?_⟩
        intro h
        rw [← h, mem_filter] at hT₁
        have h' : ¬(closed_hull T₁ ⊆  closed_hull T₂.val) := by
          intro h
          let x := segment_midpoint T₁
          have hT₁ND : T₁ 0 ≠ T₁ 1 := hYCompl.2 T₁ hT₁.1.1
          have hx : x ≠ T₁ 0 ∧ x ≠ T₁ 1 := by -- TODO: this may be good as a separate lemma
            unfold_let
            unfold segment_midpoint
            have hstupid (a : ℝ²) : (2 : ℝ) • a + (-1) • a = ((2 : ℝ) + (-1)) • a := by
              rw [add_smul]
              simp only [Fin.isValue, Int.reduceNeg, neg_smul, one_smul]
            constructor
            · apply (smul_cancel' 2)
              rw [← add_ne_add_left (- T₁ 0), ← neg_one_zsmul, hstupid]
              ring_nf
              simp only [one_div, Fin.isValue, smul_add, ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, smul_inv_smul₀, Int.reduceNeg, neg_smul, one_smul,
                add_neg_cancel_comm]
              intro hc
              symm at hc
              exact hT₁ND hc
            · apply (smul_cancel' 2)
              rw [← add_ne_add_left (- T₁ 1), ← neg_one_zsmul, hstupid]
              ring_nf
              simp only [one_div, Fin.isValue, smul_add, ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, smul_inv_smul₀, Int.reduceNeg, neg_smul, one_smul,
                add_neg_cancel_right]
              exact hT₁ND
          have hxT₁ : x ∈ closed_hull T₁ := by
            unfold closed_hull
            simp only [Fin.sum_univ_two, Fin.isValue, Set.mem_image]
            use fun i ↦ ((1 : ℝ) / (2 : ℝ))
            constructor
            · unfold closed_simplex
              simp only [Fin.sum_univ_two, Fin.isValue, one_div, Set.mem_setOf_eq, inv_nonneg,
                Nat.ofNat_nonneg, implies_true, true_and]
              ring
            · unfold_let
              unfold segment_midpoint
              rw [smul_add]
          have hx₂ : x ∉ closed_hull T₂.val := by
            by_contra hx₂
            cases' hT₂.2 with p hp
            have hxp : x = p := by
              rw [← Set.mem_singleton_iff, ← hp]
              exact ⟨hxT₁, hx₂⟩
            have hpT₁0 : p = T₁ 0 := by
              symm
              rw [← Set.mem_singleton_iff, ← hp]
              have hTT₁ : T₁ 0 ∈ closed_hull T₁ := by
                unfold closed_hull
                simp only [Fin.sum_univ_two, Fin.isValue, Set.mem_image]
                use fun i ↦ ((1 - i) : ℝ)
                constructor
                · unfold closed_simplex
                  simp only [Fin.sum_univ_two, Fin.isValue, Set.mem_setOf_eq, sub_nonneg,
                    Nat.cast_le_one, Fin.val_zero, CharP.cast_eq_zero, sub_zero, Fin.val_one,
                    Nat.cast_one, sub_self, add_zero, and_true]
                  intro i
                  exact Fin.is_le i
                · simp only [Fin.isValue, Fin.val_zero, CharP.cast_eq_zero, sub_zero, one_smul,
                  Fin.val_one, Nat.cast_one, sub_self, zero_smul, add_zero]
              exact ⟨hTT₁, h hTT₁⟩
            rw [hxp, hpT₁0] at hx
            tauto
          tauto
        tauto
      have hT₁YT₁ : T₁ ∈ YT₁ := by
        rw [mem_filter]
        exact ⟨hT₁.1, fun ⦃a⦄ a ↦ a⟩
      have hT₂YT₂ : T₂.val ∈ YT₂ := by
        rw [mem_filter]
        exact ⟨T₂.2, fun ⦃a⦄ a ↦ a⟩
      have hYT₁ND : NonDegenerateSet YT₁ := by
        intro S₁ hS₁
        exact downward_set_non_degenerate T₁ hT₁.1 hYCompl.2 S₁ hS₁
      have hYT₂ND : NonDegenerateSet YT₂ := by
        intro S₁ hS₁
        exact downward_set_non_degenerate T₂ T₂.prop hYCompl.2 S₁ hS₁
      cases' hY YT₁ hYTStrict ⟨hYTCompl, hYT₁ND⟩ T₁ hT₁YT₁ with CT₁ hCT₁
      cases' hY YT₂ hYT'Strict ⟨hYT'Compl, hYT₂ND⟩ T₂ hT₂YT₂ with CT₂ hCT₂
      use CT₁ ∪ CT₂
      constructor
      · calc closed_hull S = closed_hull T₁ ∪ closed_hull T₂.val := hT₂.1
          _ = closed_hull T₁ ∪ (⋃ (L' ∈ CT₂), closed_hull L') := by rw [hCT₂.1]
          _ = (⋃ (L ∈ CT₁), closed_hull L) ∪ (⋃ (L' ∈ CT₂), closed_hull L') := by rw [hCT₁.1]
          _ = ⋃ (L ∈ CT₁ ∪ CT₂), closed_hull L := Eq.symm (set_biUnion_union CT₁ CT₂ closed_hull)
      · rintro T
        rw [mem_union]
        rintro (hCT | hCT')
        · have h₁ : closed_hull T ⊆ closed_hull T₁ := by
            calc closed_hull T ⊆ ⋃ (L ∈ CT₁), closed_hull L := Set.subset_biUnion_of_mem hCT
              _ = closed_hull T₁ := by rw [← hCT₁.1]
          exact downward_set_basic hT₁.1 h₁ (hCT₁.2 T hCT)
        · have h₂ : closed_hull T ⊆ closed_hull T₂.val := by
            calc closed_hull T ⊆ ⋃ (L ∈ CT₂), closed_hull L := Set.subset_biUnion_of_mem hCT'
              _ = closed_hull T₂.val := by rw [← hCT₂.1]
          exact downward_set_basic T₂.2 h₂ (hCT₂.2 T hCT')

def NonDegenerate (S : Segment) := S 0 ≠ S 1

def NoDuplicates {n : ℕ} (T : Fin n → X) :=
    ∀ i j, i ≠ j → open_hull (T i).val ∩ open_hull (T j).val = ∅

theorem has_chains (S : X) (hX : IsSplitting X) (hS : NonDegenerate S) :
    ∃ n : ℕ, ∃ T : Fin (n + 1) → X, ∀ i, IsBasic X (T i).val ∧ NoDuplicates X T ∧
    ∀ i : Fin n, (T i).val 1 = (T (i + 1)).val 0 := by
  -- start with a covering of S by basis segments, need to find an ordering. Evident way:
  -- look at the order in which the points occur under the standard mapping [0,1] → closed_segment S
  -- We can use Finset.orderEmbOfFin to construct the map T
  sorry

variable (O : Type) [LinearOrder O]
example (A : Finset O) : ∃ n : ℕ, ∃ f : Fin n → O, f '' ⊤ = A ∧ ∀ i j : Fin n, i < j → f i < f j
  := by
  sorry -- Use Finset.orderEmbOfFin




/-
  Lenny's stuff
-/


/-
  First we import the definition and properties of the colouring.
  We assume 0 = red, 1 = blue, 2 = green
-/

section noncomputable

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

lemma purple_segments_parity (X : SegmentSet) (hX : HasComplements X)
  (L : X) (hL : IsPurple L) :
  (purple_segments X L.val).card % 2 = 1 := sorry

lemma grey_segments_parity (X : SegmentSet) (hX : HasComplements X)
  (L : X) (hL : ¬ IsPurple L) :
  (purple_segments X L.val).card % 2 = 0 := sorry



/-
  Now we assume given a dissection S. Write X for the set of all segments in the dissection
-/

variable (S : Finset Triangle) (hS : is_cover unit_square S)

def Y : SegmentSet := sorry
lemma hY : HasComplements Y := sorry
def B := {  L : Y | IsBasic Y L }

/-
  For any triangle in the dissection, the number of purple segments on its boundary
  is odd iff the triangle is rainbow
  TODO: probably should be 2 mod 4, given that segments are counted with
  both orientations
-/

def IsRainbow (T : Triangle) : Prop := Function.Surjective (color ∘ T)

lemma purple_odd_iff_rainbow (T : S) :
  (purple_segments Y (side T 0)).card + (purple_segments Y (side T 1)).card +
  (purple_segments Y (side T 2)).card % 2 = 1 ↔ IsRainbow T := sorry


/-
  Main goal for our group:
-/

theorem monsky_rainbow  :
    ∃ T ∈ S, IsRainbow T := sorry
