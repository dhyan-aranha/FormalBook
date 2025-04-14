import Mathlib
import Mathlib.Tactic

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical
open Finset


-- Shorthand for defining an element of ℝ²
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


-- Definition of an n-dimensional standard simplex.
def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

/-
  The Fin n → ℝ² in the following definitions represents the vertices of a polygon.
  Beware: Whenever the n vertices do not define an n-gon, i.e. a vertex lies within the
  convex hull of the others, the open_hull does not give the topological interior of the closed
  hull.

  Also when f i = P for all i, both the closed_hull and open_hull are {P i}.
-/
def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n


/- Corner of the standard simplex.-/
def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} : simplex_vertex i ∈ closed_simplex n := by
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp [simplex_vertex, h], by simp [simplex_vertex]⟩

lemma closed_simplex_zero_empty : closed_simplex 0 = ∅ := by
  unfold closed_simplex
  simp only [IsEmpty.forall_iff, univ_eq_empty, sum_empty, zero_ne_one, and_false, Set.setOf_false]

lemma open_simplex_zero_empty : open_simplex 0 = ∅ := by
  unfold open_simplex
  simp only [IsEmpty.forall_iff, univ_eq_empty, sum_empty, zero_ne_one, and_false, Set.setOf_false]

@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by simp [simplex_vertex]

@[simp]
lemma corner_in_closed_hull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ closed_hull P := by
  exact ⟨simplex_vertex i, simplex_vertex_in_simplex, by simp⟩

lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext _
  constructor
  · intro ⟨_, hα, hαv⟩
    simp [←hαv, ←sum_smul, hα.2, one_smul, Set.mem_singleton_iff]
  · intro hv; rw [hv]
    exact corner_in_closed_hull (i := ⟨0, Nat.zero_lt_of_ne_zero hn⟩)

lemma closed_hull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (hc : closed_hull f = {P}) : ∀ i, f i = P := by
  simp_rw [←Set.mem_singleton_iff, ←hc]
  exact fun _ ↦ corner_in_closed_hull


lemma open_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : ∃ x, x ∈ open_hull P := by
  use ∑ i, (1/(n : ℝ)) • P i, fun _ ↦ (1/(n : ℝ))
  exact ⟨⟨fun _ ↦ by simp [hn], by simp; exact (mul_inv_cancel₀ (by simp; linarith))⟩, by simp⟩

lemma open_sub_closed_simplex {n : ℕ} : open_simplex n ⊆ closed_simplex n :=
  fun _ ⟨hαpos, hαsum⟩ ↦ ⟨fun i ↦ by linarith [hαpos i], hαsum⟩

lemma open_sub_closed {n : ℕ} (P : Fin n → ℝ²) : open_hull P ⊆ closed_hull P :=
  Set.image_mono open_sub_closed_simplex

lemma open_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    open_hull (fun (_ : Fin n) ↦ P) = {P} :=
  (Set.Nonempty.subset_singleton_iff (open_pol_nonempty (Nat.zero_lt_of_ne_zero hn) _)).mp
      (subset_of_subset_of_eq (open_sub_closed _) (closed_hull_constant hn))

lemma closed_hull_zero_dim (f : Fin 0 → ℝ²) : closed_hull f = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x ⟨_,⟨_,h⟩,_⟩
  simp only [univ_eq_empty, sum_empty, zero_ne_one] at h

lemma open_hull_zero_dim (f : Fin 0 → ℝ²) : open_hull f = ∅ := by
  rw [←Set.subset_empty_iff]
  exact subset_of_subset_of_eq (open_sub_closed f) (closed_hull_zero_dim f)



lemma open_hull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (ho : open_hull f = {P}) : ∀ i, f i = P :=  by
  cases' eq_or_ne 0 n with hz hn
  · intro i
    subst hz
    by_contra h
    unfold open_hull at ho
    rw [open_simplex_zero_empty] at ho
    simp only [univ_eq_empty, sum_empty, Set.image_empty] at ho
    symm at ho
    exact Set.singleton_ne_empty P ho
  · by_contra hc; push_neg at hc
    cases' hc with j hj
    have hi : ∃ i, f i ≠ f j := by
      by_contra hi
      simp only [ne_eq, not_exists, Decidable.not_not] at hi
      have h_hull : open_hull f = {f j} := by
        have hf : f = fun x ↦ f j := by
          ext x
          rw [hi x]
        rw [hf]
        exact open_hull_constant hn.symm
      simp_all only [Set.singleton_eq_singleton_iff]
    cases' hi with i hi
    have hP : P ∈ open_hull f := by
      simp_all only [ne_eq, Set.mem_singleton_iff]
    unfold open_hull at hP
    rw [Set.mem_image] at hP
    cases' hP with α hα
    let α' := fun (k : Fin n) ↦ if k ≠ i ∧ k ≠ j then 0 else (
      if k = i then ((α j) / 2) else -((α j) / 2)
    )
    let β := α + α'
    let Q := ∑ i : Fin n, β i • f i
    have hQP : Q ≠ P := by
      sorry
    have hQ : Q ∈ open_hull f := by
      sorry
    tauto_set



noncomputable def linear_combination {n : ℕ} (α : Fin n → ℝ) (f : Fin n → ℝ²)
    : ℝ² := ∑ i, α i • f i

lemma linear_co_closed {n : ℕ} {α : Fin n → ℝ} (f : Fin n → ℝ²) (h : α ∈ closed_simplex n) :
    linear_combination α f ∈ closed_hull f := ⟨α, h, by rfl⟩




/- Implications of the requirements that (∀ i, 0 ≤ α i),  ∑ i, α i = 1. -/

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


lemma simplex_co_leq_1_open {n : ℕ} {α : Fin n → ℝ} (hn : 1 < n)
    (h₁ : α ∈ open_simplex n) : ∀ i, α i < 1 := by
  intro i
  apply lt_of_le_of_ne (simplex_co_leq_1 (open_sub_closed_simplex h₁) i)
  intro hα
  have hj : ∃ j, i ≠ j := by
    by_cases hs : i = ⟨0, by linarith⟩
    · use ⟨1, by linarith⟩
      simp [hs]
    · use ⟨0, by linarith⟩
  have ⟨j, hj⟩ := hj
  linarith [h₁.1 j, simplex_co_eq_1 (open_sub_closed_simplex h₁) hα j hj.symm]

/- Some lemmas specifically about Fin 2 → ℝ. -/

lemma simplex_closed_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ closed_simplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) := by
    intro i;
    rw [←h.2, Fin.sum_univ_two]
    fin_cases i <;> simp

lemma simplex_open_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ open_simplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) :=
  simplex_closed_sub_fin2 (open_sub_closed_simplex h)

def real_to_fin_2 (x : ℝ) : (Fin 2 → ℝ) := fun | 0 => x | 1 => 1 - x

lemma real_to_fin_2_closed {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 1)
    : real_to_fin_2 x ∈ closed_simplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp [real_to_fin_2]; assumption), by simp [real_to_fin_2]⟩

lemma real_to_fin_2_open {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1)
    : real_to_fin_2 x ∈ open_simplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp [real_to_fin_2]; assumption), by simp [real_to_fin_2]⟩




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



/-
  We define the boundary of a polygon as the elements in the closed hull but not
  in the open hull.
-/

def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closed_hull P) \ (open_hull P)

lemma boundary_sub_closed {n : ℕ} (P : Fin n → ℝ²) : boundary P ⊆ closed_hull P :=
  Set.diff_subset

lemma boundary_not_in_open {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∉ open_hull P :=  Set.not_mem_of_mem_diff hx

lemma boundary_in_closed {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∈ closed_hull P := Set.mem_of_mem_diff hx

lemma boundary_int_open_empty {n : ℕ} {P : Fin n → ℝ²} : boundary P ∩ open_hull P = ∅ :=
  Set.diff_inter_self

lemma boundary_open_disjoint {n : ℕ} {P : Fin n → ℝ²} : Disjoint (boundary P) (open_hull P) :=
  Set.disjoint_iff_inter_eq_empty.mpr boundary_int_open_empty

lemma boundary_union_open_closed {n : ℕ} {P : Fin n → ℝ²} :
    boundary P ∪ open_hull P = closed_hull P := Set.diff_union_of_subset (open_sub_closed P)

lemma open_closed_hull_minus_boundary {n : ℕ} {P : Fin n → ℝ²} :
    closed_hull P \ boundary P = open_hull P := by
  simp [boundary, open_sub_closed]

lemma boundary_constant {n : ℕ} {P : ℝ²} :
    boundary (fun (_ : Fin n) ↦ P) = ∅ := by
  cases' (ne_or_eq n 0) with hn hz
  · unfold boundary
    rw [open_hull_constant hn, closed_hull_constant hn]
    simp only [sdiff_self, Set.bot_eq_empty]
  · unfold boundary
    unfold closed_hull
    rw [hz]
    rw [closed_simplex_zero_empty]
    simp only [univ_eq_empty, sum_empty, Set.image_empty, Set.empty_diff]
