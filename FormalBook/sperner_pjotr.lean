import Mathlib
import Mathlib.Tactic


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
  (X = ⋃ (Δ ∈ S), closed_hull Δ) ∧
  (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, Δ₁ ≠ Δ₂ → Disjoint (open_hull Δ₁) (open_hull Δ₂))

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)




/- Should we doe this or not? -/
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

def Psquare : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

def unit_square : Set ℝ² := closed_hull Psquare

def open_unit_square : Set ℝ² := open_hull Psquare


theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  sorry




@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


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

@[simp]
lemma corner_in_closed_hull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ closed_hull P := by
  exact ⟨simplex_vertex i, simplex_vertex_in_simplex, by simp⟩

lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext v
  constructor
  · intro ⟨α, hα,hαv⟩
    simp [←sum_smul, hα.2] at hαv
    exact hαv.symm
  · intro hv
    rw [hv]
    exact corner_in_closed_hull (i := ⟨0,Nat.zero_lt_of_ne_zero hn⟩)


lemma open_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : ∃ x, x ∈ open_hull P := by
  use ∑ i, (1/(n : ℝ)) • P i, fun _ ↦ (1/(n : ℝ))
  exact ⟨⟨fun _ ↦ by simp [hn], by simp; exact (mul_inv_cancel₀ (by simp; linarith))⟩, by simp⟩

lemma open_seg_nonempty (L : Segment) : ∃ x, x ∈ open_hull L :=
  open_pol_nonempty (by linarith) L

-- Cleaner to first prove open_simplex ⊆ closed_simplex.
lemma open_sub_closed {n : ℕ} (P : Fin n → ℝ²) : open_hull P ⊆ closed_hull P :=
  fun _ ⟨α,hαx,hx⟩ ↦ ⟨α,⟨⟨fun i ↦ by linarith [hαx.1 i],hαx.2⟩,hx⟩⟩

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


lemma open_segment_sub {L₁ L₂ : Segment} (hsub: ∀ i : Fin 2, L₁ i ∈ closed_hull L₂) (hL₁ : L₁ 0 ≠ L₁ 1) :
    open_hull L₁ ⊆ open_hull L₂ := by
  intro x ⟨α,hα,hx⟩
  refine (Set.mem_image (fun α ↦ ∑ i : Fin 2, α i • L₂ i) (open_simplex 2) x).mpr ?_
  have h1: ∃ α₁ ∈ closed_simplex 2, L₁ 0 = ∑ i : Fin 2, α₁ i • L₂ i := by
    rcases hsub 0 with ⟨β, hβ₁, β₁₀⟩
    have h1': (fun α ↦ ∑ i : Fin 2, α i • L₂ i) β = ∑ i : Fin 2, β i • L₂ i := by
      simp only [Fin.sum_univ_two, Fin.isValue]
    have h1'': ∑ i : Fin 2, β i • L₂ i = L₁ 0 := by
      rw [←h1']
      exact β₁₀
    use β
    constructor
    · apply hβ₁
    · exact h1''.symm
  have h2: ∃ α₂ ∈ closed_simplex 2, L₁ 1 = ∑ i : Fin 2, α₂ i • L₂ i := by
    rcases hsub 1 with ⟨β, hβ₁, β₁₀⟩
    have h2': (fun α ↦ ∑ i : Fin 2, α i • L₂ i) β = ∑ i : Fin 2, β i • L₂ i := by
      simp only [Fin.sum_univ_two, Fin.isValue]
    have h2'': ∑ i : Fin 2, β i • L₂ i = L₁ 1 := by
      rw [←h2']
      exact β₁₀
    use β
    constructor
    · apply hβ₁
    · exact h2''.symm
  rcases h1 with ⟨α₁,hα₁,hL₁₀⟩
  rcases h2 with ⟨α₂,hα₂,hL₁₁⟩
  have pos : ∀ i, 0 < α i := by
    apply hα.1
  have pos1 : ∀ i, 0 ≤  α₁ i := by
    apply hα₁.1
  have pos2 : ∀ i, 0 ≤ α₂ i := by
    apply hα₂.1
  let x₁ : Fin 2 → ℝ := fun i => match i with
    | 0 => (α 0 * α₁ 0 + α 1 * α₂ 0)
    | 1 => (α 0 * α₁ 1 + α 1 * α₂ 1)
  have hαx₁ : x₁ ∈ open_simplex 2 := by
    constructor
    have x₁0_pos : x₁ 0 > 0 := by
      simp [x₁, pos, pos1, pos2]
      by_contra h
      simp at h
      have p : α₁ 0 = 0 := by
        by_contra hα₁0
        have p' : α 0 * α₁ 0 + α 1 * α₂ 0 > 0 := by
          simp only [add_pos_of_pos_of_nonneg,mul_pos (pos 0),lt_of_le_of_ne (pos1 0) (Ne.symm hα₁0),
          mul_nonneg (pos 1).le (hα₂.1 0)]
        linarith [p', h]
      have q : α₂ 0 = 0 := by
          by_contra hα₂0
          have q' : α 0 * α₁ 0 + α 1 * α₂ 0 > 0 := by
            simp only [add_pos_of_nonneg_of_pos, mul_nonneg (pos 0).le (hα₁.1 0), mul_pos (pos 1),
            lt_of_le_of_ne (pos2 0) (Ne.symm hα₂0)]
          linarith [q', h]
      have r : α₁ 1 = 1 := by
        by_contra
        rcases hα₁ with ⟨_,hα₁₂⟩
        rw [Fin.sum_univ_two, p, zero_add] at hα₁₂
        contradiction
      have  s : α₂ 1 = 1 := by
        by_contra
        rcases hα₂ with ⟨_,hα₂₂⟩
        rw [Fin.sum_univ_two, q, zero_add] at hα₂₂
        contradiction
      simp [p,q,r,s] at hL₁₀ hL₁₁
      rw [← hL₁₁] at hL₁₀
      absurd hL₁
      exact hL₁₀
    have x₁1_pos : x₁ 1 > 0 := by
      simp [x₁, pos, pos1, pos2]
      by_contra h
      simp only [Fin.isValue, not_lt] at h
      have t : α₁ 1 = 0 := by
        by_contra hα₁0
        have t' : α 0 * α₁ 1 + α 1 * α₂ 1 > 0 := by
          simp only [add_pos_of_pos_of_nonneg,mul_pos (pos 0),lt_of_le_of_ne (pos1 1) (Ne.symm hα₁0),
          mul_nonneg (pos 1).le (hα₂.1 1)]
        linarith [t', h]
      have u : α₂ 1 = 0 := by
          by_contra hα₂0
          have u' : α 0 * α₁ 1 + α 1 * α₂ 1 > 0 := by
            simp only [add_pos_of_nonneg_of_pos, mul_nonneg (pos 0).le (hα₁.1 1), mul_pos (pos 1),
            lt_of_le_of_ne (pos2 1) (Ne.symm hα₂0)]
          linarith [u', h]
      have v : α₁ 0 = 1 := by
        by_contra
        rcases hα₁ with ⟨_,hα₁₂⟩
        rw [Fin.sum_univ_two, t, add_zero] at hα₁₂
        contradiction
      have  w : α₂ 0 = 1 := by
        by_contra
        rcases hα₂ with ⟨_,hα₂₂⟩
        rw [Fin.sum_univ_two, u, add_zero] at hα₂₂
        contradiction
      simp [t,u,v,w] at hL₁₀ hL₁₁
      rw [← hL₁₁] at hL₁₀
      absurd hL₁
      exact hL₁₀

    · exact fun i ↦ by
        fin_cases i
        all_goals (simp [x₁, x₁0_pos, x₁1_pos, pos, pos1, pos2])
    · simp only [x₁, hα.2, hα₁.2, hα₂.2]
      rcases hα with ⟨_,h₂⟩
      rcases hα₁ with ⟨hα₁₁,hα₁₂⟩
      rcases hα₂ with ⟨hα₂₁,hα₂₂⟩
      simp [← add_assoc, add_comm, ← mul_add, add_assoc]
      rw [Fin.sum_univ_two] at hα₁₂ hα₂₂ h₂
      calc
        α 0 * α₁ 0 + (α 1 * α₂ 0 + (α 0 * α₁ 1 + α 1 * α₂ 1)) = α 0 * (α₁ 0 + α₁ 1) + α 1 * (α₂ 0 + α₂ 1) := by ring
        _ = 1 := by simp [hα₁₂,hα₂₂, mul_one, mul_one, h₂]
  use x₁
  constructor
  · exact hαx₁
  · simp only [Fin.sum_univ_two, Fin.isValue, hL₁₀, smul_add, hL₁₁, ← add_assoc, add_comm] at hx
    simp only [Fin.isValue, Fin.sum_univ_two, add_smul, mul_smul, ← add_assoc, x₁]
    exact hx


lemma open_segment_sub' {L₁ L₂ : Segment} (hsub: closed_hull L₁ ⊆ closed_hull L₂)
    (hL₁ : L₁ 0 ≠ L₁ 1) : open_hull L₁ ⊆ open_hull L₂ :=
  open_segment_sub (fun _ ↦ (hsub corner_in_closed_hull)) hL₁


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

/- Basic lemmas about Real.sign. -/
lemma real_sign_mul {x y : ℝ} : Real.sign (x * y) = Real.sign x * Real.sign y := by
  obtain (hx | hx | hx) := lt_trichotomy x 0
  · calc
      (x * y).sign  = (-((-x) * y)).sign  := by congr; ring
      _             = - ((-x) * y).sign   := by rw [Real.sign_neg]
      _             = - y.sign            := by congr 1; exact sign_mul_pos (by linarith)
      _             = (-1) * y.sign       := by ring
      _             = x.sign * y.sign     := by congr; exact (Real.sign_of_neg hx).symm
  · rw [hx, zero_mul, Real.sign_zero, zero_mul]
  · rw [sign_mul_pos hx, Real.sign_of_pos hx, one_mul]

lemma real_sign_involution {x : ℝ} : x.sign.sign = x.sign := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> (
  · rw [hx, Real.sign]
    simp
  )

lemma real_sign_div_self {x : ℝ} (hx : x ≠ 0) : 0 <  Real.sign x / x :=
  sign_div_pos hx real_sign_involution

lemma real_sign_mul_self {x : ℝ} (hx : x ≠ 0) : 0 < (Real.sign x) * x := by
  obtain (hx' | hx') := Real.sign_apply_eq_of_ne_zero x hx <;> rw [hx']
  · simp [sign_neg' hx']
  · simp [sign_pos' hx']

lemma real_sign_abs_le {x : ℝ} : |Real.sign x| ≤ 1 := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> simp [hx]

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




/-
  Better I think to just define the determinant.
-/

def det (T : Triangle) : ℝ
  := (T 0 1 - T 1 1) * (T 2 0) + (T 1 0 - T 0 0) * (T 2 1) + ((T 0 0) * (T 1 1) - (T 1 0) * (T 0 1))

lemma triangle_area_det {T : Triangle} : triangle_area T = |det T|/2 := by
  simp [triangle_area,det]
  congr 2; ring

lemma area_nonzero_iff_det_nonzero {T : Triangle}
    : triangle_area T ≠ 0 ↔ det T ≠ 0 := by
  constructor
  · intro h₁ h₂
    rw [triangle_area_det, h₂, abs_zero, zero_div] at h₁
    exact h₁ rfl
  · intro h₁ h₂
    rw [triangle_area_det, div_eq_zero_iff, abs_eq_zero] at h₂
    cases' h₂ with h₂ _
    · exact h₁ h₂
    · linarith

lemma linear_combination_det_last {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => y | 2 => (∑ i, α i • P i)) =
  ∑ i, (α i * det (fun | 0 => x | 1 => y | 2 => (P i))) := by
  simp [det, left_distrib, sum_add_distrib, sum_apply _, mul_sum, ←sum_mul, hα]
  congr <;> (ext; ring)




def sign_seg (L : Segment) (v : ℝ²) : ℝ := det (fun | 0 => L 0 | 1 => L 1 | 2 => v)


lemma sign_seg_mem_zero (L : Segment) {v : ℝ²} (hv : v ∈ closed_hull L) :
    sign_seg L v = 0 := by
  sorry



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

lemma two_co_zero_imp_corner_co {T : Triangle} {i j : Fin 3} {x : ℝ²} (hdet : det T ≠ 0)
    (hij : i ≠ j) (hi : Tco T x i = 0) (hj : Tco T x j = 0) :
    Tco T x (last_index i j) =  1 := by
  rw [←Tco_sum hdet x, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all [last_index]

lemma two_co_zero_imp_corner {T : Triangle} {i j : Fin 3} {x : ℝ²} (hdet : det T ≠ 0)
  (hij : i ≠ j) (hi : Tco T x i = 0) (hj : Tco T x j = 0) :
    x = T (last_index i j) := by
  have hk := two_co_zero_imp_corner_co hdet hij hi hj
  rw [←Tco_sum_self hdet x, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all [last_index]




def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closed_hull P) \ (open_hull P)

lemma boundary_sub_closed {n : ℕ} (P : Fin n → ℝ²) : boundary P ⊆ closed_hull P :=
  Set.diff_subset

lemma boundary_not_in_open {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∉ open_hull P :=  Set.not_mem_of_mem_diff hx

lemma boundary_in_closed {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∈ closed_hull P := Set.mem_of_mem_diff hx

lemma boundary_seg {L : Segment} (hL : L 0 ≠ L 1)
    : boundary L = image (fun i ↦ L i) (univ : Finset (Fin 2)) := by
  ext x
  constructor
  · intro hx
    have ⟨α,hα,hαx⟩ := boundary_in_closed hx
    have α_non_zero : ∃ i, α i = 0 := by
      by_contra hcontra; push_neg at hcontra
      apply boundary_not_in_open hx
      exact ⟨α,⟨fun i ↦ lt_of_le_of_ne (hα.1 i) (hcontra i).symm,hα.2⟩ ,hαx⟩
    sorry
  · sorry

/- To make the boundary_seg more useful.-/
lemma fin2_im {α : Type} {f : Fin 2 → α}
    : image f (univ : Finset (Fin 2)) = {f 0, f 1} := by
  ext
  simp
  constructor
  · intro ⟨j, g⟩
    fin_cases j
    · left; exact g.symm
    · right; exact g.symm
  · exact fun h ↦ by cases' h with h h <;> exact ⟨_, h.symm⟩

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

lemma nondegen_triangle_imp_nondegen_side {T : Triangle} (i : Fin 3) (hdet : det T ≠ 0):
    Tside T i 0 ≠ Tside T i 1 :=
  fun hS ↦ hdet (by fin_cases i <;> (simp [Tside] at hS; simp [det, hS]) <;> ring)

lemma mem_closed_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3) :
    Tco T x i = 0 ↔ x ∈ closed_hull (Tside T i) := by
  constructor
  · intro hTco
    use (fun | 0 => Tco T x (i + 1) | 1 => Tco T x (i + 2))
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun j ↦ by fin_cases j <;> exact (closed_triangle_iff hdet).1 hx _
    · simp_rw [←Tco_sum hdet x, Fin.sum_univ_three, Fin.sum_univ_two]
      fin_cases i <;> (simp [hTco, add_comm] at *)
    · nth_rw 3 [←Tco_sum_self hdet x]
      fin_cases i <;> (simp [Fin.sum_univ_three, hTco, Tside, add_comm] at *)
  · intro ⟨α, hα, hαx⟩
    rw [←hαx, Tco_linear hα.2]
    fin_cases i <;> (simp [Tside, Tco_basis_off_diag])

lemma closed_side_sub {T : Triangle} {x : ℝ²} {i : Fin 3} (hx : x ∈ closed_hull (Tside T i)) :
    x ∈ closed_hull T := by
  refine closed_hull_convex ?_ hx
  intro j
  fin_cases i <;> fin_cases j <;> simp [Tside, simplex_vertex_in_simplex]

lemma closed_side_sub' {T : Triangle} {i : Fin 3} :
    closed_hull (Tside T i) ⊆ closed_hull T := fun _ ↦ closed_side_sub

lemma closed_side_to_co {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} {i : Fin 3} (hx : x ∈ closed_hull (Tside T i)) :
    Tco T x i = 0 := (mem_closed_side hdet (closed_side_sub hx) _).2 hx

lemma mem_open_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3) :
    (Tco T x i = 0 ∧ ∀ j, j ≠ i → 0 < Tco T x j) ↔ x ∈ open_hull (Tside T i) := by
  constructor
  · intro ⟨hTco, hall⟩
    -- This is basically the same proof as the closed version.
    use (fun | 0 => Tco T x (i + 1) | 1 => Tco T x (i + 2))
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun j ↦ by fin_cases j <;> simp [hall]
    · simp_rw [←Tco_sum hdet x, Fin.sum_univ_three, Fin.sum_univ_two]
      fin_cases i <;> (simp [hTco, add_comm] at *)
    · nth_rw 3 [←Tco_sum_self hdet x]
      fin_cases i <;> (simp [Fin.sum_univ_three, hTco, Tside, add_comm] at *)
  · intro hxOpen
    have hTcoi : Tco T x i = 0 := by
      rw [mem_closed_side hdet hx]
      exact open_sub_closed _ hxOpen
    refine ⟨hTcoi, ?_⟩
    by_contra hEx;
    push_neg at hEx
    have ⟨j,hjneq,hTcoj'⟩ := hEx
    have hTcoj : Tco T x j = 0 := by
      linarith [hTcoj', (closed_triangle_iff hdet).1 hx j]
    refine boundary_not_in_open (P := Tside T i) ?_ hxOpen
    rw [boundary_seg (nondegen_triangle_imp_nondegen_side i hdet), fin2_im, two_co_zero_imp_corner hdet hjneq hTcoj hTcoi]
    simp
    fin_cases i <;> fin_cases j <;> tauto

lemma mem_open_side_other_co {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²}  {i : Fin 3} (hxOpen : x ∈ open_hull (Tside T i))
  : ∀ j, j ≠ i → 0 < Tco T x j := by
  rw [←(mem_open_side hdet (closed_side_sub (open_sub_closed _ hxOpen)))] at hxOpen
  exact hxOpen.2

lemma side_in_boundary {T : Triangle} (hdet : det T ≠ 0) (i : Fin 3) :
    closed_hull (Tside T i) ⊆ boundary T := by
  intro x hx
  rw [boundary_iff hdet (closed_side_sub hx)]
  exact ⟨i, closed_side_to_co hdet hx⟩

lemma boundary_is_union_sides {T : Triangle} (hdet : det T ≠ 0)
    : boundary T = ⋃ i, closed_hull (Tside T i) := by
  ext x
  constructor
  · intro hx
    have ⟨i,_⟩ := (boundary_iff hdet (Set.mem_of_mem_diff hx)).1 hx
    exact Set.mem_iUnion.mpr ⟨i, by rwa [←mem_closed_side hdet (Set.mem_of_mem_diff hx) i]⟩
  · intro hx
    have ⟨_,hx⟩ := Set.mem_iUnion.1 hx
    exact side_in_boundary hdet _ hx

lemma el_boundary_imp_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ boundary T)
    : ∃ i, x ∈ closed_hull (Tside T i) := by
  rw [boundary_is_union_sides hdet] at hx
  exact Set.mem_iUnion.mp hx


lemma el_in_boundary_imp_side {T : Triangle} {x : ℝ²} (hdet : det T ≠ 0)
    (hx : x ∈ boundary T) (hv : ∀ i, x ≠ T i) : ∃ i, x ∈ open_hull (Tside T i) := by
  have hxClosed := (Set.mem_of_mem_diff hx)
  have ⟨i,hi⟩ := (boundary_iff hdet hxClosed).1 hx
  use i
  rw [←mem_open_side hdet hxClosed]
  refine ⟨hi,?_⟩
  intro j hji
  by_contra hj
  apply hv (last_index j i)
  refine two_co_zero_imp_corner hdet hji  ?_ hi
  linarith [hj, (closed_triangle_iff hdet).1 hxClosed j]



def det₂ (x y : ℝ²) : ℝ := x 0 * y 1 - x 1 * y 0

lemma det₂_iff (x y : ℝ²) (hx : x ≠ 0)
  : det₂ x y = 0 ↔ ∃ (α : ℝ), y = α • x := by
  constructor
  · intro h
    have hi : ∃ i, x i ≠ 0 := by
      by_contra hall
      push_neg at hall
      refine hx ?_
      ext i
      rw [hall i, PiLp.zero_apply]
    have ⟨i,hi⟩ := hi
    use y i / x i
    ext j
    unfold det₂ at h
    rw [sub_eq_zero] at h
    fin_cases i <;> fin_cases j <;> simp_all
    · have ht : y 1 = (x 1 * y 0) / x 0 := by
        rw [←h, mul_comm]
        exact Eq.symm (mul_div_cancel_right₀ (y 1) hi)
      rw [ht]
      field_simp; linarith
    · have ht : y 0 = (x 0 * y 1) / x 1 := by
        rw [h, mul_comm]
        exact Eq.symm (mul_div_cancel_right₀ (y 0) hi)
      rw [ht]
      field_simp; linarith
  · intro ⟨α,hα⟩
    simp_rw [hα,det₂,PiLp.smul_apply, smul_eq_mul]
    ring

lemma det₂_mul_last {x y : ℝ²} (a : ℝ)
  : det₂ x (a • y) = a * det₂ x y := by
  simp [det₂]; ring

noncomputable def seg_vec (L : Segment) : ℝ² := L 1 - L 0
noncomputable def Oside (T : Triangle) (i : Fin 3) := seg_vec (Tside T i)

-- Might not be necessary
def normal_vec (L : Segment) : ℝ² := fun | 0 => L 0 1 - L 1 1 | 1 => L 1 0 - L 0 0

lemma seg_vec_co {L : Segment} {x y : ℝ²} (hx : x ∈ closed_hull L) (hy : y ∈ closed_hull L)
  : ∃ a : ℝ, y = x + a • seg_vec L := by

  sorry

lemma sign_seg_line (L : Segment) (x y : ℝ²) (a : ℝ) :
    sign_seg L (x + a • y) = (sign_seg L x) + a * (det₂ (seg_vec L) y) := by
  simp [sign_seg, det₂, det, seg_vec]; ring

example {a b : ℝ} : a - b = 0 ↔ a = b := by
  exact sub_eq_zero

lemma seg_vec_zero_iff (L : Segment) : seg_vec L = 0 ↔ L 0 = L 1 := by
  rw [seg_vec, sub_eq_zero]
  exact eq_comm

lemma Tco_line {T : Triangle} {i : Fin 3} (x y : ℝ²) (a : ℝ) :
    Tco T (x  + a • y) i = Tco T x i + a * (det₂ (Oside T i) y) / det T := by
  rw [Tco, sign_seg_line, add_div, ←Tco, ←Oside]


/- Some API to make the seg_inter_open statement more pleasant.-/
/- This lemma is in mathlib but somehow I cannot get it to work unless it is in this form. -/
lemma forall_in_swap_special {α β : Type} {P : α → β → Prop} {Q : α → Prop} :
    (∀ a, Q a → ∀ b, P a b) ↔ (∀ b, ∀ a, Q a → P a b) :=
  Set.forall_in_swap


lemma forall_exists_pos_swap {α : Type} [Fintype α] {P : ℝ → α → Prop}
    (h : ∀ δ a, P δ a → ∀ δ', δ' ≤ δ → P δ' a): (∃ δ > 0, ∀ a, P δ a) ↔ (∀ a, ∃ δ > 0, P δ a) := by
  constructor
  · exact fun ⟨δ,Qδ,Pδ⟩ a ↦ ⟨δ, Qδ, Pδ a⟩
  · intro ha
    by_cases hα : Nonempty α
    · choose fδ hfδ using ha
      have hS : (image fδ univ).Nonempty := by rwa [image_nonempty, univ_nonempty_iff]
      use min' (image fδ univ) hS
      refine ⟨?_,?_⟩
      · rw [gt_iff_lt, Finset.lt_min'_iff]
        intro y hy
        have ⟨x,_,hx⟩ := mem_image.1 hy
        rw [←hx]
        exact (hfδ x).1
      · intro x
        apply h (fδ x) x (hfδ x).2
        exact min'_le _ _ (mem_image_of_mem fδ (mem_univ x))
    · simp_all only [gt_iff_lt, not_nonempty_iff, IsEmpty.forall_iff, and_true, implies_true]
      use 1
      norm_num

def real_interval_δ {x: ℝ} (y : ℝ) (hx : 0 < x) : ∃ δ > 0, ∀ a, |a| ≤ δ → 0 < x + a * y := by
  by_cases hy : y = 0
  · exact ⟨1, by norm_num, fun a _ ↦ by rwa [hy,mul_zero,add_zero]⟩
  · use x / (2 * |y|)
    constructor
    · field_simp
      assumption
    · intro a ha
      calc
        0     <   (1/2) * x       := by linarith
        _     =   x + (- (1/2)*x) := by linarith
        _     ≤   x + a * y       := by
          gcongr x + ?_
          field_simp
          rw [←neg_le_neg_iff, ←mul_le_mul_left (a := 2) (by norm_num), neg_div',neg_neg,
              mul_div_cancel₀ _ (by norm_num)]
          refine le_of_max_le_left (?_ : |2 * -(a * y)| ≤ x)
          rw [abs_mul,Nat.abs_ofNat, abs_neg, abs_mul,mul_comm,mul_assoc]
          nth_rw 2 [mul_comm]
          refine (le_div_iff₀ ?_).mp ha
          simp_all only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, abs_pos, ne_eq, not_false_eq_true]


lemma seg_inter_open {T : Triangle} {x y : ℝ²} {i : Fin 3}
  (hxT : x ∈ open_hull (Tside T i)) (hdet: det T ≠ 0)
  (hdet₂ : det₂ (seg_vec (Tside T i)) y ≠ 0) :
  ∃ σ ∈ ({-1,1} : Finset ℝ), (∃ δ > 0, (∀ a : ℝ,
    (0 < a → a ≤ δ → x + a • σ • y ∈ open_hull T))) ∧ ∀ a : ℝ, 0 < a → x + a • (- σ) • y ∉ closed_hull T := by
  use Real.sign (det T * det₂ (Oside T i) y)
  constructor
  · rw [real_sign_mul,Oside]
    cases' Real.sign_apply_eq_of_ne_zero  _ hdet <;>
    cases' Real.sign_apply_eq_of_ne_zero  _ hdet₂ <;>
    simp_all
  · constructor
    · simp_rw [open_triangle_iff hdet, Tco_line, ←and_imp, forall_in_swap_special]
      rw [forall_exists_pos_swap]
      · intro j
        by_cases hij : j = i
        · use 1, by norm_num -- Junk value
          intro a ⟨hapos, _⟩
          rw [hij, closed_side_to_co hdet (open_sub_closed _ hxT), zero_add, mul_div_assoc]
          apply mul_pos hapos
          rw [det₂_mul_last, real_sign_mul, mul_assoc, mul_div_right_comm]
          exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self (by rwa [Oside]))
        · have ⟨δ,hδpos, hδa⟩ := real_interval_δ (det₂ (Oside T j) ((det T * det₂ (Oside T i) y).sign • y) / det T) (mem_open_side_other_co hdet hxT j  hij)
          use δ, hδpos
          intro a ⟨hapos,haup⟩
          convert hδa a (by rwa [abs_of_pos hapos]) using 1
          field_simp
      · intro δ j ha δ' hδ' a ⟨ha'1, ha'2⟩
        apply ha
        simp_all only [ne_eq, and_imp, true_and, Preorder.le_trans a δ' δ ha'2 hδ']
    · intro a hapos hacl
      simp_rw [closed_triangle_iff hdet, Tco_line] at hacl
      specialize hacl i
      revert hacl
      simp
      rw [closed_side_to_co hdet (open_sub_closed _ hxT), zero_add,←neg_smul, det₂_mul_last,
          ←mul_assoc, ←neg_mul_eq_mul_neg, ←neg_mul_eq_neg_mul, neg_div, neg_neg_iff_pos, mul_assoc,  mul_div_assoc]
      apply mul_pos hapos
      rw [real_sign_mul, mul_assoc, mul_div_right_comm]
      exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self (by rwa [Oside]))


lemma seg_dir_sub {L : Segment} {x : ℝ²} (hxL : x ∈ open_hull L) :
    ∃ δ > 0, ∀ (a : ℝ), |a| ≤ δ → x + a • seg_vec L ∈ open_hull L := by

  sorry

lemma is_cover_sub {S : Finset Triangle} {X : Set ℝ²} (hCover : is_cover X S) :
    ∀ Δ ∈ S, closed_hull Δ ⊆ X := by
  intro _ hΔ
  rw [hCover.1]
  exact Set.subset_biUnion_of_mem hΔ

lemma is_cover_open_el_imp_eq {S : Finset Triangle} {X : Set ℝ²} (hCover : is_cover X S)
  {Δ₁ Δ₂ : Triangle} (hΔ₁ : Δ₁ ∈ S) (hΔ₂ : Δ₂ ∈ S) {x : ℝ²} (hx₁ : x ∈ open_hull Δ₁)
  (hx₂ : x ∈ open_hull Δ₂) :
    Δ₁ = Δ₂ := by
  by_contra hΔ₁₂
  have hx := Set.mem_inter hx₁ hx₂
  rwa [Disjoint.inter_eq (hCover.2 Δ₁ hΔ₁ Δ₂ hΔ₂ hΔ₁₂)] at hx

lemma cover_mem_side {S : Finset Triangle} {X : Set ℝ²} (hCover : is_cover X S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) {x : ℝ²} (hx : x ∈ X) (hInt: ∀ Δ ∈ S, x ∉ (open_hull Δ))
    (hv : ∀ i, ∀ Δ ∈ S, x ≠ Δ i) : ∃ Δ ∈ S, ∃ i : Fin 3, x ∈ open_hull (Tside Δ i) := by
  sorry


lemma seg_sub_side {T : Triangle} {L : Segment} {x : ℝ²} {i : Fin 3} (hdet : det T ≠ 0)
    (hxL : x ∈ open_hull L) (hxT : x ∈ open_hull (Tside T i))
    (hInter : open_hull T ∩ closed_hull L = ∅)
    (hv : ∀ i, T i ∉ open_hull L) : closed_hull L ⊆ closed_hull (Tside T i) := by
  have hdir : det₂ (seg_vec (Tside T i)) (seg_vec L) = 0 := by
    by_contra hcontra
    have ⟨σ, hσ, ⟨δ, hδ, hain⟩, _⟩  := seg_inter_open hxT hdet hcontra
    have ⟨δ', hδ', hseg'⟩ := seg_dir_sub hxL
    rw [Set.eq_empty_iff_forall_not_mem] at hInter
    apply hInter (x + (min δ δ') • σ • seg_vec L)
    rw [@Set.mem_inter_iff]
    constructor
    · exact hain _ (lt_min hδ hδ') (min_le_left _ _)
    · rw [←mul_smul]
      refine open_sub_closed _ (hseg' (min δ δ' * σ) ?_)
      have hσabs : |σ| = 1 := by
        cases' (mem_insert.1 hσ) with ht ht
        · simp only [ht, abs_neg, abs_one]
        · simp at ht
          simp only [ht, abs_one]
      rw [abs_mul, hσabs, mul_one]
      refine Eq.trans_le (b := min δ δ') ?_ ?_
      · simp_all only [abs_eq_self, le_min_iff, and_self]
        constructor <;> linarith
      · exact min_le_right _ _
  intro y hy
  have hTyi : ∀ z, z ∈ closed_hull L →  Tco T z i = 0 := by
    intro z hz
    have ⟨b,hb⟩ := seg_vec_co (open_sub_closed _ hxL) hz
    rw [hb, Tco_line, Oside, hdir, mul_zero, zero_div,add_zero]
    exact closed_side_to_co hdet (open_sub_closed _ hxT)
  have hy₂ : y ∈ closed_hull T := by
    rw [closed_triangle_iff hdet]
    by_contra hc; push_neg at hc
    have ⟨j, hj⟩ := hc
    have hij : i ≠ j := by
      by_contra hij
      rw [←hij, hTyi y hy] at hj
      linarith
    have hxCoj : 0 < Tco T x j := by
      exact mem_open_side_other_co hdet hxT j hij.symm
    have hxCoij : 0 < Tco T x j - Tco T y j := by
      linarith
    let α : Fin 2 → ℝ := fun | 0 => ((- Tco T y j)/ (Tco T x j - Tco T y j)) | 1 => (Tco T x j/ (Tco T x j - Tco T y j))
    have hαSimp : α ∈ open_simplex 2 := by
      constructor
      · intro k
        fin_cases k <;>(
        · dsimp [α]
          field_simp
          linarith)
      · simp [α]
        field_simp
        ring
    let L' : Segment := fun | 0 => x | 1 => y
    let z := ∑ k, α k • L' k
    have hiz : Tco T z i = 0 := by
      simp_rw [z, Tco_linear hαSimp.2, Fin.sum_univ_two, L', hTyi x (open_sub_closed _ hxL), hTyi y hy]
      linarith
    have hjz : Tco T z j = 0 := by
      simp_rw [z, Tco_linear hαSimp.2, Fin.sum_univ_two, L', α]
      field_simp
      ring
    apply hv (last_index i j)
    rw [←(two_co_zero_imp_corner hdet hij hiz hjz)]
    apply open_segment_sub (L₁ := L')
    · intro k
      fin_cases k <;> simp [L']
      · exact (open_sub_closed _ hxL)
      · exact hy
    · simp [L']
      intro hcontra
      rw [←hcontra] at hj
      linarith [hj, hTyi x (open_sub_closed _ hxL)]
    · exact ⟨α,hαSimp,rfl⟩
  exact (mem_closed_side hdet hy₂ i).1 (hTyi y hy)


/- Might not be necessary.-/
lemma segment_in_boundary_imp_in_side {T : Triangle} {L : Segment} (hdet : det T ≠ 0)
    (hL : closed_hull L ⊆ boundary T) : ∃ i, closed_hull L ⊆ closed_hull (Tside T i) := by
  have ⟨x,hx⟩ := open_seg_nonempty L
  have hxBoundary := hL (open_sub_closed _ hx)
  have hall : ∀ i, T i ∉ open_hull L := by

    sorry
  have ⟨i, hi⟩ := el_in_boundary_imp_side hdet hxBoundary ?_
  refine ⟨i,seg_sub_side hdet hx hi ?_ hall⟩
  · ext y; simp
    intro hyopen hyclosed
    refine (boundary_not_in_open (hL hyclosed)) hyopen
  · intro i hi
    specialize hall i
    rw [←hi] at hall
    exact hall hx

/- Might not be necessary.-/
lemma segment_in_boundary_imp_in_side₂ {T : Triangle} {L : Segment} (hdet : det T ≠ 0)
    (hL : closed_hull L ⊆ boundary T) : ∃ i, closed_hull L ⊆ closed_hull (Tside T i) := by
  have ⟨x,hx⟩ := open_seg_nonempty L
  have ⟨α,hα,hαx⟩ := hx
  have ⟨i,hi⟩ := el_boundary_imp_side hdet (hL (open_sub_closed _ hx))
  use i
  apply closed_hull_convex
  intro j
  rw [←mem_closed_side hdet]
  · rw [←mem_closed_side hdet] at hi
    · rw [←hαx, Tco_linear hα.2] at hi
      have hk : ∀ k, α k * Tco T (L k) i = 0 := by

        sorry
      specialize hk j

      sorry
    · sorry
  · sorry




lemma perp_vec_exists (Lset : Finset Segment) (hLset : ∀ L ∈ Lset, L 0 ≠ L 1)
    : ∃ y : ℝ², ∀ L ∈ Lset, det₂ (seg_vec L) y ≠ 0 := by
  have ⟨y₁, hy₁⟩ := Infinite.exists_not_mem_finset (image (fun L ↦ seg_vec L 1 / seg_vec L 0) Lset)
  use fun | 0 => 1 | 1 => y₁
  intro L hL
  simp [det₂]
  intro hContra
  by_cases h : seg_vec L 0 = 0
  · apply hLset L hL
    rw [←seg_vec_zero_iff]
    exact PiLp.ext (fun i ↦ by fin_cases i <;> simp_all)
  · apply hy₁
    rw [mem_image]
    refine ⟨L,hL,?_⟩
    field_simp
    linarith


/- Pigeonhole lemma of the form that I have not been able to find. -/
lemma finset_infinite_pigeonhole {α β : Type} [Infinite α] {f : α → β} {B : Finset β}
    (hf : ∀ a, f a ∈ B) : ∃ b ∈ B, Set.Infinite (f⁻¹' {b}) := by
  have : Finite B := by exact Finite.of_fintype { x // x ∈ B }
  let f_B := fun (a : α) => (⟨f a, hf a⟩ : B)
  have ⟨b, hb⟩ := Finite.exists_infinite_fiber f_B
  use b
  constructor
  · exact Finset.coe_mem b
  · convert Set.infinite_coe_iff.mp hb
    ext a
    cases b
    simp [f_B]

/- A version that states that the open_unit_square is open. -/
lemma open_unit_square_open_dir {x : ℝ²} (y : ℝ²) (hx : x ∈ open_unit_square) :
    ∃ (ε : ℝ), ε > 0 ∧ ∀ (n : ℕ), x + (1 / (n : ℝ)) • (ε • y) ∈ open_unit_square := by
  sorry


/-
We let this connect to a version that states that closed_hull T is closed.
The determinant assumption is not necessary but in our setup hard to avoid.
-/
lemma closed_triangle_is_closed_dir {T : Triangle} (hdet : det T ≠ 0) {x y : ℝ²}
    (h : Set.Infinite {n : ℕ | x + (1 / (n : ℝ)) • y ∈ closed_hull T}) : x ∈ closed_hull T := by
  rw [closed_triangle_iff hdet]
  by_contra hContra; push_neg at hContra
  have ⟨i,hi⟩ := hContra
  --Tco T (x  + a • y) i = Tco T x i + a * (det₂ (Oside T i) y) / det T
  have hB := Set.Infinite.not_bddAbove h
  rw [bddAbove_def] at hB
  push_neg at hB
  have hex : ∃ (n : ℕ), n > 0 ∧ (1/(n:ℝ)) * |(det₂ (Oside T i) y) / det T| < |Tco T x i| / 2 := by
    have ⟨n, hn⟩ := exists_nat_gt (max 0 ((|(det₂ (Oside T i) y) / det T|)/ (|Tco T x i| / 2)))
    use n
    rw [sup_lt_iff] at hn
    constructor
    · convert hn.1
      simp only [gt_iff_lt, Nat.cast_pos]
    · field_simp
      rw [div_lt_iff₀ hn.1, ←div_lt_iff₀' ?_]
      · exact hn.2
      · simp
        intro this
        rw [this] at hi
        exact (lt_self_iff_false 0).mp hi
  have ⟨n,hnpos,hn⟩ := hex
  have ⟨n',hn',hnn'⟩ := hB n
  dsimp at hn'
  rw [closed_triangle_iff] at hn'
  specialize hn' i
  rw [Tco_line] at hn'
  rw [←lt_self_iff_false (0:ℝ)]
  -- Annoying algebra
  calc
    0 ≤ Tco T x i + 1 / ↑n' * (det₂ (Oside T i) y / det T)    := by convert hn' using 2; ring
    _ ≤ Tco T x i + |1 / ↑n' * (det₂ (Oside T i) y / det T)|  := by gcongr; exact le_abs_self _
    _ = Tco T x i + (1 / ↑n') * |det₂ (Oside T i) y / det T|  := by
        rw [abs_mul]; congr; simp_all only [ne_eq,
        one_div, Set.mem_setOf_eq, gt_iff_lt, abs_eq_self, inv_nonneg, Nat.cast_nonneg]
    _ ≤ Tco T x i + (1 / ↑n) * |det₂ (Oside T i) y / det T|   := by gcongr
    _ < Tco T x i + |Tco T x i|/2                             := by gcongr
    _ = Tco T x i + (-Tco T x i)/2                            := by congr; exact abs_of_neg hi
    _ < 0                                                     := by linarith
  assumption



/- I don't know if this is in mathlib. Could not find it, -/
lemma infinite_distinct_el {α : Type} {S : Set α} (hS : Set.Infinite S) (k : α) : ∃ a ∈ S, a ≠ k := by
  have ⟨a, haS, ha⟩ :=  Set.Infinite.exists_not_mem_finset hS ({k} : Finset α)
  exact ⟨a, haS, List.ne_of_not_mem_cons ha⟩




/-
Theorems about the unit square.
-/

lemma closed_unit_square_eq : closed_hull Psquare = {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩
    intro i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [Psquare, Fin.sum_univ_four, Left.add_nonneg, hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [Psquare, Fin.sum_univ_four]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    use fun
          | 0 => (1 + min (x 0) (x 1) - (x 0) - (x 1))
          | 1 => x 0 - min (x 0) (x 1)
          | 2 => min (x 0) (x 1)
          | 3 => x 1 - min (x 0) (x 1)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i
      fin_cases i <;> simp [hx 0, hx 1]
      cases min_choice (x 0) (x 1) <;> simp_all
      linarith [hx 0]
    · simp [Fin.sum_univ_four]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [Fin.sum_univ_four, Psquare, v]

-- The open unit square is more or less the same
lemma open_unit_square_eq : open_hull Psquare = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩
    intro i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [Psquare, Fin.sum_univ_four, Left.add_pos, hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [Psquare, Fin.sum_univ_four]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    -- This part is a little bit annoying. We split it up in some steps.
    have h₁ : 0 < (1 + min (x 0) (x 1) - (x 0) - (x 1)) := by
      cases min_choice (x 0) (x 1) <;> simp_all; linarith [hx 0]
    have h₂ : 0 < min (x 0) (x 1) := by
      cases min_choice (x 0) (x 1) <;> simp_all;
    let a : ℝ := min ((1 + min (x 0) (x 1) - (x 0) - (x 1))) (min (x 0) (x 1) )
    have h₃ : 0 < a := lt_min h₁ h₂
    use fun
          | 0 => (1 + min (x 0) (x 1) - (x 0) - (x 1)) - a/2
          | 1 => x 0 - min (x 0) (x 1) + a/2
          | 2 => min (x 0) (x 1) - a/2
          | 3 => x 1 - min (x 0) (x 1) + a/2
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i; fin_cases i <;> simp only [Fin.isValue, sub_pos]
      · exact gt_of_ge_of_gt (b := a) (min_le_left _ _) (by linarith)
      · exact add_pos_of_nonneg_of_pos (by simp) (by linarith)
      · exact gt_of_ge_of_gt (b := a) (min_le_right _ _) (by linarith)
      · exact add_pos_of_nonneg_of_pos (by simp) (by linarith)
    · simp [Fin.sum_univ_four]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [Fin.sum_univ_four, Psquare, v]


lemma element_in_boundary_square {x : ℝ²} (hx : x ∈ boundary Psquare) :
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


lemma segment_in_boundary_square {x : ℝ²} (hx : x ∈ boundary Psquare)
    : ∃ i, ∀ L, x ∈ open_hull L → closed_hull L ⊆ closed_hull Psquare → (seg_vec L) i = 0 := by
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

lemma aux_det₂ {L : ℝ²} (hL : L ≠ 0) (hi : ∃ i, L i = 0) : det₂ L (v 1 1) ≠ 0 := by
  by_contra hz
  refine hL ?_
  ext j
  have ⟨i, hi⟩ := hi
  fin_cases i <;> (
    simp at hi
    simp [det₂, hi] at hz
    fin_cases j <;> (simp; assumption)
  )

lemma el_boundary_square_triangle_dir {x : ℝ²} (hx : x ∈ boundary Psquare):
    ∃ σ ∈ ({-1,1} : Finset ℝ), ∀ (Δ : Triangle), (det Δ ≠ 0) →
    (closed_hull Δ ⊆ closed_hull Psquare) → (∃ i, x ∈ open_hull (Tside Δ i))
    → (∃ εΔ > 0, ∀ y, 0 < y → y ≤ εΔ → x + (σ * y) • (v 1 1) ∈ open_hull Δ) := by
    -- First we produce such triangle
    by_cases hΔ : ∃ Δ, (det Δ ≠ 0) ∧ (closed_hull Δ ⊆ closed_hull Psquare) ∧ (∃ i, x ∈ open_hull (Tside Δ i))
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
                  try simp [neg_eq_zero] at hL
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



lemma segment_triangle_pairing_int (S : Finset Triangle) (hCover : is_cover unit_square S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ open_hull Psquare) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
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
        rw [←unit_square, hCover.1, Set.mem_iUnion₂] at this
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
          exact hΔneq (is_cover_open_el_imp_eq hCover hΔ' hΔ hain' hain)
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
            exact hneq (is_cover_open_el_imp_eq hCover hΔ'' hΔ hain'' hain)
          simp only [hl, mem_insert, mem_singleton, or_true]
        · have hl : Δ'' = Δ' := by
            by_contra hneq
            rw [h] at hain''
            specialize hain' (min δ' δ'') (lt_min hδ' hδ'') (min_le_left δ' δ'')
            specialize hain'' (min δ' δ'') (lt_min hδ' hδ'') (min_le_right δ' δ'')
            exact hneq (is_cover_open_el_imp_eq hCover hΔ'' hΔ' hain'' hain')
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


lemma segment_triangle_pairing_boundary (S : Finset Triangle) (hCover : is_cover unit_square S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ boundary Psquare) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
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
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (boundary_sub_closed Psquare (hLunit hLx)) hU hxNvtx
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
    have ⟨ε, hε, hεΔ⟩ := hσ Δ (hArea Δ hΔ) (is_cover_sub hCover Δ hΔ) ⟨i,hxi⟩
    have ⟨ε', hε', hεΔ'⟩ := hσ Δ' (hArea Δ' hΔ') (is_cover_sub hCover Δ' hΔ') ⟨i',open_segment_sub' hi' hL hLx⟩
    specialize hεΔ (min ε ε') (lt_min hε hε') (min_le_left ε ε')
    specialize hεΔ' (min ε ε') (lt_min hε hε') (min_le_right ε ε')
    exact is_cover_open_el_imp_eq hCover hΔ' hΔ hεΔ' hεΔ





/-
  The square can be covered by an even number of triangles.
-/

/- These two triangles dissect the square and have equal area.-/
def Δ₀  : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

lemma Δ₀_det : det Δ₀ ≠ 0 := by
  simp_rw [det, Δ₀, v]
  norm_num

lemma Δ₀'_det : det Δ₀' ≠ 0 := by
  simp_rw [det, Δ₀', v]
  norm_num

lemma areaΔ₀ : triangle_area Δ₀ = 1 / 2 := by
  simp [triangle_area, Δ₀]

lemma areaΔ₀' : triangle_area Δ₀' = 1 / 2 := by
  simp [triangle_area, Δ₀']

lemma Δ₀_Tco₀ (x : ℝ²) : Tco Δ₀ x 0 = 1 - (x 0 + x 1):= by
  simp [Tco, sign_seg, det, Tside, Δ₀]; ring

lemma Δ₀_Tco₁ (x : ℝ²) : Tco Δ₀ x 1 = x 0 := by
  simp [Tco, sign_seg, det, Tside, Δ₀]

lemma Δ₀_Tco₂ (x : ℝ²) : Tco Δ₀ x 2 = x 1 := by
  simp [Tco, sign_seg, det, Tside, Δ₀]

lemma Δ₀_open_halfspace {x : ℝ²} (hx : x ∈ open_hull Δ₀) : x 0 + x 1 < 1 := by
  have hx := (open_triangle_iff Δ₀_det).1 hx 0
  rw [Δ₀_Tco₀] at hx
  linarith

lemma Δ₀'_Tco₀ (x : ℝ²) : Tco Δ₀' x 0 = 1 - x 1:= by
  simp [Tco, sign_seg, det, Tside, Δ₀']; ring

lemma Δ₀'_Tco₁ (x : ℝ²) : Tco Δ₀' x 1 = 1 - x 0:= by
  simp [Tco, sign_seg, det, Tside, Δ₀']; ring

lemma Δ₀'_Tco₂ (x : ℝ²) : Tco Δ₀' x 2 = (x 0 + x 1) - 1:= by
  simp [Tco, sign_seg, det, Tside, Δ₀']; ring

lemma Δ₀'_open_halfspace {x : ℝ²} (hx : x ∈ open_hull Δ₀') : x 0 + x 1 > 1 := by
  have hx := (open_triangle_iff Δ₀'_det).1 hx 2
  rw [Δ₀'_Tco₂] at hx
  linarith

lemma Δ₀_Δ₀'_disj : Disjoint (open_hull Δ₀) (open_hull Δ₀') := by
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro x hx y hy hxy
  rw [hxy] at hx
  linarith [Δ₀_open_halfspace hx, Δ₀'_open_halfspace hy]

lemma Δ₀_sub_square : closed_hull Δ₀ ⊆ closed_hull Psquare := by
  intro x hx
  rw [closed_unit_square_eq]
  rw [closed_triangle_iff Δ₀_det] at hx
  have hx₀ := hx 0; simp [Δ₀_Tco₀] at hx₀
  have hx₁ := hx 1; simp [Δ₀_Tco₁] at hx₁
  have hx₂ := hx 2; simp [Δ₀_Tco₂] at hx₂
  intro i
  constructor <;> fin_cases i <;> (simp; linarith)

lemma Δ₀'_sub_square : closed_hull Δ₀' ⊆ closed_hull Psquare := by
  intro x hx
  rw [closed_unit_square_eq]
  rw [closed_triangle_iff Δ₀'_det] at hx
  have hx₀ := hx 0; simp [Δ₀'_Tco₀] at hx₀
  have hx₁ := hx 1; simp [Δ₀'_Tco₁] at hx₁
  have hx₂ := hx 2; simp [Δ₀'_Tco₂] at hx₂
  intro i
  constructor <;> fin_cases i <;> (simp; linarith)

lemma Δ₀Δ₀'_cover_square : is_cover (closed_hull Psquare) {Δ₀, Δ₀'} := by
  constructor
  simp
  · ext x
    constructor
    · intro hx
      rw [closed_unit_square_eq] at hx
      by_cases hxbound : x 0 + x 1 ≤ 1
      · left
        rw [closed_triangle_iff Δ₀_det]
        intro i; fin_cases i
        · simp [Δ₀_Tco₀, hxbound]
        · simp [Δ₀_Tco₁, hx 0]
        · simp [Δ₀_Tco₂, hx 1]
      · right
        rw [closed_triangle_iff Δ₀'_det]
        intro i; fin_cases i
        · simp [Δ₀'_Tco₀, hx 1]
        · simp [Δ₀'_Tco₁, hx 0]
        · simp [Δ₀'_Tco₂]; linarith
    · intro hx
      obtain (hx | hx) := hx
      · exact Δ₀_sub_square hx
      · exact Δ₀'_sub_square hx
  · intro Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
    simp_all
    cases hΔ₁ <;> cases hΔ₂ <;> simp_all [Disjoint.symm, Δ₀_Δ₀'_disj]

lemma Δ₀Δ₀'_equal_cover_square : is_equal_area_cover (closed_hull Psquare) {Δ₀, Δ₀'} := by
  refine ⟨Δ₀Δ₀'_cover_square,?_⟩
  use 1 / 2
  intro _ hΔ
  simp at hΔ
  cases' hΔ with hΔ hΔ <;> rw [hΔ]
  · exact areaΔ₀
  · exact areaΔ₀'

lemma Δ₀_neq_Δ₀' : Δ₀ ≠ Δ₀' := by
  intro heq
  have heq₀ := congrFun (congrFun heq 0) 0
  simp [Δ₀, Δ₀'] at heq₀

lemma Δ₀Δ₀'_finset_size : ({Δ₀, Δ₀'} : Finset Triangle).card = 2 :=
  card_pair (Δ₀_neq_Δ₀')

lemma exists_equal_area_cover_size_two
    : (∃ (S : Finset Triangle), is_equal_area_cover (closed_hull Psquare) S ∧ S.card = 2) := by
  exact ⟨{Δ₀, Δ₀'}, by convert Δ₀Δ₀'_equal_cover_square; simp, Δ₀Δ₀'_finset_size⟩



/- Now we show how a cover of size two implies a cover of any even size.-/

/- Elementary stuff about scaling (only in the y direction).-/

def scale_vector (a : ℝ) (y : ℝ²) : ℝ² := fun | 0 => y 0 | 1 => a * y 1

def scale_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ scale_vector a (T i)

lemma scale_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (scale_triangle a T) = |a| * (triangle_area T) := by
  simp [triangle_area, scale_triangle, scale_vector, ←abs_mul, ←mul_div_assoc]
  congr; ring

lemma open_hull_scale {a : ℝ} (T : Triangle)
    : open_hull (scale_triangle a T) = (scale_vector a) '' (open_hull T) := by
  ext x
  constructor
  · intro ⟨α,hα,hαx⟩
    use (∑ i, α i • T i)
    refine ⟨by use α;,?_⟩
    rw [←hαx]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, scale_triangle, scale_vector]; ring
  · intro ⟨y, ⟨α,hα,hαy⟩, hyx⟩
    use α, hα
    rw [←hyx, ←hαy]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, scale_triangle, scale_vector]; ring

lemma closed_hull_scale {a : ℝ} (T : Triangle)
    : closed_hull (scale_triangle a T) = (scale_vector a) '' (closed_hull T) := by
  ext x
  constructor
  · intro ⟨α,hα,hαx⟩
    use (∑ i, α i • T i)
    refine ⟨by use α;,?_⟩
    rw [←hαx]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, scale_triangle, scale_vector]; ring
  · intro ⟨y, ⟨α,hα,hαy⟩, hyx⟩
    use α, hα
    rw [←hyx, ←hαy]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, scale_triangle, scale_vector]; ring

lemma scale_inverse {a : ℝ} {x : ℝ²} (ha : a ≠ 0) : scale_vector a⁻¹ (scale_vector a x) = x := by
  ext i; fin_cases i <;> simp [scale_vector]
  rw [←mul_assoc, inv_mul_cancel₀ ha, one_mul]

lemma scale_inverse' {a : ℝ} {x : ℝ²} (ha : a ≠ 0) : scale_vector a (scale_vector a⁻¹ x) = x := by
  convert scale_inverse (a := a⁻¹) (inv_ne_zero ha)
  exact Eq.symm (DivisionMonoid.inv_inv a)

lemma scale_injective {a : ℝ} (ha : a ≠ 0) : (fun x ↦ scale_vector a x).Injective :=
  Function.RightInverse.injective (g := (fun x ↦ scale_vector a⁻¹ x)) (fun _ ↦ scale_inverse ha)

lemma scale_disjoint {X₁ X₂ : Set ℝ²} {a : ℝ} (ha : a ≠ 0) (h₁₂ : Disjoint X₁ X₂)
    : Disjoint ((scale_vector a) '' X₁) ((scale_vector a) '' X₂) :=
  (Set.disjoint_image_iff (scale_injective ha)).mpr h₁₂

lemma scale_union {α : Type} {f : α → Set ℝ²} {S : Set α} {a : ℝ}
    : ⋃ X ∈ S, (scale_vector a) '' (f X) = (scale_vector a) '' (⋃ X ∈ S, (f X)) :=
  Eq.symm (Set.image_iUnion₂ _ fun i _ => f i)

lemma scale_disjoint' {X₁ X₂ : Set ℝ²} {a : ℝ} (ha : a ≠ 0)
    (h₁₂ : Disjoint ((scale_vector a) '' X₁) ((scale_vector a) '' X₂)) : Disjoint X₁ X₂ := by
  convert scale_disjoint (X₁ := ((scale_vector a) '' X₁)) (X₂ := ((scale_vector a) '' X₂)) (a := a⁻¹) (inv_ne_zero ha) h₁₂ <;> (
    rw [Set.image_image]
    conv => rhs; lhs; intro x; rw [scale_inverse ha]
    simp only [Set.image_id']
  )

/- Elementary stuff about translating (only in the y direction).-/

def translate_vector (a : ℝ) (x : ℝ²) : ℝ² := fun | 0 => x 0 | 1 => a + x 1
def translate_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ translate_vector a (T i)

lemma translate_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (translate_triangle a T) = (triangle_area T) := by
  simp [triangle_area, translate_triangle, translate_vector]
  congr 2; ring

lemma open_hull_translate {a : ℝ} (T : Triangle)
    : open_hull (translate_triangle a T) = (translate_vector a) '' (open_hull T) := by
  ext x
  constructor
  · intro ⟨α,hα,hαx⟩
    use (∑ i, α i • T i)
    refine ⟨by use α;,?_⟩
    rw [←hαx]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, translate_triangle, translate_vector]; ring_nf
    nth_rw 1 [←mul_one a, ←hα.2, Fin.sum_univ_three]
    ring
  · intro ⟨y, ⟨α,hα,hαy⟩, hyx⟩
    use α, hα
    rw [←hyx, ←hαy]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, translate_triangle, translate_vector]; ring_nf
    nth_rw 4 [←mul_one a]
    simp [←hα.2, Fin.sum_univ_three]
    ring

lemma closed_hull_translate {a : ℝ} (T : Triangle)
    : closed_hull (translate_triangle a T) = (translate_vector a) '' (closed_hull T) := by
  ext x
  constructor
  · intro ⟨α,hα,hαx⟩
    use (∑ i, α i • T i)
    refine ⟨by use α;,?_⟩
    rw [←hαx]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, translate_triangle, translate_vector]; ring_nf
    nth_rw 1 [←mul_one a, ←hα.2, Fin.sum_univ_three]
    ring
  · intro ⟨y, ⟨α,hα,hαy⟩, hyx⟩
    use α, hα
    rw [←hyx, ←hαy]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, translate_triangle, translate_vector]; ring_nf
    nth_rw 4 [←mul_one a]
    simp [←hα.2, Fin.sum_univ_three]
    ring

lemma translate_inverse {a : ℝ} {x : ℝ²} : translate_vector (-a) (translate_vector a x) = x := by
  ext i; fin_cases i <;> simp [translate_vector]

example (f₁ f₂ : ℝ² → ℝ²) (X : Set ℝ²) : f₁ '' (f₂ '' X) = (fun x ↦ f₁ (f₂ x)) '' X := by
  exact Set.image_image f₁ f₂ X

lemma translate_inverse' {a : ℝ} {x : ℝ²} : translate_vector a (translate_vector (-a) x) = x := by
  convert translate_inverse (a := -a); exact (neg_neg a).symm

lemma translate_injective {a : ℝ} : (fun x ↦ translate_vector a x).Injective :=
  Function.RightInverse.injective (g := (fun x ↦ translate_vector (-a) x)) (fun _ ↦ translate_inverse)

lemma translate_disjoint {X₁ X₂ : Set ℝ²} {a : ℝ} (h₁₂ : Disjoint X₁ X₂)
    : Disjoint ((translate_vector a) '' X₁) ((translate_vector a) '' X₂) :=
  (Set.disjoint_image_iff translate_injective).mpr h₁₂

lemma translate_disjoint' {X₁ X₂ : Set ℝ²} {a : ℝ}
    (h₁₂ : Disjoint ((translate_vector a) '' X₁) ((translate_vector a) '' X₂)) : Disjoint X₁ X₂ := by
  convert translate_disjoint (X₁ := ((translate_vector a) '' X₁)) (X₂ := ((translate_vector a) '' X₂)) (a := -a) h₁₂ <;> (
    rw [Set.image_image]
    conv => rhs; lhs; intro x; rw [translate_inverse]
    simp only [Set.image_id']
  )

lemma translate_union {α : Type} {f : α → Set ℝ²} {S : Set α} {a : ℝ}
    : ⋃ X ∈ S, (translate_vector a) '' (f X) = (translate_vector a) '' (⋃ X ∈ S, (f X)) := by
  exact Eq.symm (Set.image_iUnion₂ (translate_vector a) fun i j => f i)


/- This rewriting is for convenience. -/
def disjoint_set {α β : Type} (X : Set α) (f : α → Set β) := ∀ a₁ a₂, a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ → Disjoint (f a₁) (f a₂)
def covers {α β} (X : Set α) (Y : Set β) (f : α → Set β) := Y = ⋃ a ∈ X, f a

lemma is_cover_iff (X : Set ℝ²) (S : Set Triangle)
    : is_cover X S ↔ covers S X closed_hull ∧ disjoint_set S open_hull := by
  simp [is_cover,covers, disjoint_set]
  intro _
  constructor
  · intro h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq
    exact h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
  · intro h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
    exact h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq

lemma unit_square_fold {a : ℝ} (hal : 0 < a) (hau: a < 1)
    : closed_hull Psquare = (scale_vector a '' closed_hull Psquare) ∪ (translate_vector a '' (scale_vector (1-a) '' closed_hull Psquare)) := by
  have h₁ := inv_pos_of_pos hal
  have h₂ : 0 < 1 - a := by linarith
  have h₃ := inv_pos_of_pos h₂
  ext x
  simp [closed_unit_square_eq]
  constructor
  · intro hx
    by_cases ha : x 1 ≤ a
    · left; use scale_vector a⁻¹ x
      refine ⟨?_, scale_inverse' (by linarith)⟩
      intro i; fin_cases i <;> simp [scale_vector, hx 0]
      exact ⟨(mul_nonneg_iff_of_pos_left h₁).mpr (hx 1).1, (inv_mul_le_iff₀ hal).mpr (by linarith)⟩
    · right; use scale_vector (1 - a)⁻¹ (translate_vector (-a) x)
      refine ⟨?_, by rw [scale_inverse' (by linarith), translate_inverse']⟩
      intro i; fin_cases i <;> simp [scale_vector, translate_vector, hx 0]
      exact ⟨(le_inv_mul_iff₀' h₂).mpr (by linarith),(inv_mul_le_iff₀ h₂).mpr (by linarith [hx 1])⟩
  · intro hx
    cases' hx with hx hx <;> (
      have ⟨y, hy, hyx⟩ := hx
      rw [←hyx]
      intro i; fin_cases i <;> simp [scale_vector, translate_vector, hy 0, hy 1]
    )
    · refine ⟨(mul_nonneg_iff_of_pos_left hal).mpr (hy 1).1,?_⟩
      calc
        a * y 1 ≤ 1 * y 1 := by gcongr; exact (hy 1).1
        _       ≤ 1 * 1   := by gcongr; exact (hy 1).2
        _       = 1       := by norm_num
    · refine ⟨Left.add_nonneg (by linarith) ((mul_nonneg_iff_of_pos_left h₂).mpr (hy 1).1), ?_⟩
      calc
        a + (1 - a) * y 1 ≤ a + (1 - a) * 1  := by gcongr; exact (hy 1).2
        _                 = 1                := by ring

lemma combine_covers {S₁ S₂ : Set Triangle} (h₁ : covers S₁ (closed_hull Psquare) closed_hull)
    (h₂ : covers S₂ (closed_hull Psquare) closed_hull) {a : ℝ} (hal : 0 < a) (hau : a < 1)
    : covers ((scale_triangle a '' S₁) ∪ (translate_triangle a '' (scale_triangle (1-a) '' S₂))) (closed_hull Psquare) closed_hull := by
  unfold covers at h₁ h₂
  rw [covers, Set.biUnion_union, Set.biUnion_image, Set.biUnion_image, Set.biUnion_image]
  simp_rw [closed_hull_translate, closed_hull_scale, translate_union, scale_union, ←h₁, ←h₂]
  exact unit_square_fold hal hau

lemma cover_nontrivial_open {S : Set Triangle} (h : covers S (closed_hull Psquare) closed_hull)
    (hNonDegenerate : ∀ Δ ∈ S, det Δ ≠ 0) : ∀ Δ ∈ S, open_hull Δ ⊆ open_hull Psquare := by
  intro Δ hΔ x hx
  sorry




lemma disjoint_set_scale {a : ℝ} (ha : a ≠ 0) {S : Set Triangle}
    (hX : disjoint_set S open_hull) : disjoint_set (scale_triangle a '' S) open_hull := by
  intro Δ₁ Δ₂ ⟨Δ₁',hΔ₁',hΔ₁Δ₁'⟩ ⟨Δ₂',hΔ₂',hΔ₂Δ₂'⟩ hneq
  specialize hX Δ₁' Δ₂' hΔ₁' hΔ₂' ?_
  · intro hContra
    apply hneq
    rw [←hΔ₁Δ₁',←hΔ₂Δ₂',hContra]
  · rw [←hΔ₁Δ₁', ←hΔ₂Δ₂', open_hull_scale, open_hull_scale]
    exact scale_disjoint ha hX

lemma disjoint_set_translate {a : ℝ} {S : Set Triangle}
    (hS : disjoint_set S open_hull) : disjoint_set (translate_triangle a '' S) open_hull := by
  intro Δ₁ Δ₂ ⟨Δ₁',hΔ₁',hΔ₁Δ₁'⟩ ⟨Δ₂',hΔ₂',hΔ₂Δ₂'⟩ hneq
  specialize hS Δ₁' Δ₂' hΔ₁' hΔ₂' ?_
  · intro hContra
    apply hneq
    rw [←hΔ₁Δ₁',←hΔ₂Δ₂',hContra]
  · rw [←hΔ₁Δ₁', ←hΔ₂Δ₂', open_hull_translate, open_hull_translate]
    exact translate_disjoint hS


lemma disjoint_folded_square {a : ℝ} (hal : 0 < a) (hau: a < 1)
    : Disjoint (scale_vector a '' open_hull Psquare) (translate_vector a '' (scale_vector (1-a) '' open_hull Psquare)) := by
  simp_rw [Set.disjoint_iff_forall_ne, open_unit_square_eq]
  intro x₁ ⟨y, hy, hyx₁⟩ x₂ ⟨z, ⟨w, hw, hwz⟩, hzx₂⟩
  have hx₁Bound : x₁ 1 < a := by
    simp_rw [←hyx₁, scale_vector]
    calc
      a * y 1 < a * 1 := by gcongr; exact (hy 1).2
      _       = a     := by ring
  have hx₂Bound : a < x₂ 1 := by
    simp_rw [←hzx₂, ←hwz, translate_vector, scale_vector]
    apply lt_add_of_pos_right _
    exact mul_pos (by linarith) (hw 1).1
  intro hcontra
  rw [@PiLp.ext_iff] at hcontra
  specialize hcontra 1
  linarith

lemma disjoint_aux {α β : Type} (S₁ S₂ : Set α) (f : α → Set β) (h₁ : disjoint_set S₁ f)
    (h₂ : disjoint_set S₂ f) (h₃ : ∀ a₁ a₂, a₁ ∈ S₁ → a₂ ∈ S₂ → Disjoint (f a₁) (f a₂)) : disjoint_set (S₁ ∪ S₂) f := by
  intro a₁ a₂ ha₁ ha₂ hneq
  cases' ha₁ with ha₁ ha₁ <;> cases' ha₂ with ha₂ ha₂
  · exact h₁ a₁ a₂ ha₁ ha₂ hneq
  · exact h₃ a₁ a₂ ha₁ ha₂
  · exact (h₃ a₂ a₁ ha₂ ha₁ ).symm
  · exact h₂ a₁ a₂ ha₁ ha₂ hneq

/- Two covers of the unit square can be combined to a new cover.-/

lemma combine_disjoint_covers {S₁ S₂ : Set Triangle} (h₁ : is_cover (closed_hull Psquare) S₁)
    (h₂ : is_cover (closed_hull Psquare) S₂) (h₁NonDegen : ∀ Δ ∈ S₁, det Δ ≠ 0) (h₂NonDegen : ∀ Δ ∈ S₂, det Δ ≠ 0)
    {a : ℝ} (hal : 0 < a) (hau : a < 1)
    : is_cover (closed_hull Psquare) ((scale_triangle a '' S₁) ∪ (translate_triangle a '' (scale_triangle (1-a) '' S₂))) := by
  rw [is_cover_iff] at *
  constructor
  · exact combine_covers h₁.1 h₂.1 hal hau
  · refine disjoint_aux _ _ _ ?_ ?_ ?_
    · exact disjoint_set_scale (by linarith) h₁.2
    · exact disjoint_set_translate (disjoint_set_scale (by linarith) h₂.2)
    · intro Δ₁ Δ₂ ⟨Δ₁', hΔ₁S₁, hΔ₁Δ₁'⟩ ⟨t,  ⟨Δ₂', hΔ₂S₂, hΔ₂Δ₂'⟩ , ht⟩
      rw [←hΔ₁Δ₁', ←ht, ←hΔ₂Δ₂', open_hull_scale, open_hull_translate, open_hull_scale]
      refine Set.disjoint_of_subset ?_ ?_ (disjoint_folded_square hal hau)
      · exact Set.image_mono (cover_nontrivial_open h₁.1 h₁NonDegen _ hΔ₁S₁)
      · exact Set.image_mono (Set.image_mono (cover_nontrivial_open h₂.1 h₂NonDegen _ hΔ₂S₂))



/- The third property is implied by the first two, but we do not need that. -/
def aux_monsky_eady_dir (m : ℕ) : Prop := ∃ (S : Finset Triangle),
      is_equal_area_cover unit_square S ∧
      S.card = 2*(m+1) ∧
      ∀ Δ ∈ S, triangle_area Δ = 1 / (2*(m+1):ℝ)

lemma monsky_easy_direction₂ : aux_monsky_eady_dir 0 := by
  refine ⟨{Δ₀, Δ₀'}, by convert Δ₀Δ₀'_equal_cover_square; simp, ⟨Δ₀Δ₀'_finset_size,?_⟩⟩
  intro Δ hΔ
  simp at hΔ
  cases hΔ <;> simp_all [areaΔ₀, areaΔ₀']

lemma monsky_easy_direction_step (m : ℕ)
    : aux_monsky_eady_dir m → aux_monsky_eady_dir (m + 1) := by
  have ⟨S₁, ⟨hS₁cover,_⟩, hS₁size, hS₁Area⟩ := monsky_easy_direction₂
  intro ⟨S₂, ⟨hS₂cover,_⟩, hS₂size, hS₂Area⟩
  let a := 1 / ((m : ℝ) + 2)
  use (Finset.image (fun T ↦ scale_triangle a T) S₁) ∪ Finset.image (fun T ↦ (translate_triangle a (scale_triangle (1-a) T))) S₂
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · convert combine_disjoint_covers hS₁cover hS₂cover (a := a) ?_ ?_ ?_ ?_
    · simp; congr;
      sorry
    · intro Δ hΔS₁
      rw [←area_nonzero_iff_det_nonzero, hS₁Area _ hΔS₁]
      linarith
    · intro Δ hΔS₂
      rw [←area_nonzero_iff_det_nonzero, hS₂Area _ hΔS₂]
      simp
      linarith
    · simp [a]; linarith
    · simp [a]; sorry
  · use 1 / (2*((m:ℝ)+2))
    intro Δ; simp
    rintro (hΔ | hΔ) <;> (have ⟨Δ',hΔ',hΔΔ'⟩ := hΔ; rw [←hΔΔ'])
    · rw [scale_triangle_area _ _, hS₁Area Δ' hΔ']
      simp [a]; linarith
    · rw [translate_triangle_area _ _, scale_triangle_area _ _, hS₂Area Δ' hΔ']
      simp [a]; rw [←mul_assoc]; congr
      sorry
  · -- Disjointness here is still not easy.
    sorry
  ·
    sorry





theorem monsky_easy_direction {n : ℕ} (hn : Even n) (hnneq : n ≠ 0)
    : (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n) := by
  let f : ℕ → Prop := fun m ↦ ∃ (S : Finset Triangle),
      is_equal_area_cover unit_square S ∧
      S.card = 2*(m+1) ∧
      ∀ Δ ∈ S, triangle_area Δ = 1 / (2*(m+1):ℝ)
  have h₀ : f 0 := by
    sorry
  have hI : ∀ m, f m := by
    intro m;
    induction' m with m ih
    · exact h₀
    ·
      sorry
  have ⟨m, hm⟩ := hn
  have hm : m ≠ 0 := by
    intro hc; simp_rw [hc, zero_add] at hm; exact hnneq hm
  have ⟨m',hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm



  sorry







-- Here a different try. Just give a very explicit cover.
noncomputable def zig_part_cover (n : ℕ)
  := Finset.image (fun (s : Fin n) ↦ translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀)) univ

noncomputable def zag_part_cover (n : ℕ)
  := Finset.image (fun (s : Fin n) ↦ translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')) univ

lemma zig_cover_size (n : ℕ) : (zig_part_cover n).card = n := by
  unfold zig_part_cover
  by_cases hn : n = 0
  rw [hn]; simp
  rw [Finset.card_image_of_injective]
  · simp only [card_univ, Fintype.card_fin]
  · intro s₁ s₂ hsame
    have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
    have hn' := (Nat.cast_ne_zero (R := ℝ)).mpr hn
    simp [translate_triangle, translate_vector, div_eq_div_iff hn' hn'] at hsame
    cases' hsame with h h
    · exact Fin.eq_of_val_eq h
    · rw [h] at hn'; simp at hn'


lemma zag_cover_size (n : ℕ) : (zag_part_cover n).card = n := by
  unfold zag_part_cover
  by_cases hn : n = 0
  rw [hn]; simp
  rw [Finset.card_image_of_injective]
  · simp only [card_univ, Fintype.card_fin]
  · intro s₁ s₂ hsame
    have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
    have hn' := (Nat.cast_ne_zero (R := ℝ)).mpr hn
    simp [translate_triangle, translate_vector, div_eq_div_iff hn' hn'] at hsame
    cases' hsame with h h
    · exact Fin.eq_of_val_eq h
    · rw [h] at hn'; simp at hn'

lemma zig_zag_cover_size (n : ℕ) : (zig_part_cover n ∪ zag_part_cover n).card = 2 * n := by
  have h : (zig_part_cover n ∩ zag_part_cover n).card = 0 := by
    rw [card_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_left]
    intro _ h₁ h₂
    simp [zig_part_cover, zag_part_cover] at h₁ h₂
    have ⟨s₁,hs₁⟩ := h₁
    have ⟨s₂,hs₂⟩ := h₂
    rw [←hs₂] at hs₁
    have hsame := congrArg (fun Δ ↦ Δ 0 0) hs₁
    simp [translate_triangle, translate_vector, scale_triangle, scale_vector, Δ₀, Δ₀'] at hsame
  simp_rw [card_union, zig_cover_size, zag_cover_size, h, tsub_zero, two_mul]


lemma zig_cover_area {n : ℕ} : ∀ {Δ : Triangle}, Δ ∈ zig_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp [zig_part_cover] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀]
  simp

lemma zag_cover_area {n : ℕ} : ∀ {Δ : Triangle}, Δ ∈ zag_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp [zag_part_cover] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀']
  simp

lemma fin_el_bound {n : ℕ} {x: ℝ} {s₁ s₂ : Fin n} (h₁l : x - 1 < s₁) (h₁u : s₁ < x)
    (h₂l : x - 1 < s₂)  (h₂u : s₂ < x) : s₁ = s₂ := by

  sorry

lemma zig_open_disjoint{n : ℕ} : disjoint_set ((zig_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp [mem_coe, zig_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    · refine hΔneq ?_
      simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      rw [←hs₁, ←hs₂, fin_el_bound (by linarith) hx₁₂ (by linarith) hx₂₂]
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
  · simp [Nat.eq_zero_of_not_pos nsign, zig_part_cover, disjoint_set]

lemma zag_open_disjoint{n : ℕ} : disjoint_set ((zag_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp [mem_coe, zag_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    · refine hΔneq ?_
      simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      rw [←hs₁, ←hs₂, fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂) (by linarith) (by linarith) (by linarith) (by linarith)]
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover, disjoint_set]

lemma zig_zag_open_disjoint {n : ℕ}
    : ∀ a₁ a₂, a₁ ∈ (zig_part_cover n) → a₂ ∈ (zag_part_cover n) → Disjoint (open_hull a₁) (open_hull a₂) := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂
    simp [mem_coe, zig_part_cover, zag_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₁ := hx₂ 1
    have hx₂₂ := hx₂ 2
    · simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      have l := fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂) (by linarith) (by linarith) (by linarith) (by linarith)
      rw [l] at hx₁₀ hx₁₂
      linarith
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover, disjoint_set]

lemma zig_zag_covers_square {n : ℕ} (hn : n ≠ 0)
    : covers ((zig_part_cover n ∪ zag_part_cover n) : Set Triangle) (closed_hull Psquare) closed_hull := by
  ext x
  simp [closed_unit_square_eq]
  constructor
  · intro hx

    sorry
  · rintro ⟨S,(hzig | hzag),hS⟩
    · simp [zig_part_cover] at hzig
      have ⟨s, hs⟩ := hzig
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hs₀ hs₁ hs₂
        field_simp [hn] at hs₀ hs₁ hs₂
        intro i; constructor <;> (fin_cases i <;> simp; linarith)
        · sorry
        · sorry
      · sorry
    · sorry

theorem monsky_easy_direction' {n : ℕ} (hn : Even n) (hnneq : n ≠ 0)
    : (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n) := by
  have ⟨m,hm⟩ := hn
  use (zig_part_cover m ∪ zag_part_cover m)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [is_cover_iff]
    refine ⟨?_,?_⟩
    · convert zig_zag_covers_square (n := m) ?_
      · simp only [coe_union]
      · intro h; apply hnneq
        rw [hm,h,add_zero]
    · convert disjoint_aux (S₁ := zig_part_cover m) (S₂ := (zag_part_cover m : Set Triangle)) (f := open_hull) zig_open_disjoint zag_open_disjoint zig_zag_open_disjoint
      exact coe_union (zig_part_cover m) (zag_part_cover m)
  · use 1 / (2*m)
    intro Δ hΔ
    simp at hΔ
    cases' hΔ with hΔ hΔ
    · exact zig_cover_area hΔ
    · exact zag_cover_area hΔ
  · convert zig_zag_cover_size m
    linarith










/-
  Dions stuff

  For a collection of segments, we define the collection of basis segments.
  Next, we define what it means for a collection of segments to be complete,
  and we show that any segment in a complete collection is a union of basis segments.
-/

local notation "SegmentSet" => Finset Segment


instance partialorder (X : SegmentSet) : Preorder X where
  le := fun S ↦ (fun T ↦ closed_hull S.val ⊆ closed_hull T.val)
  le_refl := by exact fun a ⦃a_1⦄ a ↦ a
  le_trans := by exact fun a b c a_1 a_2 ⦃a_3⦄ a ↦ a_2 (a_1 a)


-- A basis segment is a segment that does not properly contain another segment
def basis_segment (X : SegmentSet) (S : Segment) : Prop :=
  S ∈ X ∧ ∀ T : X, closed_hull T.val ⊆ closed_hull S → closed_hull T.val = closed_hull S

-- A SegmentSet is complete if for any inclusions of segements, the closure of the complement
-- of a segment is also in the SegmentSet
def complete_segment_set : SegmentSet → Prop :=
  fun X ↦ (∀ S T : X, closed_hull S.val ⊂ closed_hull T.val → ∃ S' : X,
  (closed_hull T.val = closed_hull S.val ∪ closed_hull S'.val ∧
  ∃ p : ℝ², closed_hull S.val ∩ closed_hull S'.val = {p}))

-- A decomposition of a segment is a collection of segments covering it
def segment_covering {X : SegmentSet} (S : Segment) {n : ℕ} (f : Fin n → X) : Prop :=
  closed_hull S = ⋃ (i : Fin n), closed_hull (f i).val

-- A SegmentSet is splitting if every segment is the union of the basic segments it contains.
def splitting_segment_set (X : SegmentSet) : Prop :=
  ∀ S : Segment, S ∈ X → ∃ n : ℕ, ∃ f : Fin n → X,
  (segment_covering S f ∧ ∀ i : Fin n, basis_segment X (f i))


-- Example: if X : Segment_Set is a singleton, its only member is a basis segment
theorem singleton_has_basis (S : Segment) : basis_segment (singleton S) S  := by
  constructor
  · exact mem_singleton.mpr rfl
  · intro T
    have hTeqS : T = S := by
      rw [← Set.mem_singleton_iff]
      exact Set.mem_toFinset.mp T.2
    exact fun _ ↦ congrArg closed_hull hTeqS


theorem downward_set_complete {Y : SegmentSet} (S : Segment) (h : S ∈ Y)
(hYCompl : complete_segment_set Y) :
  complete_segment_set {T ∈ Y | closed_hull T ⊆ closed_hull S} := by
  sorry


theorem complete_is_splitting: ∀ (X : SegmentSet),
  complete_segment_set X → splitting_segment_set X := by
  apply Finset.strongInduction
  intro Y hY hYCompl S hSY
  let YS : Finset Segment := {T ∈ Y | closed_hull T ⊆ closed_hull S}
  have hYSsubY : YS ⊆ Y := filter_subset (fun T ↦ closed_hull T ⊆ closed_hull S) Y
  have hSinYS : S ∈ YS := by
    rw [mem_filter]
    exact ⟨hSY, by rfl⟩
  have hYSComp : complete_segment_set YS := downward_set_complete S hSY hYCompl
  cases' ssubset_or_eq_of_subset hYSsubY with hstrict heq
  · -- Apply induction hypothesis
    specialize hY YS hstrict hYSComp
    rcases hY S hSinYS with ⟨n, f, ⟨hl, hr⟩⟩
    use n
    let g : Fin n → {x // x ∈ Y} := fun i ↦ ⟨f i, hYSsubY (f i).2⟩
    use g
    constructor
    · calc closed_hull S = ⋃ (i : Fin n), closed_hull (f i).val := hl
        _ = ⋃ (i : Fin n), closed_hull (g i).val := by rfl
    · intro i
      constructor
      · exact coe_mem (g i)
      · intro T hT
        -- now need to prove that T is actually in YS to apply h.right
        have hTS : ↑T ∈ YS := by
          have hTinS : closed_hull T.val ⊆ closed_hull S := by
            calc closed_hull T.val ⊆ closed_hull (g i).val := hT
              _ = closed_hull (f i).val := rfl
              _ ⊆ ⋃ (i : Fin n), closed_hull (f i).val := Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
              _ = closed_hull S := by rw [← hl]
          rw [mem_filter]
          exact ⟨coe_mem T, hTinS⟩
        exact (hr i).2 ⟨T, hTS⟩ hT
  · -- if S is basis, we are done. If not, choose something in S and use completeness to
    -- apply the induction hypothesis to two smaller sets.
    by_cases hSBasis : (basis_segment Y S)
    · use 1
      let f : Fin 1 → Y := fun 0 ↦ ⟨S, hSY⟩
      use f
      constructor
      · calc closed_hull S = closed_hull (f 0).val := by rfl
          _ = ⋃ (i : Fin 1), closed_hull (f 0).val := Eq.symm (Set.iUnion_const (closed_hull (f 0).val))
          _ = ⋃ (i : Fin 1), closed_hull (f i).val := by sorry
      · intro i
        rw [Fin.fin_one_eq_zero i]
        exact hSBasis
    · -- Then need to take a complement of T and apply induction hypothesis to the two subsets
      -- of elements contained in T or its complement.
      have hT : ∃ T ∈ Y, closed_hull T ⊂ closed_hull S := by
        unfold basis_segment at hSBasis
        rw [Decidable.not_and_iff_or_not] at hSBasis
        cases' hSBasis with hl hr
        · tauto
        · rw [Decidable.not_forall] at hr
          cases' hr with T hT
          use T
          refine ⟨coe_mem T, ?_⟩
          sorry
      cases' hT with T hT
      have hComp : closed_hull T ⊂ closed_hull S → ∃ S' : Y, (closed_hull S = closed_hull T ∪ closed_hull S'.val ∧
        ∃ p : ℝ², closed_hull T ∩ closed_hull S'.val = {p}) := hYCompl ⟨T, hT.1⟩ ⟨S, hSY⟩
      specialize hComp hT.2
      cases' hComp with T' hT'
      let YT : Finset Segment := {U ∈ Y | closed_hull U ⊆ closed_hull T}
      let YT' : Finset Segment := {U ∈ Y | closed_hull U ⊆ closed_hull T'.val}
      have hYTCompl : complete_segment_set YT := downward_set_complete T hT.1 hYCompl
      have hYT'Compl : complete_segment_set YT' := downward_set_complete T' T'.2 hYCompl
      sorry



theorem basis_segments_exist (X : SegmentSet) :
  ∃ S : X, basis_segment X S := by
  sorry




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
