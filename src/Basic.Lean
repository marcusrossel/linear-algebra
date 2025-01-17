import data.real.basic
import data.real.sqrt

-- Based on https://www.khanacademy.org/math/linear-algebra

prefix `√`:60 := real.sqrt

def vec (n : ℕ) := fin n → ℝ

variable {n : ℕ} 

namespace vec

abbreviation nth (v : vec n) (i : fin n) : ℝ := v i

def drop (v : vec (n + 1)) : vec n :=
  λ i, v.nth i

def map (v : vec n) (f : ℝ → ℝ) : vec n :=
  λ i, f (v.nth i)

protected abbreviation zero : vec n := 
  λ _, 0

instance : has_zero (vec n) := ⟨vec.zero⟩

theorem zero_nth_zero (i : fin n) : (0 : vec n).nth i = 0 := 
  rfl

protected def add (v₁ v₂ : vec n) : vec n :=
  λ i, v₁.nth i + v₂.nth i

instance {n : ℕ} : has_add (vec n) := ⟨vec.add⟩

theorem add_pointwise (v₁ v₂ : vec n) (i : fin n) : 
  (v₁ + v₂).nth i = (v₁.nth i) + (v₂.nth i) := by finish

protected theorem add_comm (v₁ v₂ : vec n) : 
  v₁ + v₂ = v₂ + v₁ := by 
  { simp [(+), vec.add], ext, finish }

instance : is_commutative (vec n) (+) := ⟨vec.add_comm⟩

protected theorem add_assoc (v₁ v₂ v₃ : vec n) : 
  (v₁ + v₂) + v₃ = v₁ + (v₂ + v₃) := begin
  simp [(+), vec.add],
  ext,
  sorry
end

instance : is_associative (vec n) (+) := ⟨vec.add_assoc⟩

protected def smul (s : ℝ) (v : vec n) : vec n :=
  λ i, s * (v.nth i)

infixl ` * `:70  := vec.smul

theorem smul_pointwise (s : ℝ) (v : vec n) (i : fin n) : 
  (s * v).nth i = s * (v.nth i) :=
  sorry

theorem smul_one_neutral (v : vec n) : 1 * v = v := sorry

theorem smul_add_distributive (s : ℝ) (v₁ v₂ : vec n) : 
  s * (v₁ + v₂) = (s * v₁) + (s * v₂) := begin
  sorry
end

theorem add_smul_distributive (s₁ s₂ : ℝ) (v : vec n) : 
  (s₁ + s₂) * v = (s₁ * v) + (s₂ * v) := begin
  sorry
end

protected def neg (v : vec n) : vec n :=
  λ i, -(v.nth i)

instance {n : ℕ} : has_neg (vec n) := ⟨vec.neg⟩

theorem neg_neg (v : vec n) : -(-v) = v := sorry

theorem neg_eq_smul_neg_one (v : vec n) : -v = (-1) * v := sorry

protected def sub (v₁ v₂ : vec n) : vec n :=
  v₁ + (-v₂)

instance : has_sub (vec n) := ⟨vec.sub⟩

theorem sub_eq_add_neg (v₁ v₂ : vec n) : v₁ - v₂ = v₁ + (-v₂) := rfl

theorem sub_eq_zero {v₁ v₂ : vec n} : 
  (v₁ - v₂) = 0 ↔ v₁ = v₂ :=
  sorry

def dot_prod (v₁ v₂ : vec n) : ℝ :=
  finset.univ.sum (λ i, (v₁ i) * (v₂ i))

infixl ` ⬝ `:70  := vec.dot_prod

theorem dot_prod_comm (v₁ v₂ : vec n) : 
  v₁ ⬝ v₂ = v₂ ⬝ v₁ := by
  simp [dot_prod, mul_comm]

theorem add_dot_prod_distrib (v₁ v₂ v₃ : vec n) : 
  (v₁ + v₂) ⬝ v₃ = (v₁ ⬝ v₃) + (v₂ ⬝ v₃) := begin
  sorry
end

theorem smul_dot_prod_distrib (v₁ v₂ : vec n) (s : ℝ) : 
  s * (v₁ ⬝ v₂) = (s * v₁) ⬝ (s * v₂) := begin
  sorry
end

theorem sub_dot_prod_distrib (v₁ v₂ v₃ : vec n) : 
  (v₁ - v₂) ⬝ v₃ = (v₁ ⬝ v₃) - (v₂ ⬝ v₃) := begin
  sorry
end

-- Euclidian norm
noncomputable def magnitude (v : vec n) : ℝ := 
  √ finset.univ.sum (λ i, (v i) ^ 2)

notation `∥` v `∥`  := vec.magnitude v

theorem magnitude_squared_eq_self_dot_prod (v : vec n) :
  ∥v∥ ^ 2 = (v ⬝ v) := begin
  simp [magnitude, dot_prod],
  have h : 0 ≤ finset.univ.sum (λ i, (v i) ^ 2) := finset.sum_nonneg (λ _ _, sq_nonneg _),
  rw [real.sq_sqrt h],
  congr,
  ext i,
  exact sq (v i)
end

theorem cauchy_schwarz_inequality (v₁ v₂ : vec n) :
  |v₁ ⬝ v₂| ≤ ∥v₁∥ * ∥v₂∥ := begin
  let p : ℝ → ℝ := λ t, ∥(t * v₂) - v₁∥ ^ 2,
  have hp₁ : ∀ t, 0 ≤ p t := sorry,
  have hp₂ : ∀ t, p t = (v₂ ⬝ v₂) * (t ^ 2) - 2 * (v₁ ⬝ v₂) * t + (v₁ ⬝ v₁) := begin
    intro t,
    calc 
      p t = ∥(t * v₂) - v₁∥ ^ 2 : rfl
      ... = (t * v₂ - v₁) ⬝ (t * v₂ - v₁) : magnitude_squared_eq_self_dot_prod _
      ... = (t * v₂) ⬝ (t * v₂ - v₁) - v₁ ⬝ (t * v₂ - v₁) : sub_dot_prod_distrib _ _ _
      ... = (t * v₂ - v₁) ⬝ (t * v₂) - v₁ ⬝ (t * v₂ - v₁) : by rw [dot_prod_comm]
      ... = (t * v₂) ⬝ (t * v₂) - v₁ ⬝ (t * v₂) - v₁ ⬝ (t * v₂ - v₁) : by rw [sub_dot_prod_distrib]
      ... = _ : sorry
  end,
  let a := v₂ ⬝ v₂,
  let b := 2 * (v₁ ⬝ v₂),
  let c := v₁ ⬝ v₁,
  let t := b / (2 * a),
  have hp₃ : p t = -(b ^ 2 / 4 * a) + c := sorry,
  sorry
end

def is_unit (v : vec n) : Prop := 
  ∥v∥ = 1

-- Set of colinear vectors
def line (v : vec n) : set (vec n) :=
  { p | ∃ s, p = s * v }

-- Line with rise `vᵣ` that runs through point `vₚ`
def line' (vᵣ vₚ : vec n) : set (vec n) :=
  { p | ∃ s, p = vₚ + s * vᵣ }

def line_through (v₁ v₂ : vec n) : set (vec n) :=
  line' (v₁ - v₂) v₁

theorem line_through_point_agnostic (v₁ v₂ : vec n) :
  line_through v₁ v₂ = line' (v₁ - v₂) v₂ := begin
  simp [line_through, line'],
  ext,
  constructor 
  ; intro h
  ; obtain ⟨s, hs⟩ := h
  ; simp [hs],
  {
    existsi s + 1,
    -- TODO: Try calc mode
    simp [sub_eq_add_neg, smul_add_distributive, ←vec.add_assoc],
    conv in (v₁ + s * v₁) { rw [←(smul_one_neutral v₁)] },
    conv in (s * (1 * v₁)) { rw [smul_one_neutral] },
    conv in ((1 * v₁) + (s * v₁)) { rw [←add_smul_distributive] },
    conv begin to_rhs, rw [vec.add_comm] end,
    conv in (v₂ + (s + 1) * v₁) { rw [←(neg_neg v₂), neg_eq_smul_neg_one] },
    conv begin to_rhs, rw [←vec.add_assoc, ←add_smul_distributive] end,
    simp [vec.add_comm, add_comm],
  },
  {
    existsi s - 1,
    sorry 
  }
end
   
theorem line_through_symm (v₁ v₂ : vec n) :
  line_through v₁ v₂ = line_through v₂ v₁ :=  begin
  simp [line_through, line'],
  ext,
  constructor
  ; intro h
  ; obtain ⟨s, hs⟩ := h
  ; simp [hs],
  {
    existsi -(s + 1),
    sorry -- TODO: This needs all kinds of laws for +, -, * on vectors.
  },
  {
    existsi -(s + 1),
    sorry -- TODO: This needs all kinds of laws for +, -, * on vectors.
  }
end

theorem line_equations {v p : vec n} (m : fin n) :
  (p ∈ v.line) → ∃ s, p.nth m = s * (v.nth m) := begin
  intro h,
  simp [line] at h,
  obtain ⟨s, hs⟩ := h,
  existsi s,
  simp [hs, smul_pointwise]
end

end vec

def linear_combination (vs : finset (vec n)) := { v // v ∈ vs } → ℝ

namespace linear_combination

variable {vs : finset (vec n)}

def ext_iff (l₁ l₂ : linear_combination vs) :
  (l₁ = l₂) ↔ (∀ v, l₁ v = l₂ v) := begin
  constructor,
  finish,
  { intros h, ext v, exact h v }
end

noncomputable def scalars (l : linear_combination vs) : finset ℝ := vs.attach.image l

theorem mem_scalars_iff (l : linear_combination vs) (s : ℝ) :
  (s ∈ l.scalars) ↔ (∃ v, l v = s) := 
  by simp [scalars]

theorem mem_scalars (l : linear_combination vs) (v) :
  (l v) ∈ l.scalars := begin
  simp [scalars],
  existsi v.val,
  existsi v.property,
  simp
end

theorem scalars_singleton {l : linear_combination vs} {s : ℝ} :
  l.scalars = {s} → ∀ v, l v = s := begin
  intros h v,
  have hm := l.mem_scalars v,
  rw [h] at hm,
  exact finset.mem_singleton.mp hm
end

def value (l : linear_combination vs) : vec n :=
  vs.attach.fold (+) 0 (λ v, (l v) * ↑v)

protected def sub (l₁ l₂ : linear_combination vs) : linear_combination vs :=
  λ v, l₁ v - l₂ v

instance : has_sub (linear_combination vs) := ⟨linear_combination.sub⟩

theorem sub_value (l₁ l₂ : linear_combination vs) : 
  (l₁ - l₂).value = l₁.value - l₂.value := 
  sorry

theorem sub_mem_scalars_iff (l₁ l₂ : linear_combination vs) (s : ℝ) :
  (s ∈ (l₁ - l₂).scalars) ↔ (∃ v, s = l₁ v - l₂ v) := begin
  simp [mem_scalars_iff],
  constructor
  ; intro h
  ; obtain ⟨v, hv, h⟩ := h
  ; existsi v
  ; existsi hv
  ; exact h.symm
end

end linear_combination

def span (vs : finset (vec n)) : set (vec n) :=
  { p | ∃ l : linear_combination vs, l.value = p }

abbreviation linearly_dependent (vs : finset (vec n)) : Prop :=
  ∃ (l : linear_combination vs), (l.value = 0) ∧ (l.scalars ≠ {0})

abbreviation linearly_independent (vs : finset (vec n)) : Prop :=
  ¬(linearly_dependent vs) 

theorem more_vecs_than_dim_to_linearly_dependent (vs : finset (vec n)) :
  (vs.card > n) → linearly_dependent vs := begin
  intro h,
  sorry
end

-- Real vector space
structure is_rvs (vs : set (vec n)) : Prop :=
  (has_zero : (0 : vec n) ∈ vs)
  (closed_smul : ∀ s (v ∈ vs), s * v ∈ vs)
  (closed_add : ∀ (v₁ ∈ vs) (v₂ ∈ vs), v₁ + v₂ ∈ vs)

def rvs (n : ℕ) := { vs : set (vec n) // is_rvs vs }

instance : has_coe (rvs n) (set (vec n)) := ⟨subtype.val⟩

theorem span_is_rvs (vs : finset (vec n)) : 
  is_rvs (span vs) :=
  sorry

structure basis (ρ : rvs n) :=
  (vectors : finset (vec n))
  (indep : linearly_independent vectors)
  (spans : span vectors = ρ)

theorem basis.unique_lin_comb {v : vec n} {ρ : rvs n} (b : basis ρ) {l₁ l₂ : linear_combination b.vectors} :
  (v ∈ ρ.val) → (l₁.value = v) → (l₂.value = v) → l₁ = l₂ := begin
  intros hv hl₁ hl₂,
  rw [linear_combination.ext_iff],
  intro x,
  have hl := vec.sub_eq_zero.mpr (hl₁.trans hl₂.symm),
  rw [←linear_combination.sub_value] at hl,
  have hi := (not_exists.mp b.indep) (l₁ - l₂),
  have h := (not_and_distrib.mp hi).resolve_left (not_not.mpr hl),
  simp at h,
  have hz := linear_combination.scalars_singleton h x,
  exact sub_eq_zero.mp hz
end


