import data.real.basic
import data.real.sqrt

-- Based on https://www.khanacademy.org/math/linear-algebra

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
  (v₁ + v₂).nth i = (v₁.nth i) + (v₂.nth i) :=
  sorry

protected theorem add_comm (v₁ v₂ : vec n) : v₁ + v₂ = v₂ + v₁ := begin
  simp [(+), vec.add],
  ext,
  sorry
end

instance : is_commutative (vec n) (+) := ⟨vec.add_comm⟩

protected theorem add_assoc (v₁ v₂ v₃ : vec n) : (v₁ + v₂) + v₃ = v₁ + (v₂ + v₃) := sorry

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

protected def sum : Π {n : ℕ}, vec n → ℝ
  | 0         _ := 0
  | n@(_ + 1) v := (v.nth n) + v.drop.sum

-- Euclidian norm
noncomputable def magnitude (v : vec n) : ℝ := 
  real.sqrt (v.map (λ x, x ^ 2)).sum

def is_unit (v : vec n) : Prop := 
  v.magnitude = 1

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

noncomputable def scalars (l : linear_combination vs) : finset ℝ := vs.attach.image l

def value (l : linear_combination vs) : vec n :=
  vs.attach.fold (+) 0 (λ v, (l v) * ↑v)

end linear_combination

def span (vs : finset (vec n)) : set (vec n) :=
  { p | ∃ l : linear_combination vs, l.value = p }

def linearly_dependent (vs : finset (vec n)) : Prop :=
  ∃ (l : linear_combination vs), (l.value = 0) ∧ (l.scalars ≠ {0})

theorem more_vecs_than_dim_to_linearly_dependent (vs : finset (vec n)) :
  (vs.card > n) → linearly_dependent vs := begin
  intro h,
  simp [linearly_dependent],
  sorry
end

-- Real vector space
structure is_rvs (vs : set (vec n)) : Prop :=
  (has_zero : (0 : vec n) ∈ vs)
  (closed_smul : ∀ s (v ∈ vs), s * v ∈ vs)
  (closed_add : ∀ (v₁ ∈ vs) (v₂ ∈ vs), v₁ + v₂ ∈ vs)

def rvs (n : ℕ) := { vs : set (vec n) // is_rvs vs }

theorem span_is_rvs (vs : finset (vec n)) : 
  is_rvs (span vs) :=
  sorry


