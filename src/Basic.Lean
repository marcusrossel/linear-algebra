import data.real.basic
import data.real.sqrt

-- Based on https://www.khanacademy.org/math/linear-algebra

variable {n : ℕ} 

namespace vector

protected abbreviation zero : vector ℝ n := ⟨list.repeat 0 n, by simp⟩

instance : has_zero (vector ℝ n) := ⟨vector.zero⟩

theorem zero_nth_zero (i : fin n) : (0 : vector ℝ n).nth i = 0 :=
  by apply list.nth_le_repeat

protected def add : Π {n : ℕ}, vector ℝ n → vector ℝ n → vector ℝ n
  | 0       ⟨[], _⟩        ⟨[], _⟩        := nil
  | (m + 1) ⟨hd₁::tl₁, h₁⟩ ⟨hd₂::tl₂, h₂⟩ := 
    let v₁ : vector ℝ m := ⟨tl₁, (by simp [list.length_cons] at h₁; exact h₁)⟩ in
    let v₂ : vector ℝ m := ⟨tl₂, (by simp [list.length_cons] at h₂; exact h₂)⟩ in
    (hd₁ + hd₂) ::ᵥ (add v₁ v₂)

instance {n : ℕ} : has_add (vector ℝ n) := ⟨vector.add⟩

protected theorem add_comm (v₁ v₂ : vector ℝ n) : v₁ + v₂ = v₂ + v₁ := sorry

protected theorem add_assoc (v₁ v₂ v₃ : vector ℝ n) : (v₁ + v₂) + v₃ = v₁ + (v₂ + v₃) := sorry

protected def smul (s : ℝ) : Π {n : ℕ}, vector ℝ n → vector ℝ n
  | 0       ⟨[], _⟩     := nil
  | (m + 1) ⟨hd::tl, h⟩ := cons (s * hd) (smul ⟨tl, (by simp [list.length_cons] at h; exact h)⟩)

infixl ` * `:70  := vector.smul

theorem smul_pointwise (s : ℝ) (v : vector ℝ n) (i : fin n) : 
  (s * v).nth i = s * (v.nth i) := begin
  cases n,
  { exact fin_zero_elim i },
  {
    obtain ⟨v, _⟩ := v,
    cases v with hd tl,
    { contradiction },
    {
      simp [vector.smul, vector.nth],
      -- TODO: By cases. If i = 0 we get the head, otherwise the tail.
      sorry
    }
  }
end

theorem smul_one_neutral (v : vector ℝ n) : 1 * v = v := sorry

theorem smul_add_distributive (s : ℝ) (v₁ v₂ : vector ℝ n) : 
  s * (v₁ + v₂) = (s * v₁) + (s * v₂) := begin
  sorry
end

theorem add_smul_distributive (s₁ s₂ : ℝ) (v : vector ℝ n) : 
  (s₁ + s₂) * v = (s₁ * v) + (s₂ * v) := begin
  sorry
end


protected def neg (v : vector ℝ n) : vector ℝ n :=
  v.map (λ x, -1 * x)

instance {n : ℕ} : has_neg (vector ℝ n) := ⟨vector.neg⟩

theorem neg_neg (v : vector ℝ n) : -(-v) = v := sorry

theorem neg_eq_smul_neg_one (v : vector ℝ n) : -v = (-1) * v := sorry

protected def sub (v₁ v₂ : vector ℝ n) : vector ℝ n :=
  v₁ + (-v₂)

instance : has_sub (vector ℝ n) := ⟨vector.sub⟩

theorem sub_eq_add_neg (v₁ v₂ : vector ℝ n) : v₁ - v₂ = v₁ + (-v₂) := rfl

protected def sum : Π {n : ℕ}, vector ℝ n → ℝ
  | 0       ⟨[], _⟩     := 0
  | (m + 1) ⟨hd::tl, h⟩ := 
    let v : vector ℝ m := ⟨tl, (by simp [list.length_cons] at h; exact h)⟩ in
    hd + v.sum

-- Euclidian norm
noncomputable def magnitude (v : vector ℝ n) : ℝ := 
  real.sqrt (v.map (λ x, x ^ 2)).sum

def is_unit (v : vector ℝ n) : Prop := 
  v.magnitude = 1

-- Set of colinear vectors
def line (v : vector ℝ n) : set (vector ℝ n) :=
  { p | ∃ s, p = s * v }

-- Line with rise `vᵣ` that runs through point `vₚ`
def line' (vᵣ vₚ : vector ℝ n) : set (vector ℝ n) :=
  { p | ∃ s, p = vₚ + s * vᵣ }

def line_through (v₁ v₂ : vector ℝ n) : set (vector ℝ n) :=
  line' (v₁ - v₂) v₁

theorem line_through_point_agnostic (v₁ v₂ : vector ℝ n) :
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
    simp [sub_eq_add_neg, smul_add_distributive, ←vector.add_assoc],
    conv in (v₁ + s * v₁) { rw [←(smul_one_neutral v₁)] },
    conv in (s * (1 * v₁)) { rw [smul_one_neutral] },
    conv in ((1 * v₁) + (s * v₁)) { rw [←add_smul_distributive] },
    conv begin to_rhs, rw [vector.add_comm] end,
    conv in (v₂ + (s + 1) * v₁) { rw [←(neg_neg v₂), neg_eq_smul_neg_one] },
    conv begin to_rhs, rw [←vector.add_assoc, ←add_smul_distributive] end,
    simp [vector.add_comm, add_comm],
  },
  {
    existsi s - 1,
    sorry 
  }
end
   
theorem line_through_symm (v₁ v₂ : vector ℝ n) :
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

theorem line_equations {v p : vector ℝ n} (m : fin n) :
  (p ∈ v.line) → ∃ s, p.nth m = s * (v.nth m) := begin
  intro h,
  simp [line] at h,
  obtain ⟨s, hs⟩ := h,
  existsi s,
  simp [hs, smul_pointwise]
end

end vector

def linear_combination (n : ℕ) := list (ℝ × (vector ℝ n))

namespace linear_combination

def vectors (l : linear_combination n) : list (vector ℝ n) := l.map prod.snd

def over (vs : list (vector ℝ n)) :=
  { l : linear_combination n // (l.map prod.snd) = vs }

variable {vs : list (vector ℝ n)}

def over.scalars (l : linear_combination.over vs) : list ℝ := l.val.map prod.fst

def over.value (l : linear_combination.over vs) : vector ℝ n :=
  l.val.foldl (λ v e, v + e.fst * e.snd) 0

end linear_combination

def span (vs : list (vector ℝ n)) : set (vector ℝ n) :=
  { p | ∃ l : linear_combination.over vs, l.value = p }

def linearly_dependent (vs : list (vector ℝ n)) : Prop :=
  ∃ (l : linear_combination.over vs) (i : ℕ) (h : i < l.scalars.length), (l.value = 0) ∧ (l.scalars.nth_le i h ≠ 0) 

theorem more_vecs_than_dim_to_linearly_dependent (vs : list (vector ℝ n)) :
  (vs.length > n) → linearly_dependent vs := begin
  intro h,
  simp [linearly_dependent],
  -- TODO: Is it easier to prove this by contradiction?
  -- by_contra hc, 
  -- simp at hc,
  sorry
end


