import data.real.basic
import data.real.sqrt

-- Based on https://www.khanacademy.org/math/linear-algebra

variable {n : ℕ} 

namespace vector

protected def zero : vector ℝ n := ⟨list.repeat 0 n, by simp⟩

instance : has_zero (vector ℝ n) := ⟨vector.zero⟩

protected def add : Π {n : ℕ}, vector ℝ n → vector ℝ n → vector ℝ n
  | 0       ⟨[], _⟩        ⟨[], _⟩        := nil
  | (m + 1) ⟨hd₁::tl₁, h₁⟩ ⟨hd₂::tl₂, h₂⟩ := 
    let v₁ : vector ℝ m := ⟨tl₁, (by simp [list.length_cons] at h₁; exact h₁)⟩ in
    let v₂ : vector ℝ m := ⟨tl₂, (by simp [list.length_cons] at h₂; exact h₂)⟩ in
    cons (hd₁ + hd₂) (add v₁ v₂)

instance {n : ℕ} : has_add (vector ℝ n) := ⟨vector.add⟩

protected def mul (s : ℝ) : Π {n : ℕ}, vector ℝ n → vector ℝ n
  | 0       ⟨[], _⟩     := nil
  | (m + 1) ⟨hd::tl, h⟩ := cons (s * hd) (mul ⟨tl, (by simp [list.length_cons] at h; exact h)⟩)

infixl ` * `:70  := vector.mul

protected def neg (v : vector ℝ n) : vector ℝ n :=
  v.map (λ x, -1 * x)

instance {n : ℕ} : has_neg (vector ℝ n) := ⟨vector.neg⟩

protected def sub (v₁ v₂ : vector ℝ n) : vector ℝ n :=
  v₁ + (-v₂)

instance : has_sub (vector ℝ n) := ⟨vector.sub⟩

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

theorem line_through' (v₁ v₂ : vector ℝ n) :
  line_through v₁ v₂ = line' (v₁ - v₂) v₂ := 
  sorry

theorem line_through_symm (v₁ v₂ : vector ℝ n) :
  line_through v₁ v₂ = line_through v₂ v₁ := 
  sorry

theorem line_equations {v p : vector ℝ n} (m : fin n) :
  (p ∈ v.line) → ∃ s, p.nth m = s * (v.nth m) := 
  sorry

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
  ∃ l : linear_combination.over vs, (l.value = 0) ∧ (l.scalars.any (λ s, s ≠ 0)) 

theorem more_vecs_than_dim_to_linearly_dependent (vs : list (vector ℝ n)) :
  (vs.length > n) → linearly_dependent vs :=
  sorry


