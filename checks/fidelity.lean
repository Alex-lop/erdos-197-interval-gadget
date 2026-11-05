module

public import Solution
public import Mathlib.Algebra.Module.NatInt

public section

/-! Verbatim copies of the formal-conjectures definitions (commit
5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, lines 36, 51-52, 129-130, 246-247),
at top level as there (Mathlib defines none of these names). -/

variable {α : Type*} [AddCommMonoid α]

def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

/-- Corollary I restated with the formal-conjectures predicate itself; accepted by `exact`
(definitional unfolding only), so the inlined predicate of `Challenge.lean` is the same
proposition. -/
theorem fc_form (S : Set ℕ) (f : ℕ ≃ S) (hf : ¬HasMonotoneAP (Subtype.val ∘ f) 3)
    (v : ℕ) (hv : v ∈ S) (hv1 : v + 1 ∈ S) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, ¬ Set.Icc P (2 * P + 6 - v) ⊆ S := by
  exact Erdos197Interval.main_result S f hf v hv hv1

/-- Non-vacuity of Corollary I: its hypotheses can hold. The powers of two, listed increasingly,
have no 3-term AP at all, and contain the consecutive integers `v = 1` and `v + 1 = 2`. -/
theorem hyps_ok : ∃ S : Set ℕ, ∃ f : ℕ ≃ S, ¬HasMonotoneAP (Subtype.val ∘ f) 3 ∧
    1 ∈ S ∧ 1 + 1 ∈ S := by
  refine ⟨_, Equiv.ofInjective (2 ^ ·) (Nat.pow_right_injective le_rfl), ?_, ⟨0, rfl⟩,
    ⟨1, rfl⟩⟩
  rintro ⟨l, ⟨a, d, h⟩, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp [List.IsAPOfLengthWith, List.range_succ] at h
  simp at hl
  have hij : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right Nat.one_lt_two hl.1.1
  have hjk : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right Nat.two_pos hl.2
  rw [pow_succ] at hjk
  have := Nat.one_le_two_pow (n := i)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

#print axioms fc_form
#print axioms hyps_ok
