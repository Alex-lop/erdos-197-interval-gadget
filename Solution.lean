module

public import Erdos197Interval

public section

/-!
# Proved solution

Comparator checks that the declarations below have exactly the statements of their
counterparts in `Challenge.lean` and use only the permitted axioms. The proofs live in
`Erdos197Interval/Basic.lean`.
-/

theorem Erdos197Interval.gadget (M : ℕ) (hM : 8 ≤ M) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc M (2 * M + 6)))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    ¬ ∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (M + j) - a) < σ (M + j) :=
  Erdos197Interval.gadget_thm M hM σ hσ hAP

theorem Erdos197Interval.main_result (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (v : ℕ) (hv : v ∈ S) (hv1 : v + 1 ∈ S) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, ¬ Set.Icc P (2 * P + 6 - v) ⊆ S :=
  Erdos197Interval.corollary S f hf v hv hv1
