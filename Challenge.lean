module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs

public section

/-!
# Advertised statements

Partial progress on Erdős Problem #197 (<https://www.erdosproblems.com/197>), which remains open.

Erdős #197 asks whether `ℕ` can be split into two sets, each admitting an enumeration (a listing
of order type `ω`) with no monotone 3-term arithmetic progression. A set with such an
enumeration is called *permutable*. The two statements below are Theorem I and Corollary I of
`docs/proof.md`.

**Theorem I (`Erdos197Interval.gadget`).** A linear order of the interval `[M, 2M + 6]` is
given by an injective ranking `σ` (`x` comes before `y` when `σ x < σ y`). "No monotone 3-term
AP" means: for every 3-term AP `x < y < z` of the interval, `σ y` is not strictly between
`σ x` and `σ z`. The theorem says that for `M ≥ 8` such an order cannot satisfy all eight
*anchor constraints* `2(M + j) - a` before `M + j` (`j ∈ {0, 1, 2, 3}`, `a ∈ {0, 1}`).
(The window `2M + 6` cannot be shortened to `2M + 5`: see `docs/proof.md`.)

**Corollary I (`Erdos197Interval.main_result`).** If `S ⊆ ℕ` is permutable and contains two
consecutive integers `v, v + 1`, then from some point on `S` contains no interval
`[P, 2P + 6 - v]`.

**Encoding of Corollary I.**
* An enumeration of `S` is a bijection `f : ℕ ≃ S`, read as the list `f 0, f 1, f 2, …`.
* "No monotone 3-term AP" is the predicate `¬HasMonotoneAP (Subtype.val ∘ f) 3` of
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`),
  written out by unfolding `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith`: no
  strictly increasing list of indices `l` is mapped by `Subtype.val ∘ f` onto `a, a + d, a + 2d`
  or onto `a + 2d, a + d, a`. This is the condition used in formal-conjectures'
  `Erdos197.erdos_197`; writing it out keeps this file Mathlib-only and free of new definitions.
  (It agrees with the original up to definitional unfolding of instances: here `n • d` uses
  `instSMulOfMul` for `ℕ`.)
* `2 * P + 6 - v` is truncated subtraction in `ℕ`; it is the true value `2P + 6 - v` for every
  `P ≥ v`, in particular for all large `P`.
-/

/-- **Theorem I.** For `M ≥ 8`, no injective ranking `σ` of `[M, 2M + 6]` without monotone
3-term APs puts `2(M + j) - a` before `M + j` for all `j ≤ 3` and `a ≤ 1`. -/
theorem Erdos197Interval.gadget (M : ℕ) (hM : 8 ≤ M) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc M (2 * M + 6)))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    ¬ ∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (M + j) - a) < σ (M + j) := by
  sorry

/-- **Corollary I.** Let `f : ℕ ≃ S` be an enumeration of `S ⊆ ℕ` with no monotone 3-term
arithmetic progression (formal-conjectures' `¬HasMonotoneAP (Subtype.val ∘ f) 3`, unfolded),
and let `v, v + 1 ∈ S`. Then for all large `P` the interval `[P, 2P + 6 - v]` is not contained
in `S`. -/
theorem Erdos197Interval.main_result (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (v : ℕ) (hv : v ∈ S) (hv1 : v + 1 ∈ S) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, ¬ Set.Icc P (2 * P + 6 - v) ⊆ S := by
  sorry
