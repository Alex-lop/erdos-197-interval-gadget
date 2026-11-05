module

public import Solution

public section

/-! Sharpness of Theorem I at `M = 8`: with the window `[M, 2M + 5]` in place of `[M, 2M + 6]`
the hypotheses of `Erdos197Interval.gadget` are satisfiable, together with every anchor
constraint whose top `2(M + j) - a` lies in the window (all but `j = 3, a = 0`, whose top is
`2M + 6`). So the hypotheses of Theorem I are not contradictory by themselves, and the constant
`6` cannot be lowered to `5`. The order below was found by `chk/nv/find.py 8 21`; the kernel
re-checks it here. -/

/-- An order of `[8, 21]`: `15` first, `14` last. -/
def ord : List ℕ := [15, 19, 21, 11, 13, 17, 16, 20, 18, 9, 8, 12, 10, 14]

/-- The ranking of that order. -/
def rk (x : ℕ) : ℕ := ord.idxOf x

theorem window5_sat : ∃ σ : ℕ → ℕ, Set.InjOn σ (Set.Icc 8 21) ∧
    (∀ x y z : ℕ, x ∈ Set.Icc 8 21 → z ∈ Set.Icc 8 21 → x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) ∧
    (∀ j a : ℕ, j ≤ 3 → a ≤ 1 → 2 * (8 + j) - a ≤ 21 →
        σ (2 * (8 + j) - a) < σ (8 + j)) := by
  have inj : ∀ x < 22, ∀ y < 22, 8 ≤ x → 8 ≤ y → rk x = rk y → x = y := by decide
  have ap : ∀ x < 22, ∀ d < 8, 8 ≤ x ∧ 0 < d ∧ x + 2 * d ≤ 21 →
      ¬ (rk x < rk (x + d) ∧ rk (x + d) < rk (x + 2 * d)) ∧
      ¬ (rk (x + 2 * d) < rk (x + d) ∧ rk (x + d) < rk x) := by decide
  have anc : ∀ j < 4, ∀ a < 2, 2 * (8 + j) - a ≤ 21 → rk (2 * (8 + j) - a) < rk (8 + j) := by
    decide
  refine ⟨rk, fun x hx y hy h => ?_, fun x y z hx hz hxy hyz hd => ?_,
    fun j a hj ha h => anc j (by omega) a (by omega) h⟩
  · rw [Set.mem_Icc] at hx hy
    exact inj x (by omega) y (by omega) hx.1 hy.1 h
  · rw [Set.mem_Icc] at hx hz
    obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
    obtain rfl : z = x + 2 * d := by omega
    exact ap x (by omega) d (by omega) ⟨hx.1, by omega, by omega⟩

/-- The same window with the eighth constraint added (its top `22` lies outside `[8, 21]`, so
the order above cannot be used), i.e. Theorem I at `M = 8`, follows from the main theorem. -/
example : ¬ ∃ σ : ℕ → ℕ, Set.InjOn σ (Set.Icc 8 22) ∧
    (∀ x y z : ℕ, x ∈ Set.Icc 8 22 → z ∈ Set.Icc 8 22 → x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) ∧
    (∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (8 + j) - a) < σ (8 + j)) :=
  fun ⟨σ, h₁, h₂, h₃⟩ => Erdos197Interval.gadget 8 le_rfl σ h₁ h₂ h₃

#print axioms window5_sat
