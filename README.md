# Erdős #197: the anchored gadget $[M,2M+6]$ is infeasible

> **Status: PARTIAL result toward Erdős #197, NOT a solution.** This repository does **not** solve [Erdős Problem #197](https://www.erdosproblems.com/197), which is still open. It proves, and formally verifies in Lean 4, a finite obstruction (Theorem I) and its consequence for permutable sets (Corollary I).

## The result

Erdős #197 (Erdős–Graham) asks whether $\mathbb N$ can be partitioned into two sets, each with an enumeration (a listing of order type $\omega$) that contains no monotone 3-term arithmetic progression. Call such a set *permutable*. Davis–Entringer–Graham–Simmons (1977) showed that $\mathbb N$ itself is not permutable. Kasel (arXiv:2609.02939, 2026) showed that the dyadic partition fails, using a finite *order gadget*.

**Theorem I.** For every $M\ge8$, no linear order of the interval $[M,2M+6]$ that has no monotone 3-term AP satisfies the eight *anchor constraints*
$$2(M+j)-a\ \text{ comes before }\ M+j\qquad(j\in\{0,1,2,3\},\ a\in\{0,1\}).$$

These are the constraints forced on the interval by an enumeration that lists $0$ and $1$ before all of it: if $a$ is listed before $w$ and $2w-a$ is listed too, then $2w-a$ must come before $w$.

**Corollary I.** If $S\subseteq\mathbb N$ is permutable and $v,v+1\in S$, then there is $P_0$ such that no interval $[P,\,2P-v+6]$ with $P\ge P_0$ is contained in $S$.

**Context.** Kasel conjectured (his Remark 30) that his gadget $\mathrm{OG}(M)$ is infeasible for every $M\ge16$. This was proved in Lean in [the-omega-institute/trureturing PR #9626](https://github.com/the-omega-institute/trureturing/pull/9626). In the terms above, $\mathrm{OG}(M)$ is the same gadget on the longer window $[M',2M'+13]$, and the PR's theorem gives Corollary I with $2P-v+13$. Theorem I shortens the window to $2P-v+6$. The constant $6$ is optimal for Theorem I as stated ($M\ge8$): for $M=8$ the window $[M,2M+5]$ admits an order satisfying every anchor constraint that lies in it, which the Lean kernel checks ([`checks/nonvacuity.lean`](checks/nonvacuity.lean)). SAT computations (two independent encodings) find such orders for 12 other $M\le90$ as well. That is evidence, not proof, for the conjecture that this happens for infinitely many $M$, in which case the argument of Corollary I cannot give a shorter window. See [`docs/proof.md`](docs/proof.md), Sections 6 and 7. An earlier, independent partial result on #197 from the same project is [Alex-lop/erdos-197-bounded-lag](https://github.com/Alex-lop/erdos-197-bounded-lag).

**Idea of the proof.** Kasel's ladder lemmas (zigzag and flood) propagate order information along residue classes. Applied to the whole interval, the zigzag lemma fixes a *leading parity* $\pi$: every point of that parity comes before both of its neighbours. Two derived rules then turn one comparison with a far-away point into a statement about a point's immediate neighbours (Rule A for odd distances, Rule B for distances $\equiv2\bmod4$). The proof splits into $16$ cases ($M\bmod 8$ times $\pi$). In ten of them two adjacent centres near $3M/2$ are forced to "lead" simultaneously, which the zigzag lemma forbids (Lemma I, the four-flood cycle of PR #9626). In the other six one centre and a single extra 3-term progression give the contradiction (Lemma II, new). The whole argument is in [`docs/proof.md`](docs/proof.md).

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The two statements to audit (Mathlib-only, proofs `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statements, proved. |
| [`Erdos197Interval/Basic.lean`](Erdos197Interval/Basic.lean) | The proof: ladder lemmas, Rules A and B, Lemmas I and II, the 16 cases, Corollary I. |

```lean
theorem Erdos197Interval.gadget (M : ℕ) (hM : 8 ≤ M) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc M (2 * M + 6)))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    ¬ ∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (M + j) - a) < σ (M + j)

theorem Erdos197Interval.main_result (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (v : ℕ) (hv : v ∈ S) (hv1 : v + 1 ∈ S) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, ¬ Set.Icc P (2 * P + 6 - v) ⊆ S
```

How to read them:

- In `gadget`, a linear order of $[M,2M+6]$ is an injective ranking `σ`: $x$ comes before $y$ when `σ x < σ y`. Every linear order of a finite set has such a ranking, so nothing is lost. `hAP` says that no 3-term AP $x<y<z$ of the interval has `σ y` strictly between `σ x` and `σ z`. The conclusion says the eight anchor constraints cannot all hold.
- In `main_result`, an enumeration of $S$ is `f : ℕ ≃ S`, listing `f 0, f 1, f 2, …`. The `¬ ∃ l …` clause is `¬HasMonotoneAP (Subtype.val ∘ f) 3` from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjectures/ErdosProblems/197.lean) with the definitions unfolded. It is the predicate used in formal-conjectures' `Erdos197.erdos_197`, and is written out the same way as in the earlier repository [Alex-lop/erdos-197-bounded-lag](https://github.com/Alex-lop/erdos-197-bounded-lag).
- $\mathbb N$ is Lean's $\{0,1,2,\dots\}$, as in formal-conjectures; the proof does not care. `2 * P + 6 - v` is truncated subtraction, which is the true value for every $P\ge v$.

Checks performed (Lean `v4.35.0`, Mathlib `v4.35.0`):

- `lake build` succeeds. Its only warnings are the two deliberate `sorry`s in `Challenge.lean`. There is no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` anywhere else.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for both theorems.
- The statements in `Challenge.lean` and `Solution.lean` elaborate to identical terms (checked with `pp.all`; the outputs are byte-identical).
- In `checks/fidelity.lean`, verbatim copies of formal-conjectures' `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith` are used to restate Corollary I. `Erdos197Interval.main_result` proves that restatement by `exact`, i.e. by definitional unfolding alone.
- Non-vacuity (`checks/nonvacuity.lean` and `checks/fidelity.lean`):
  - The hypotheses of `gadget` are satisfiable once the window is shortened by one. An explicit order of $[8,21]$ has no monotone 3-term AP and satisfies all seven anchor constraints whose top lies in $[8,21]$; the kernel checks it with `decide`. So `gadget` is sharp as stated ($M\ge8$), and its hypotheses are not contradictory by themselves.
  - The hypotheses of `main_result` are satisfiable: the powers of two, listed increasingly, contain $v=1$, $v+1=2$ and no 3-term AP.
- `check-lean-sources.py` and `validate-formalization.rb` from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) (commit `2891de4`) pass. The scripts are not vendored here; copy them from the template to rerun them.

The repository follows the [Palomar](https://palomar-registry.org) layout, with `comparator.json` and `formalization.yaml`. It has **not** been submitted to the registry.

To build:

```sh
lake exe cache get   # download Mathlib build files
lake build
```

## Reproducing the checks

After `lake build`, run `lake env lean checks/fidelity.lean` and `lake env lean checks/nonvacuity.lean` from the repository root. The first file copies formal-conjectures' `List.IsAPOfLengthWith`, `List.IsAPOfLength` and `HasMonotoneAP` verbatim from commit [`5d8b04d3`](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean), restates Corollary I with them (`fc_form`, proved from `Erdos197Interval.main_result` by `exact`) and shows that the hypotheses of Corollary I can hold (`hyps_ok`). The second checks the order of $[8,21]$ from Section 6 of [`docs/proof.md`](docs/proof.md) by `decide` (`window5_sat`). Both end with `#print axioms`, which reports only `propext`, `Classical.choice` and `Quot.sound`. The search script named in `checks/nonvacuity.lean` and the SAT computations of Section 6 are work notes and are not included.

## Use of AI

This work was produced by **Claude Fable 5.1** and **Claude Opus 5.5** (Anthropic), running in Claude Code, under the direction of **Alex Lopez**. Claude Fable 5.1 found the hand proof of Theorem I; Claude Opus 5.5 wrote the Lean formalization and this repository. The hand proof was checked by three adversarial AI referees (proof, computation and scope), and the Lean kernel checks both theorems. The informal proof in `docs/proof.md` has **not** been refereed by a human.

## License

Apache-2.0; see [LICENSE](LICENSE).
