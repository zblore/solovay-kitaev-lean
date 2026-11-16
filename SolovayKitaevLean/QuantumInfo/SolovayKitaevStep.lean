/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import SolovayKitaevLean.Analysis.CStarAlgebra.GroupCommutator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Solovay–Kitaev recursion: why the error contracts at exponent `3/2`

`GroupCommutator.lean` contracts a commutator, `CommutatorDecomposition.lean` produces one, and
`CliffordTNet.lean` supplies the base case. This file is the step that turns them into a
recursion, and the whole content is **why the exponent is `3/2` and not `1`**.

Replace each factor of a commutator by a `δ`-approximation and the naive estimate is `4δ`
(`norm_groupCommutator_sub_groupCommutator_le` in `GroupCommutator.lean`) — which contracts
**nothing**, since the input error was already `δ`. The gain comes from the commutator being
*bilinear in the deviations from the identity*: the leading term is
`(v - ṽ)w + ṽ(w - w̃) - (w - w̃)v - w̃(v - ṽ)`, every summand pairing a **factor norm** with an
**approximation error**. With the factors of `CommutatorDecomposition.lean` at `√(2ε)` and the
approximations at `δ`, that is `O(√ε · δ)` — and with `δ = ε` it is `ε^{3/2}`.

## What is proved

* `norm_mul_sub_mul_le'` — the two-factor perturbation bound in any normed ring,
  `‖AB - A′B′‖ ≤ ‖A - A′‖·‖B‖ + ‖A′‖·‖B - B′‖`, which is what makes the pairing visible;
* `norm_groupCommutator_sub_le` — **the sharp estimate**:
  `‖[V,W] - [Ṽ,W̃]‖ ≤ 4aδ(1 + a)` where `a` bounds all four distances to the identity and `δ` the
  two approximation errors. Against the `4δ` of `GroupCommutator.lean` this is smaller by a
  factor `a`, and that factor is what takes the error from `ε` to order `ε^{3/2}`;
* `norm_groupCommutator_sub_le_sqrt` — the same estimate at the factor size of
  `CommutatorDecomposition.lean`, `a = √2·√ε`:
  `‖[V,W] - [Ṽ,W̃]‖ ≤ 4√2·√ε·δ·(1 + √2·√ε)`, the `√ε · δ` form the recursion consumes;
* `skError_le_rpow` — **the error bookkeeping, in closed form**: a sequence with
  `ε_{n+1} ≤ C·ε_n^{3/2}` satisfies `C²·ε_n ≤ (C²·ε_0)^{(3/2)^n}`, by induction through
  `Real.rpow`. `SolovayKitaevCount.lean` takes logarithms of this inequality.

## Scope

**The length half of the recursion is not here.** This file proves the error bookkeeping. The
length bookkeeping (`ℓ_{n+1} = 5ℓ_n`) needs a notion of **word length** in the generating set.
`cliffordT` is `Submonoid.closure {H, T}`, a set of matrices with no length function, and the net
of `CliffordTNet.lean` is a `Finset` of matrices rather than of words. `CliffordTWords.lean`
supplies the words, their evaluation, and the net restated as words.

**The length count uses a gate set closed under inverses.** The recursion uses `Ṽ⁻¹` and
`W̃⁻¹`, so `CliffordTWords.lean` counts `T⁻¹` as a letter, and a level costs five. Over `H` and `T`
alone the exponent `log 5 / log(3/2)` still holds: replacing each `T⁻¹` in a finished word by `T⁷`
multiplies its length by at most `7`. Nothing below depends on this: the error recursion is
indifferent to it.

**No approximant is constructed.** `skError_le_rpow` is a statement about real sequences; it says
what the recursion's error does *given* the recurrence, and the recurrence is justified by the
estimates above rather than by an implemented algorithm.

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `30850da3`), file
`CsdLean4/Mathlib/QuantumInfo/SolovayKitaevStep.lean`, with imports renamed from `CsdLean4.Mathlib`
to `SolovayKitaevLean`. The code is unchanged. The comments were edited for this repository to
remove csd-lean4's internal notes and references to files that are not here.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
§3 (the recursion, eq. (1)) and §4.2, Lemma 1 (the perturbation bound); M. Nielsen, I. Chuang, *Quantum Computation and Quantum
Information*, Appendix 3; `GroupCommutator.lean`, `CommutatorDecomposition.lean`,
`CliffordTNet.lean`.
-/

@[expose] public section

namespace CSD.SolovayKitaev

variable {E : Type*}

/-! ### The pairing that makes the exponent `3/2` -/

/-- **The two-factor perturbation bound.** `AB - A′B′ = (A - A′)B + A′(B - B′)`, so each summand
pairs one *difference* with one *factor* — which is what lets a small factor norm multiply the
approximation error instead of adding to it. -/
theorem norm_mul_sub_mul_le' [NormedRing E] (A B A' B' : E) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have key : A * B - A' * B' = (A - A') * B + A' * (B - B') := by noncomm_ring
  rw [key]
  exact le_trans (norm_add_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

section CStar

variable [NormedRing E] [StarRing E] [CStarRing E]

omit [StarRing E] [CStarRing E] in
/-- The deviation of a commutator's two factors, as a single product. -/
theorem norm_mul_sub_mul_comm_sub_le {V W V' W' : E} {a δ : ℝ}
    (haW : ‖W - 1‖ ≤ a) (haV' : ‖V' - 1‖ ≤ a) (haV : ‖V - 1‖ ≤ a) (haW' : ‖W' - 1‖ ≤ a)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖(V * W - W * V) - (V' * W' - W' * V')‖ ≤ 4 * a * δ := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV
  have hid : (V * W - W * V) - (V' * W' - W' * V')
      = ((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1)) := by noncomm_ring
  have h1 : ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le' (V - 1) (W - 1) (V' - 1) (W' - 1)) ?_
    have e1 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    have e2 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    rw [e1, e2]
    have := mul_le_mul hδV haW (norm_nonneg _) hδ0
    have := mul_le_mul haV' hδW (norm_nonneg _) ha0
    nlinarith [mul_le_mul hδV haW (norm_nonneg _) hδ0,
      mul_le_mul haV' hδW (norm_nonneg _) ha0]
  have h2 : ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le' (W - 1) (V - 1) (W' - 1) (V' - 1)) ?_
    have e1 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    have e2 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    rw [e1, e2]
    nlinarith [mul_le_mul hδW haV (norm_nonneg _) hδ0,
      mul_le_mul haW' hδV (norm_nonneg _) ha0]
  rw [hid]
  calc ‖((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1))‖
      ≤ ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖
        + ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * a * δ + 2 * a * δ := add_le_add h1 h2
    _ = 4 * a * δ := by ring

/-- **The sharp commutator-perturbation estimate**, and the reason Solovay–Kitaev converges.
Replacing both factors by `δ`-approximations moves the commutator by at most `4aδ(1 + a)`, where `a`
bounds the factors' distance to the identity.

`norm_groupCommutator_sub_groupCommutator_le` in `GroupCommutator.lean` gives `4δ`, which
contracts nothing. The extra factor `a` here is what makes the error shrink: with the factors of
`CommutatorDecomposition.lean` at `a = √(2ε)` and `δ = ε`, the output error is `O(ε^{3/2})`. -/
theorem norm_groupCommutator_sub_le {V W V' W' : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {a δ : ℝ}
    (haV : ‖V - 1‖ ≤ a) (haW : ‖W - 1‖ ≤ a) (haV' : ‖V' - 1‖ ≤ a) (haW' : ‖W' - 1‖ ≤ a)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ ≤ 4 * a * δ * (1 + a) := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV
  -- the commutator as `1 + P * Q`
  have hKQ := CStarRing.groupCommutator_sub_one_eq hV hW
  have hKQ' := CStarRing.groupCommutator_sub_one_eq hV' hW'
  have hsplit : V * W * star V * star W - V' * W' * star V' * star W'
      = ((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)
        + (V' * W' - W' * V') * (star V * star W - star V' * star W') := by
    have h1 : V * W * star V * star W = 1 + (V * W - W * V) * (star V * star W) := by
      rw [← hKQ]; abel
    have h2 : V' * W' * star V' * star W' = 1 + (V' * W' - W' * V') * (star V' * star W') := by
      rw [← hKQ']; abel
    rw [h1, h2]
    noncomm_ring
  -- the trailing unitary drops out of the first term
  have hQu : (star V * star W) ∈ unitary E :=
    mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW)
  have hP : ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)‖ ≤ 4 * a * δ := by
    rw [CStarRing.norm_mul_mem_unitary _ hQu]
    exact norm_mul_sub_mul_comm_sub_le haW haV' haV haW' hδV hδW
  -- the second term pairs the commutator's own size against the adjoint error
  have hP' : ‖V' * W' - W' * V'‖ ≤ 2 * a * a := by
    refine le_trans (norm_mul_sub_mul_comm_le V' W') ?_
    nlinarith [mul_le_mul haV' haW' (norm_nonneg _) ha0]
  have hQ : ‖star V * star W - star V' * star W'‖ ≤ 2 * δ := by
    refine le_trans (CStarRing.norm_mul_sub_mul_le (Unitary.star_mem hW)
      (Unitary.star_mem hV')) ?_
    have e1 : ‖star V - star V'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδV
    have e2 : ‖star W - star W'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδW
    linarith
  calc ‖V * W * star V * star W - V' * W' * star V' * star W'‖
      ≤ ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)‖
        + ‖(V' * W' - W' * V') * (star V * star W - star V' * star W')‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ 4 * a * δ + (2 * a * a) * (2 * δ) := by
        refine add_le_add hP ?_
        refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul hP' hQ (norm_nonneg _) (by positivity)
    _ = 4 * a * δ * (1 + a) := by ring

/-- **The estimate at the factor size of `CommutatorDecomposition.lean`.** With the factors
`√2·√ε`-close to the identity, the commutator of two `δ`-approximations is within
`4√2·√ε·δ·(1 + √2·√ε)` of the commutator — the `√ε · δ` shape the recursion consumes, which at
`δ = ε` is `ε^{3/2}`. -/
theorem norm_groupCommutator_sub_le_sqrt {V W V' W' : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {ε δ : ℝ}
    (haV : ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε) (haW : ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (haV' : ‖V' - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (haW' : ‖W' - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖
      ≤ 4 * (Real.sqrt 2 * Real.sqrt ε) * δ * (1 + Real.sqrt 2 * Real.sqrt ε) :=
  norm_groupCommutator_sub_le hV hW hV' hW' haV haW haV' haW' hδV hδW

end CStar

/-! ### The error bookkeeping -/

/-- **The recursion's error, in closed form.** A sequence obeying `ε_{n+1} ≤ C·ε_n^{3/2}`
satisfies `C²·ε_n ≤ (C²·ε_0)^{(3/2)^n}`: the error is **doubly exponentially** small in the number of
levels, which is what makes the gate count only polylogarithmic. `SolovayKitaevCount.lean` takes
logarithms of this inequality. -/
theorem skError_le_rpow {C : ℝ} (hC : 0 < C) {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hrec : ∀ n, ε (n + 1) ≤ C * ε n ^ ((3 : ℝ) / 2)) (n : ℕ) :
    C ^ 2 * ε n ≤ (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n := by
  have hC2 : ((C ^ 2 : ℝ)) ^ ((3 : ℝ) / 2) = C ^ 3 := by
    rw [show (C ^ 2 : ℝ) = C ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast C 2).symm,
      ← Real.rpow_mul hC.le,
      show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  have hzero : (0 : ℝ) ≤ C ^ 2 * ε 0 := mul_nonneg (sq_nonneg C) (hε 0)
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : (0 : ℝ) ≤ C ^ 2 * ε n := mul_nonneg (sq_nonneg C) (hε n)
      set X := ε n ^ ((3 : ℝ) / 2) with hX
      have h1 : C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := by
        calc C ^ 2 * ε (n + 1) ≤ C ^ 2 * (C * X) :=
              mul_le_mul_of_nonneg_left (hrec n) (sq_nonneg C)
          _ = C ^ 3 * X := by ring
      have h2 : (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) = C ^ 3 * X := by
        rw [Real.mul_rpow (sq_nonneg C) (hε n), hC2, hX]
      calc C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := h1
        _ = (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) := h2.symm
        _ ≤ ((C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hbase ih (by norm_num)
        _ = (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ (n + 1) := by
            rw [← Real.rpow_mul hzero]
            congr 1

end CSD.SolovayKitaev

end
