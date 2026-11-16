/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Solovay–Kitaev theorem for Clifford+T words

A **Clifford+T word** is a finite sequence of the letters `H`, `T` and `T⁻¹`, where `H` is the
Hadamard gate, `T = diag(1, e^{iπ/4})`, and `T⁻¹ = T⁷`. Its value is the product of its letters'
matrices, in order.

**The Solovay–Kitaev theorem** (R. Solovay, unpublished, 1995; A. Kitaev, *Quantum computations:
algorithms and error correction*, Russian Math. Surveys 52 (1997) 1191; the form here is
C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006)
81): there are constants `K > 0` and `e > 0` such that for every `ε` with `0 < ε ≤ e`, every
`U ∈ SU(2)` is within `ε` of the value of a word of length at most `K · log(1/ε)^c`, with
`c = log 5 / log (3/2) ≈ 3.97`.

* `solovay_kitaev` states this. Distances are in the operator norm (the `ℓ²` operator norm on
  `2 × 2` matrices, `Matrix.Norms.L2Operator`). The word approximates `U` itself, not `U` up to a
  phase.
* `exponent_mem_Ioo` places the exponent between `3` and `4`.

`K` and `e` are not given. The exponent is Dawson and Nielsen's, for a gate set closed under
inverses: one level of the recursion uses five shorter words, and inverting a word does not
lengthen it.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace QuantumInfo

/-- The `T` gate's phase, `e^{iπ/4}`. -/
noncomputable def tPhase : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

namespace CliffordT

/-- The Hadamard gate as a `2 × 2` matrix. -/
noncomputable def hGateM : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- The `T` gate as a `2 × 2` matrix. -/
noncomputable def tGateM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, tPhase]

end CliffordT

namespace SU2

open CliffordT

/-- The three letters: `0` is `H`, `1` is `T`, and `2` is `T⁻¹ = T⁷`. -/
noncomputable def ctGen : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![hGateM, tGateM, tGateM ^ 7]

/-- The value of a word: the product of its letters' matrices, in order. -/
noncomputable def ctEval (w : List (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ := (w.map ctGen).prod

end SU2

end QuantumInfo

open QuantumInfo.SU2

/-- **The Solovay–Kitaev theorem for Clifford+T words.** There are `K > 0` and `e > 0` such
that for every `ε ∈ (0, e]` and every `U ∈ SU(2)`, some word `w` over `H`, `T`, `T⁻¹` has
`‖U - ctEval w‖ ≤ ε` and length at most `K · log(1/ε)^c`, where `c = log 5 / log (3/2)`. -/
theorem solovay_kitaev :
    ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
      ∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∃ w : List (Fin 3),
        ‖U - ctEval w‖ ≤ ε ∧
          (w.length : ℝ) ≤ K * Real.log ε⁻¹ ^ (Real.log 5 / Real.log (3 / 2)) := by
  sorry

/-- The exponent `log 5 / log (3/2)` lies strictly between `3` and `4`. -/
theorem exponent_mem_Ioo : Real.log 5 / Real.log (3 / 2) ∈ Set.Ioo (3 : ℝ) 4 := by
  sorry
