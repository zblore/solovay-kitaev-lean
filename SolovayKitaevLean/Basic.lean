/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import SolovayKitaevLean.QuantumInfo.SolovayKitaevCount

/-!
# The statements of `Challenge.lean`

This file proves the two statements of `Challenge.lean` from the copied csd-lean4 files.
`solovay_kitaev` is `QuantumInfo.SU2.exists_word_approx_polylog`, restated with Mathlib's
`Matrix.specialUnitaryGroup` in place of `QuantumInfo.SU2.su2Set` and with the exponent written
out in place of `QuantumInfo.SU2.skExponent`. `exponent_mem_Ioo` is `three_lt_skExponent` and
`skExponent_lt_four`.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

open QuantumInfo.SU2

/-- **The Solovay–Kitaev theorem for Clifford+T words.** There are `K > 0` and `e > 0` such
that for every `ε ∈ (0, e]` and every `U ∈ SU(2)`, some word `w` over `H`, `T`, `T⁻¹` has
`‖U - ctEval w‖ ≤ ε` and length at most `K · log(1/ε)^c`, where `c = log 5 / log (3/2)`. -/
theorem solovay_kitaev :
    ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
      ∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∃ w : List (Fin 3),
        ‖U - ctEval w‖ ≤ ε ∧
          (w.length : ℝ) ≤ K * Real.log ε⁻¹ ^ (Real.log 5 / Real.log (3 / 2)) := by
  obtain ⟨K, e, hK, he, h⟩ := exists_word_approx_polylog
  refine ⟨K, e, hK, he, fun ε hε hεe U hU => ?_⟩
  have hU' : U ∈ su2Set := Matrix.mem_specialUnitaryGroup_iff.1 hU
  exact h ε hε hεe U hU'

/-- The exponent `log 5 / log (3/2)` lies strictly between `3` and `4`. -/
theorem exponent_mem_Ioo : Real.log 5 / Real.log (3 / 2) ∈ Set.Ioo (3 : ℝ) 4 :=
  ⟨three_lt_skExponent, skExponent_lt_four⟩
