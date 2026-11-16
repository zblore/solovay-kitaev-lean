/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import SolovayKitaevLean

/-!
# Controls

* The axiom audit would catch a `sorry`: `#print axioms` reports `sorryAx` for an unproved
  statement.
* The gates are the ones `Challenge.lean` names, entry by entry: `H` has entries `±1/√2` and
  determinant `-1`, and `T = diag(1, e^{iπ/4})`, with `e^{iπ/4}` to the fourth power `-1`, so `T`
  has order exactly `8`. Neither gate is in `SU(2)`.
* The letters are what `Challenge.lean` says: `H` is its own inverse, and the third letter `T⁷` is
  the inverse of `T`. So `T⁻¹` costs one letter.
* A word is evaluated in order: the word `[T, H]` has value `T·H`.
* The norm in the theorem is the `ℓ²` operator norm. The norm of a matrix equals the norm of the
  operator it defines on `ℂ²`, and the Hadamard gate has norm `1`. The entrywise sup norm would
  give `1/√2`, and the Frobenius norm and the `ℓ∞` operator norm `√2`. The theorem is also restated
  with the operator norm's instance written out, without the scoped notation, and closed by
  `solovay_kitaev`.
-/

open Matrix

open QuantumInfo QuantumInfo.SU2 QuantumInfo.CliffordT

public theorem unproved : ∀ n : ℕ, Nonempty (Fin n) := by
  sorry

/-- info: 'unproved' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms unproved

/-! ### The gates, entry by entry -/

example : hGateM 0 0 = (Real.sqrt 2 : ℂ)⁻¹ := by simp [hGateM]
example : hGateM 0 1 = (Real.sqrt 2 : ℂ)⁻¹ := by simp [hGateM]
example : hGateM 1 0 = (Real.sqrt 2 : ℂ)⁻¹ := by simp [hGateM]
example : hGateM 1 1 = -(Real.sqrt 2 : ℂ)⁻¹ := by simp [hGateM]

example : tGateM 0 0 = 1 := by simp [tGateM]
example : tGateM 0 1 = 0 := by simp [tGateM]
example : tGateM 1 0 = 0 := by simp [tGateM]
example : tGateM 1 1 = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  simp [tGateM, tPhase]

/-- `e^{iπ/4}` to the fourth power is `-1`, so `T⁴ ≠ 1` and `T` has order `8`. -/
example : tPhase ^ 4 = -1 := tPhase_pow_four

/-- `T⁸ = 1`. -/
example : tGateM ^ 8 = 1 := tGateM_pow_eight

/-- `H` has determinant `-1`, so it is not in `SU(2)`. -/
example : hGateM.det = -1 := by
  have h2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hGateM, Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, h2]
  norm_num

/-! ### The letters -/

/-- `H` is its own inverse. -/
example : ctGen 0 * ctGen 0 = 1 := by
  simpa [ctGen] using hGateM_mul_self

/-- The third letter is the inverse of `T`. -/
example : ctGen 1 * ctGen 2 = 1 := by
  have h1 : ctGen 1 = tGateM := rfl
  have h2 : ctGen 2 = tGateM ^ 7 := rfl
  rw [h1, h2, ← pow_succ', tGateM_pow_eight]

/-- And `T` is the inverse of the third letter. -/
example : ctGen 2 * ctGen 1 = 1 := by
  have h1 : ctGen 1 = tGateM := rfl
  have h2 : ctGen 2 = tGateM ^ 7 := rfl
  rw [h1, h2, ← pow_succ, tGateM_pow_eight]

/-! ### Words -/

/-- The empty word is the identity. -/
example : ctEval [] = 1 := rfl

/-- A word is evaluated in order: `[T, H]` has value `T·H`. -/
example : ctEval [1, 0] = tGateM * hGateM := by simp [ctEval, ctGen]

/-! ### The norm -/

section Norm

open scoped Matrix.Norms.L2Operator

/-- The norm of a matrix is the norm of the operator it defines on `ℂ²`. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A‖ = ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A‖ := rfl

/-- The Hadamard gate has norm `1`, as a unitary does in the operator norm. -/
example : ‖hGateM‖ = 1 := CStarRing.norm_of_mem_unitary hGateM_mem_unitary

end Norm

/-- The theorem with the operator norm's instance written out. -/
example : ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
    ∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∃ w : List (Fin 3),
      @Norm.norm _ Matrix.instL2OpNormedRing.toNorm (U - ctEval w) ≤ ε ∧
        (w.length : ℝ) ≤ K * Real.log ε⁻¹ ^ (Real.log 5 / Real.log (3 / 2)) :=
  solovay_kitaev
