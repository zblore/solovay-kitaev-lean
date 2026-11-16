/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import SolovayKitaevLean

/-!
# Axioms of the main results

Fails if a main result, or a key lemma, comes to depend on anything beyond Lean's three standard
axioms.
-/

/--
info: 'solovay_kitaev' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solovay_kitaev

/--
info: 'exponent_mem_Ioo' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exponent_mem_Ioo

/--
info: 'QuantumInfo.SU2.exists_word_approx_polylog' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_word_approx_polylog

/--
info: 'QuantumInfo.SU2.exists_mem_skWords_norm_sub_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_mem_skWords_norm_sub_le

/--
info: 'QuantumInfo.SU2.exists_word_net' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_word_net

/--
info: 'QuantumInfo.SU2.su2Set_subset_closure_cliffordT' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2Set_subset_closure_cliffordT

/--
info: 'QuantumInfo.SU2.exists_commutator_of_det_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_commutator_of_det_one

/--
info: 'CSD.SolovayKitaev.norm_groupCommutator_sub_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.norm_groupCommutator_sub_le

/--
info: 'CSD.SolovayKitaev.skError_le_rpow' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.skError_le_rpow

/--
info: 'QuantumInfo.SU2.length_le_of_mem_skWords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.length_le_of_mem_skWords

/--
info: 'QuantumInfo.SU2.det_ctEval_pow_eight' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.det_ctEval_pow_eight
