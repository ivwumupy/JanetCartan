module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Negative

/-!
# Negative pairings from the actual local adjoint

These deductions transfer the measured positive restriction estimates to the
physical plus pair and its real compression. The source carries its genuine
negative zero-extension norm and the test its restriction norm. All statements
concern actual local L² classes (`negative-duality`, `finite-gap-theorem`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential ArbitraryAccuracy
open Characteristic.RetardedLocalization Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem complex_inner_zeroExtend_restrictL2
    {U : Set E} (hU : MeasurableSet U) (u : LocalL2 U F) (v : H) :
    inner ℂ (SmallSupport.zeroExtend hU u) v = inner ℂ u (restrictL2 U v) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ y, U.indicator (fun x ↦ inner ℂ (u x) (v x)) y := by
      apply integral_congr_ae
      filter_upwards [SmallSupport.zeroExtend_coeFn hU u] with y hy
      rw [hy]
      by_cases hyU : y ∈ U <;> simp [hyU]
    _ = ∫ y in U, inner ℂ (u y) (v y) := integral_indicator hU
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restrictL2_coeFn U v] with y hy
      rw [hy]

/-- The real-linear local realization also has the exact complex pairing
identity with its literal adjoint. This supplies physical negative duality
without an assumed complex extension (`measured-adjoint`). -/
theorem complex_inner_localRetardedOperator_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (u : LocalL2 U F) (v : LocalL2 V F) :
    inner ℂ (localRetardedOperator hU V T u) v =
      inner ℂ u ((localRetardedOperator hU V T).adjoint v) := by
  rw [localRetardedOperator_adjoint hU hV]
  change inner ℂ (restrictL2 V (T (SmallSupport.zeroExtend hU u))) v =
    inner ℂ u (restrictL2 U (T.adjoint (SmallSupport.zeroExtend hV v)))
  rw [← complex_inner_zeroExtend_restrictL2 hU]
  rw [ContinuousLinearMap.adjoint_inner_right]
  have he := congrArg (starRingEnd ℂ)
    (complex_inner_zeroExtend_restrictL2 hV v (T (SmallSupport.zeroExtend hU u)))
  simpa only [inner_conj_symm] using he.symm

/-- A positive restriction bound for the literal complex adjoint gives the
supported/restriction negative pairing. Consumer: the physical measured pair
in `negative-duality`; the higher coefficient remains linear. -/
theorem local_complex_negative_pairing_of_restriction_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (k : ℕ) (A high : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hT : ∀ v : LocalL2 V F, MemRestrictionSobolev V k v →
      MemRestrictionSobolev U (k+1) ((localRetardedOperator hU V T).adjoint v) ∧
        restrictionSobolevNorm U (k+1) ((localRetardedOperator hU V T).adjoint v) ≤
          A*(restrictionSobolevNorm V k v+high*‖v‖))
    (u : LocalL2 U F) (v : LocalL2 V F) (hv : MemRestrictionSobolev V k v) :
    ‖inner ℂ (localRetardedOperator hU V T u) v‖ ≤
      (((q : ℝ)*scalarLocalDualityConstant (d+1) (k+1))*A*(1+high))*
        vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)*
          restrictionSobolevNorm V k v := by
  obtain ⟨hm, hn⟩ := hT v hv
  have hb : restrictionSobolevNorm U (k+1) ((localRetardedOperator hU V T).adjoint v) ≤
      (A*(1+high))*restrictionSobolevNorm V k v := by
    apply hn.trans
    calc
      _ ≤ A*(restrictionSobolevNorm V k v+high*restrictionSobolevNorm V k v) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_le_restrictionSobolevNorm hv) hh)) hA
      _ = _ := by ring
  rw [complex_inner_localRetardedOperator_adjoint hU hV]
  apply (norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm hU (k+1) u _ hm).trans
  have hc : 0 ≤ ((q : ℝ)*scalarLocalDualityConstant (d+1) (k+1))*
      vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (scalarLocalDualityConstant_pos _ _).le) (norm_nonneg _)
  convert mul_le_mul_of_nonneg_left hb hc using 1
  ring

/-- The complex physical `H⁻¹ → L²` endpoint follows from its actual adjoint's
restriction `L² → H¹` estimate (`finite-gap-theorem`). -/
theorem local_complex_negative_one_to_L2_of_restriction_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (A high : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hT : ∀ v : LocalL2 V F, MemRestrictionSobolev V 0 v →
      MemRestrictionSobolev U 1 ((localRetardedOperator hU V T).adjoint v) ∧
        restrictionSobolevNorm U 1 ((localRetardedOperator hU V T).adjoint v) ≤
          A*(restrictionSobolevNorm V 0 v+high*‖v‖)) (u : LocalL2 U F) :
    ‖localRetardedOperator hU V T u‖ ≤
      (((q : ℝ)*scalarLocalDualityConstant (d+1) 1)*A*(1+high))*
        vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hU u) := by
  let z := localRetardedOperator hU V T u
  have hp := local_complex_negative_pairing_of_restriction_adjoint hU hV T 0 A high hA hh hT
    u z (memRestrictionSobolev_zero hV z)
  have hc : 0 ≤ (((q : ℝ)*scalarLocalDualityConstant (d+1) 1)*A*(1+high))*
      vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hU u) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg q)
      (scalarLocalDualityConstant_pos _ _).le) hA) (by linarith)) (norm_nonneg _)
  change ‖z‖ ≤ _
  by_cases hz : ‖z‖ = 0
  · rw [hz]; exact hc
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz))).mp
    change ‖inner ℂ z z‖ ≤ _ at hp
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm] at hp
    simpa only [Nat.zero_add, Nat.cast_one, restrictionSobolevNorm_zero hV] using hp

/-- Real local adjoint duality for the measured physical compression, using the
existing real component norm and genuine weak extensions (`negative-duality`). -/
theorem local_real_negative_pairing_of_restriction_adjoint
    {U V : Set E} (hU : MeasurableSet U)
    (R : LocalL2 U RF →L[ℝ] LocalL2 V RF) (k : ℕ) (A high : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hR : ∀ v : LocalL2 V RF, MemRestrictionSobolev V k v →
      MemRestrictionSobolev U (k+1) (R.adjoint v) ∧
        restrictionSobolevNorm U (k+1) (R.adjoint v) ≤
          A*(restrictionSobolevNorm V k v+high*‖v‖))
    (u : LocalL2 U RF) (v : LocalL2 V RF) (hv : MemRestrictionSobolev V k v) :
    |inner ℝ (R u) v| ≤
      (localDualityConstant (d+1) (k+1) (EuclideanSpace.basisFun (Fin q) ℝ)*A*(1+high))*
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ)
          (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)*restrictionSobolevNorm V k v := by
  obtain ⟨hm, hn⟩ := hR v hv
  have hb : restrictionSobolevNorm U (k+1) (R.adjoint v) ≤
      (A*(1+high))*restrictionSobolevNorm V k v := by
    apply hn.trans
    calc
      _ ≤ A*(restrictionSobolevNorm V k v+high*restrictionSobolevNorm V k v) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_le_restrictionSobolevNorm hv) hh)) hA
      _ = _ := by ring
  rw [← ContinuousLinearMap.adjoint_inner_right]
  apply (abs_inner_le_negativeNorm_mul_restrictionSobolevNorm
    (EuclideanSpace.basisFun (Fin q) ℝ) hU (k+1) u _ hm).trans
  have hc := mul_nonneg (localDualityConstant_pos (d+1) (k+1) (EuclideanSpace.basisFun (Fin q) ℝ)).le
    (componentFourierSobolevNorm_nonneg (EuclideanSpace.basisFun (Fin q) ℝ)
      (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u))
  convert mul_le_mul_of_nonneg_left hb hc using 1
  ring

/-- The real physical compression has the genuine `H⁻¹ → L²` bound, deduced
from its literal adjoint's positive restriction endpoint (`finite-gap-theorem`). -/
theorem local_real_negative_one_to_L2_of_restriction_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (R : LocalL2 U RF →L[ℝ] LocalL2 V RF) (A high : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hR : ∀ v : LocalL2 V RF, MemRestrictionSobolev V 0 v →
      MemRestrictionSobolev U 1 (R.adjoint v) ∧ restrictionSobolevNorm U 1 (R.adjoint v) ≤
        A*(restrictionSobolevNorm V 0 v+high*‖v‖)) (u : LocalL2 U RF) :
    ‖R u‖ ≤ (localDualityConstant (d+1) 1 (EuclideanSpace.basisFun (Fin q) ℝ)*A*(1+high))*
      componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ) (-1)
        (SmallSupport.zeroExtend hU u) := by
  have hp := local_real_negative_pairing_of_restriction_adjoint hU R 0 A high hA hh hR
    u (R u) (memRestrictionSobolev_zero hV (R u))
  have hc : 0 ≤ (localDualityConstant (d+1) 1 (EuclideanSpace.basisFun (Fin q) ℝ)*A*(1+high))*
      componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ) (-1)
        (SmallSupport.zeroExtend hU u) :=
    mul_nonneg (mul_nonneg (mul_nonneg (localDualityConstant_pos _ _ _).le hA) (by linarith))
      (componentFourierSobolevNorm_nonneg _ _ _)
  by_cases hz : ‖R u‖ = 0
  · rw [hz]; exact hc
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg (R u)) (Ne.symm hz))).mp
    simpa only [Nat.zero_add, Nat.cast_one, restrictionSobolevNorm_zero hV,
      real_inner_self_eq_norm_sq, abs_pow, abs_mul, abs_norm, pow_two] using hp

end JanetCartan.RegularSector.FiniteAssembly
