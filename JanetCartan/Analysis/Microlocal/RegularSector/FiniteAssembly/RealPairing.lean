module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# The real physical pair on the actual restriction spaces

For real inputs the compression of `S+cSc` is twice the real part of the
same S. Apply the existing weak-extension fiber maps, without identifying
Fourier and restriction norms. The finite direct constructor supplies the
complex `L² → H¹` estimate used here; the literal real adjoint exchanges the
original domains (`finite-gap-theorem`, `measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open Realization LocalSobolev Characteristic.RetardedLocalization
open JanetCartan.ArbitraryAccuracy.ResidualLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem realPart_star {μ : Measure E} (u : Lp F 2 μ) :
    l2RealPart μ (star u) = l2RealPart μ u := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (star u),
    euclideanRealPart.coeFn_compLpL u, Lp.coeFn_star u] with y hs hr hu
  change euclideanRealPart.compLpL 2 μ (star u) y = euclideanRealPart.compLpL 2 μ u y
  rw [hs, hr, hu]
  ext j
  exact Complex.conj_re _

private theorem restrict_star (V : Set E) (u : H) :
    restrictL2 V (star u) = star (restrictL2 V u) := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn V (star u), Lp.coeFn_star (restrictL2 V u),
    ae_restrict_of_ae (Lp.coeFn_star u), restrictL2_coeFn V u] with y hy hz hu hv
  rw [hy, hz, hu]
  simp only [Pi.star_apply, hv]

/-- The actual physical plus pairing on real local data, preserving literal
zero extension and both masks inside T (`real-sector-normalization`). -/
theorem localRealCompression_physicalPair
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H)
    (u : LocalL2 U RF) :
    localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u =
      (2 : ℝ) • localRealCompression hU V T u := by
  have he := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU u
  change l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at he
  simp only [physicalPairedSectorSum, Finset.sum_singleton]
  change l2RealPart (volume.restrict V)
      (restrictL2 V (T (SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u)) +
        star (T (star (SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u)))))) = _
  rw [← he, star_inclusion, map_add, restrict_star, map_add, realPart_star]
  rw [two_smul ℝ, he]
  rfl

/-- The real compressed physical pair inherits the actual complex local
`L² → Hˢ` bound. The constant four is independent of the coefficients and s;
the weak-jet order is unchanged (`finite-gap-theorem`). -/
theorem localRealCompression_physicalPair_restriction_bound
    {U V : Set E} (hU : MeasurableSet U) (T : H →L[ℂ] H) (s : ℕ) (A : ℝ)
    (hA : 0 ≤ A)
    (hT : ∀ u : LocalL2 U F,
      MemRestrictionSobolev V s (localRetardedOperator hU V T u) ∧
      restrictionSobolevNorm V s (localRetardedOperator hU V T u) ≤ A*‖u‖)
    (u : LocalL2 U RF) :
    MemRestrictionSobolev V s
        (localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ∧
      restrictionSobolevNorm V s
        (localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ≤
          (4*A)*‖u‖ := by
  obtain ⟨hm, hn⟩ := hT (l2ComplexInclusion (volume.restrict U) u)
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound (euclideanRealPart (ι := Fin q)) hm
  change MemRestrictionSobolev V s (localRealCompression hU V T u) at hr
  change restrictionSobolevNorm V s (localRealCompression hU V T u) ≤ _ at hnr
  have hi : ‖l2ComplexInclusion (volume.restrict U) u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (l2ComplexInclusion (volume.restrict U)).le_of_opNorm_le
      (l2ComplexInclusion_norm_le _) u
  have hrbound : restrictionSobolevNorm V s (localRealCompression hU V T u) ≤ (2*A)*‖u‖ := by
    calc
      _ ≤ (‖euclideanRealPart (ι := Fin q)‖+1) * (A*‖u‖) :=
        hnr.trans (mul_le_mul_of_nonneg_left
          (hn.trans (mul_le_mul_of_nonneg_left hi hA)) (by positivity))
      _ ≤ 2*(A*‖u‖) := mul_le_mul_of_nonneg_right
        (by linarith [euclideanRealPart_norm_le (ι := Fin q)]) (mul_nonneg hA (norm_nonneg u))
      _ = _ := by ring
  rw [localRealCompression_physicalPair]
  refine ⟨hr.smul 2, ?_⟩
  rw [restrictionSobolevNorm_smul hr]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- Both orientations of the SAME real physical pair inherit the uniform
restriction endpoint. The second conclusion is its literal real Hilbert
adjoint, with U and V exchanged (`measured-adjoint`, `finite-gap-theorem`). -/
theorem localRealCompression_physicalPair_restriction_bounds
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (s : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u : LocalL2 U F,
      MemRestrictionSobolev V s (localRetardedOperator hU V T u) ∧
      restrictionSobolevNorm V s (localRetardedOperator hU V T u) ≤ A*‖u‖)
    (ha : ∀ v : LocalL2 V F,
      MemRestrictionSobolev U s ((localRetardedOperator hU V T).adjoint v) ∧
      restrictionSobolevNorm U s ((localRetardedOperator hU V T).adjoint v) ≤ A*‖v‖) :
    let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
    (∀ u : LocalL2 U RF, MemRestrictionSobolev V s (R u) ∧
      restrictionSobolevNorm V s (R u) ≤ (4*A)*‖u‖) ∧
    (∀ v : LocalL2 V RF, MemRestrictionSobolev U s (R.adjoint v) ∧
      restrictionSobolevNorm U s (R.adjoint v) ≤ (4*A)*‖v‖) := by
  refine ⟨localRealCompression_physicalPair_restriction_bound hU T s A hA hf, ?_⟩
  intro v
  rw [localRealCompression_adjoint hU hV, physicalPairedSectorSum_adjoint_eq]
  apply localRealCompression_physicalPair_restriction_bound hV T.adjoint s A hA _ v
  simpa only [localRetardedOperator_adjoint hU hV] using ha

end JanetCartan.RegularSector.FiniteAssembly
