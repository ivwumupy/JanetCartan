module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectConstruction.L2Consequences
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Assembly

/-!
# The actual inverse localizer and the measured physical residual

Identify the existing L²-to-Lᵖ implementation with the measured whole-space
operator, retaining the real physical plus pair and both cutoff positions.
This supplies the common operator needed to apply the restriction estimates
in `exists_finite_direct_fixed_inverse` (`app:ch_regular:eq:one-gain-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric Filter MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization
namespace JanetCartan.FixedDomainInverse
open LocalSobolev SmallSupport RegularSector.Realization RegularSector.FiniteAssembly
open FourierIntegral.LowBounds RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization
open CharacteristicTransport.CompleteResidual

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem inclusion_zeroExtend_bumpL2 {W : Set E} (hW : MeasurableSet W)
    {x : E} (χ : ContDiffBump x) (u : LocalL2 W RF) :
    l2ComplexInclusion volume (zeroExtend hW (bumpL2 (p := 2) le_rfl χ u)) =
      sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ)
        (l2ComplexInclusion volume (zeroExtend hW u)) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL
      (zeroExtend hW (bumpL2 (p := 2) le_rfl χ u)),
    zeroExtend_bumpL2_coeFn hW χ u,
    sourceCutMultiplier_coeFn χ χ.continuous (bump_norm_le_one χ)
      (l2ComplexInclusion volume (zeroExtend hW u)),
    euclideanComplexInclusion.coeFn_compLpL (zeroExtend hW u),
    zeroExtend_coeFn hW u] with y hi hz hm hi' hz'
  change (euclideanComplexInclusion (ι := Fin q)).compLpL 2 volume
    (zeroExtend hW (bumpL2 (p := 2) le_rfl χ u)) y = _
  rw [hi, hz, hm]
  simp only [l2ComplexInclusion]
  rw [hi', hz', map_smul]
  ext j
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.real_smul]

private theorem real_measuredOperator_coeFn {W : Set E} (hW : MeasurableSet W)
    {x : E} (χ₂ χ₃ : ContDiffBump x) (T : H →L[ℂ] H) (u : LocalL2 W RF) :
    realCompression (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) T) (zeroExtend hW u) =ᵐ[volume]
      fun y ↦ χ₂ y • realCompression T
        (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ u)) y := by
  let z := l2ComplexInclusion volume (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ u))
  change l2RealPart volume (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂)
    (T (sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
      (l2ComplexInclusion volume (zeroExtend hW u))))) =ᵐ[volume] _
  rw [← inclusion_zeroExtend_bumpL2 hW χ₃ u]
  filter_upwards [euclideanRealPart.coeFn_compLpL
      (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂) (T z)),
    sourceCutMultiplier_coeFn χ₂ χ₂.continuous (bump_norm_le_one χ₂) (T z),
    euclideanRealPart.coeFn_compLpL (T z)] with y hr hm hr'
  change (euclideanRealPart (ι := Fin q)).compLpL 2 volume
    (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂) (T z)) y =
      χ₂ y • (euclideanRealPart (ι := Fin q)).compLpL 2 volume (T z) y
  rw [hr, hm, hr']
  ext j
  simp only [euclideanRealPart_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The literal localizer used by the Neumann inverse is the measured real
physical pair of the SAME residual, not a replacement chosen at each order
(`app:ch_regular:thm:exact-correction`, `app:ch_regular:eq:one-gain-tame`). -/
theorem localizedResidual_eq_real_measuredOperator
    {W : Set E} (hW : MeasurableSet W) (c : E) {r : ℝ} (hr : 0 < r)
    (hUW : ball c r ⊆ W) (T : H →L[ℂ] H)
    (hmem : ∀ u, MemRestrictionSobolev (ball c r) 1
      (localRealCompression hW (ball c r) (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, restrictionSobolevNorm (ball c r) 1
      (localRealCompression hW (ball c r) (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u)
        ≤ M*‖u‖)
    {x : E} (χ₂ χ₃ : ContDiffBump x) (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ ball c r) :
    localizedResidual (two_lt_ballSobolevExponent c hr).le χ₂ χ₃ isOpen_ball.measurableSet
        (residualToLpOnBall c hr hUW _ hmem hM hbound) =
      localRealCompression hW W (physicalPairedSectorSum {()} (fun _ : Unit ↦
        measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) T)) := by
  rw [physicalPair_measuredOperator]
  let P := physicalPairedSectorSum {()} (fun _ : Unit ↦ T)
  ext1 u
  apply Lp.ext
  have hR := (ae_restrict_iff' isOpen_ball.measurableSet).mp
    (localRealCompression_coeFn hW (ball c r) P (bumpL2 (p := 2) le_rfl χ₃ u))
  filter_upwards [localizedResidual_residualToLpOnBall_coeFn c hr hUW
      (localRealCompression hW (ball c r) P) hmem hM hbound χ₂ χ₃ u,
    localRealCompression_coeFn hW W
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) P) u,
    ae_restrict_of_ae (real_measuredOperator_coeFn hW χ₂ χ₃ P u),
    ae_restrict_of_ae hR] with y hK hmeas hreal hR
  rw [hK, hmeas, hreal]
  by_cases hy : y ∈ ball c r
  · rw [indicator_of_mem hy, hR hy]
  · rw [indicator_of_notMem hy,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hs₂ h)), zero_smul, zero_smul]

end JanetCartan.FixedDomainInverse
