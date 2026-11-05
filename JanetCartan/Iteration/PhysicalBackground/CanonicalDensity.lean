module

public import JanetCartan.Iteration.PhysicalBackground.Admission
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.InitializedProofCache

/-!
# Density constants depending only on the original masks

The Fourier synthesis estimates must be chosen before the source scale and
physical history. The auxiliary datum below is used ONLY to supply the two
fixed masks to the existing synthesis theorem; no physical mean, carrier
operator, inverse or current geometry is taken from it. Every actual density
is synthesized from the supplied native current raw datum. Consumer:
`app:ch_background:prop:bg-current` and the native original-current application.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalBackground
open ContinuumRow CanonicalConic

/-- Smooth representatives of the actual carrier measure are unique; used to
transfer finite-low admission to the SAME previously constructed density. -/
theorem densityCarrierMeasure_open_pos (n : ℕ) : (carrierMeasure n).IsOpenPosMeasure := by
  unfold carrierMeasure
  infer_instance

/-- A mask-only input for the Fourier constants, never a physical carrier. -/
private def synthesisMaskData {n N : ℕ} (z : Euclidean 3) (θ : Euclidean (n - 1))
    {a w : ℝ} (ha : 0 < a) (hw : 0 < w) : CarrierData n N where
  outputChart := ∅
  chartPoint := 0
  transportedPosition := 0
  covector := 0
  normalField := 0
  stressFrame := 0
  measurementCutoff := 0
  angularCutoff := angularMask z θ ha hw
  highCutoff := FixedCutoffs.highFrequency

private theorem synthesisMaskData_angular_smooth {n N : ℕ}
    (z : Euclidean 3) (θ : Euclidean (n - 1)) {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    ContDiff ℝ ∞ (fun p : CarrierVariable n ↦
      ((synthesisMaskData (N := N) z θ ha hw).angularCutoff p.1 p.2 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (angularMask_smooth z θ ha hw)

private theorem synthesisMaskData_angular_compact {n N : ℕ}
    (z : Euclidean 3) (θ : Euclidean (n - 1)) {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    HasCompactSupport (fun p : CarrierVariable n ↦
      ((synthesisMaskData (N := N) z θ ha hw).angularCutoff p.1 p.2 : ℂ)) := by
  change HasCompactSupport (Complex.ofReal ∘ Function.uncurry (angularMask z θ ha hw))
  exact (angularMask_compact z θ ha hw).comp_left (g := Complex.ofReal) Complex.ofReal_zero

private theorem synthesisMaskData_high_le {n N : ℕ}
    (z : Euclidean 3) (θ : Euclidean (n - 1)) {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (t : ℝ) :
    |(synthesisMaskData (N := N) z θ ha hw).highCutoff t| ≤ 1 := by
  exact (abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc t).1).trans_le
    (FixedCutoffs.highFrequency_mem_Icc t).2

private theorem synthesisMaskData_angular_le {n N : ℕ}
    (z : Euclidean 3) (θ : Euclidean (n - 1)) {a w : ℝ} (ha : 0 < a) (hw : 0 < w)
    (p : CarrierParameter) (η : Euclidean (n - 1)) :
    |(synthesisMaskData (N := N) z θ ha hw).angularCutoff p η| ≤ 1 := by
  exact (abs_of_nonneg (angularMask_mem_Icc z θ ha hw p η).1).trans_le
    (angularMask_mem_Icc z θ ha hw p η).2

/- All density estimates use constants depending only on the fixed canonical
masks and the original initial-label compact sets, before any source scale,
current carrier or raw input (`app:ch_background:eq:bg-current-profile`). -/
proof_from canonicalDensityEstimates
    {n N : ℕ} {ι : Type} [Fintype ι]
    (z : ι → Euclidean 3) (θ : ι → Euclidean (n - 1))
    {a w : ι → ℝ} (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (hKin : ∀ i, IsCompact (Kin i)) :=
  exists_uncut_density_estimates
    (fun i ↦ synthesisMaskData (N := N) (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_smooth (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_compact (z i) (θ i) (ha i) (hw i))
    (fun _ ↦ FixedCutoffs.highFrequency_smooth)
    (fun _ _ ht ↦ FixedCutoffs.highFrequency_zero ht)
    (fun i ↦ synthesisMaskData_high_le (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_le (z i) (θ i) (ha i) (hw i)) Kin hKin

/- The finite-low threshold, like the high constants, is fixed before σ and
history. The later application must prove the actual raw bound; it cannot use
this theorem as a substitute for that bound (`app:ch_background:prop:bg-current`). -/
proof_from canonicalDensityAdmission
    {n N : ℕ} {ι : Type} [Fintype ι]
    (z : ι → Euclidean 3) (θ : ι → Euclidean (n - 1))
    {a w : ι → ℝ} (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (hKin : ∀ i, IsCompact (Kin i)) (κ : ℕ) :=
  exists_uncut_density_admission
    (fun i ↦ synthesisMaskData (N := N) (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_smooth (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_compact (z i) (θ i) (ha i) (hw i))
    (fun _ ↦ FixedCutoffs.highFrequency_smooth)
    (fun _ _ ht ↦ FixedCutoffs.highFrequency_zero ht)
    (fun i ↦ synthesisMaskData_high_le (z i) (θ i) (ha i) (hw i))
    (fun i ↦ synthesisMaskData_angular_le (z i) (θ i) (ha i) (hw i)) Kin hKin κ

end JanetCartan.PhysicalBackground
end
