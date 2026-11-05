module

public import JanetCartan.Iteration.PhysicalForwardMean.OriginalScalar
public import JanetCartan.Iteration.PhysicalForwardMean.NativeRegularity
public import JanetCartan.Iteration.PhysicalScalarChannel.Native

/-!
# Actual original bare single-channel tester in the forward convention

The scalar36 tester and the individual raw operator use the SAME original
single refined-shell measure, same full finite-parameter phase, scalar plateau,
angular/high-pass masks and every refined band copy. There are NO sample
weights or counts here. Multiplication of this bare mask by sqrt|η| recovers
exactly the original full halfweighted mask of the individual raw operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalSampling PhysicalSamplingShells PhysicalScalarChannel PhysicalMean
open Sampling Sampling.MeasuredAmplitude SamplingKernelBounds
open RawPrimary.MaskProfiles RawInputPartition ContinuumRow NormalComparison
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

/-- The bare single-channel scalar mask, INCLUDING c_n and ALL original smooth
masks, but excluding the raw operator's halfweight. No sample factor is present. -/
def singleBareScalarMask {n J : ℕ} (d : Euclidean (n - 1) → ℝ)
    (u : RefinedIndex J × Euclidean (n - 1)) : ℝ :=
  (2 * Real.pi) ^ (-((n : ℝ) / 2)) * d u.2 * radialBand n u.1.1.val u.2

/-- Moving the exact halfweight to the original input preserves the FULL raw
operator mask, not merely its support (`app:ch_mean_pairs:eq:block-fields`). -/
theorem singleBareScalarMask_mul_sqrt {n J : ℕ} (d : Euclidean (n - 1) → ℝ)
    (u : RefinedIndex J × Euclidean (n - 1)) :
    singleBareScalarMask d u * Real.sqrt ‖u.2‖ = forwardScalarBandMask n d u.1.1.val u.2 := by
  unfold singleBareScalarMask forwardScalarBandMask
  ring

/-- Continuity of the actual single-channel bare mask, without differentiating
its frequency factors quantitatively. -/
theorem continuous_singleBareScalarMask {n J : ℕ} {d : Euclidean (n - 1) → ℝ}
    (hd : Continuous d) : Continuous (singleBareScalarMask (J := J) d) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  exact ((continuous_const.mul hd).mul (contDiff_radialBand n i.1.val (r := 0)).continuous)

/-- Compact source support comes only from the original finitely many radial
bands. No artificial one-point sample or new input cutoff is introduced. -/
theorem hasCompactSupport_singleBareScalarMask {n J : ℕ} (d : Euclidean (n - 1) → ℝ) :
    HasCompactSupport (singleBareScalarMask (J := J) d) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_univ : IsCompact (univ : Set (RefinedIndex J))).prod
      (isCompact_iUnion fun j : Fin J ↦ (hasCompactSupport_radialBand n j.val).isCompact))
  intro u hu
  refine ⟨mem_univ _, mem_iUnion.mpr ⟨u.1.1, subset_tsupport _ ?_⟩⟩
  intro hz
  exact hu (by simp only [singleBareScalarMask, hz, mul_zero])

/-- The actual original bare input support is above the high-pass floor. -/
theorem one_lt_norm_of_singleBareScalarMask_ne_zero
    {n J : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) {u : RefinedIndex J × Euclidean (n - 1)}
    (hu : singleBareScalarMask (originalForwardDetector hηb hr) u ≠ 0) : 1 < ‖u.2‖ := by
  apply one_lt_norm_of_originalForwardDetector_ne_zero hηb hr
  intro hz
  exact hu (by simp only [singleBareScalarMask, hz, mul_zero, zero_mul])

variable {m J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) (τ : ℝ) (z : Euclidean 3)

/-- The original FULL finite-parameter phase, independent of the refined copy
label. There is no linearization or new carrier. -/
def singleRetainedForwardPhase
    (u : RefinedIndex J × Euclidean (m + 1 - 1)) (x : Euclidean (m + 1)) : ℝ :=
  rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
    (extendedRetainedCarrier T center.2.1 hρ z) τ x u.2

/-- Continuity of the literal original full phase is derived from its original
retained smooth extension, not supplied as an analytic success premise. -/
theorem continuous_singleRetainedForwardPhase :
    Continuous (Function.uncurry (singleRetainedForwardPhase (J := J) T Q center hρ τ z)) := by
  let ζ := extendedRetainedCarrier T center.2.1 hρ z
  have hS := (contDiff_extendedRetainedPhase T Q).continuous
  have hplus : Continuous (fun q : (RefinedIndex J × Euclidean (m + 1 - 1)) × Euclidean (m + 1) ↦
      (q.2, ζ + τ • q.1.2)) :=
    continuous_snd.prodMk (continuous_const.fun_add (continuous_const.fun_smul (continuous_snd.comp continuous_fst)))
  have hbase : Continuous (fun q : (RefinedIndex J × Euclidean (m + 1 - 1)) × Euclidean (m + 1) ↦
      (q.2, ζ)) := continuous_snd.prodMk continuous_const
  change Continuous (fun q : (RefinedIndex J × Euclidean (m + 1 - 1)) × Euclidean (m + 1) ↦
    (extendedRetainedPhase T Q q.2 (ζ + τ • q.1.2) - extendedRetainedPhase T Q q.2 ζ) / τ)
  simpa only [Function.uncurry_apply_pair, Function.comp_def] using
    ((hS.comp hplus).fun_sub (hS.comp hbase)).div_const τ

/-- The actual scalar36 native kernel is exactly the bare `sampledMomentKernel`
used for the individual forward bound. Original scalar plateau and full phase
are unchanged (`app:ch_mean_pairs:eq:block-fields`). -/
theorem originalBareNativeKernel_eq_sampledMomentKernel
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    {ηb : Euclidean (m + 1 - 1)} {r : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r)
    (x : Euclidean (m + 1)) (u : RefinedIndex J × Euclidean (m + 1 - 1)) :
    originalBareNativeKernel T Q χ center hρ hηb hr τ z x u =
      sampledMomentKernel (singleRetainedForwardPhase T Q center hρ τ z)
        (singleBareScalarMask (originalForwardDetector hηb hr))
        (fun _ y ↦ (χ y : ℂ)) x u := by
  simp only [originalBareNativeKernel, sampledMomentKernel, singleRetainedForwardPhase,
    singleBareScalarMask, Complex.ofReal_mul, ofReal_originalForwardDetector,
    weightedRadialBand, oscillatoryFactor, one_mul, Complex.star_def, Complex.conj_ofReal]
  ring_nf

end JanetCartan.PhysicalForwardMean
