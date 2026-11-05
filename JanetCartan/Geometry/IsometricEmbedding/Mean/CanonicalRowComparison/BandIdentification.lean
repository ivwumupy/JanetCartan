module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.CrossResponse
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawBandBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.IntegralSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.WaveAction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SmoothRealization
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer

/-!
# Identify the constructed sampling band with its physical cross response

The existing `RawKernel.bandKernelData` is instantiated with the measured
cross amplitude. Its real channel is proved to be the literal Hermitian cross
response of the original raw derivative integral. The detector, high-pass,
smooth band, half derivative and Fourier scalar remain in that integral.
Only the derivative integrand is masked; the background is uncut.

The actual corrected amplitude and its global extensions are supplied by
`CorrectedAtoms` and `CanonicalAtomRealization`. This identifies the response
from primitive amplitudes; no forward-map or normal equality is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison

open Sampling Sampling.RawKernel Sampling.MeanNormalBound SamplingKernelBounds
open RawInputPartition RawPrimary RawPrimary.SliceBounds
open AmplitudeBound

variable {n N : ℕ}

local instance : ContinuousENorm (Matrix (Fin N) (Fin n) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin N) (Fin n) ℂ) inferInstance).toContinuousENorm

/-- The uncut background and measurement commute through the ORIGINAL
smooth-band derivative integral. Integrability follows from continuity on
the compact wide band and the actual L² raw input
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem complexCrossMeasurement_rawSliceBandIntegral
    (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (V : Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (ζ : Euclidean (n - 1)) (τ : ℝ) (d : Euclidean (n - 1) → ℂ)
    (C : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : Matrix (Fin N) (Fin n) ℂ) (j : ℕ) (f : WideBandL2 n j)
    (x : Euclidean n) (hS : Continuous (S x)) (hV : Continuous (V x))
    (hd : Continuous d) :
    complexCrossMeasurement C B
        (rawSliceBandIntegral S V (fun _ ↦ 1) ζ τ (weightedRadialBand d j) j f x) =
      rawSliceBandIntegral S (fun y η ↦ complexCrossMeasurement C B (V y η))
        (fun _ ↦ 1) ζ τ (weightedRadialBand d j) j f x := by
  let k : Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ := fun η ↦
    (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) *
      ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j η)) • V x (ζ + τ • η)
  have hk : Continuous k := by
    have hr := (contDiff_radialBand n j (r := 0)).continuous
    dsimp [k, rawPrimaryPhaseDifference, weightedRadialBand]
    fun_prop
  have hwide : IsCompact (wideBand n j) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hint : Integrable (fun η ↦ f η • k η) (volume.restrict (wideBand n j)) :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).smul
      (memLp_restrict_compact_column hk hwide))
  have hzero (η : Euclidean (n - 1)) (hη : η ∉ wideBand n j) : k η = 0 := by
    simp [k, weightedRadialBand_eq_zero_off_wideBand d hη]
  have hcomm := (complexCrossMeasurement C B).integral_comp_comm hint
  have hleft : rawSliceBandIntegral S V (fun _ ↦ 1) ζ τ
      (weightedRadialBand d j) j f x = ∫ η in wideBand n j, f η • k η := by
    simp only [rawSliceBandIntegral, Complex.ofReal_one, one_smul,
      rawPrimaryDemodulatedIntegral]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun η hη ↦ by simp [hzero η hη])]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [k, smul_smul]
    congr 1
    ring
  rw [hleft, ← hcomm]
  simp only [rawSliceBandIntegral, Complex.ofReal_one, one_smul,
    rawPrimaryDemodulatedIntegral]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun η hη ↦ by simp [hzero η hη])]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [k, map_smul, smul_smul]
  congr 1
  ring

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] {bands : ℕ}

variable
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (V : P → Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (background : P → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      S q.1.1 q.1.2 q.2))
    (hV : ∀ p x, Continuous (V p x))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (background q.1.1 q.1.2)
        (V q.1.1 q.1.2 q.2)))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K →
      complexCrossMeasurement (C x) (background p x) (V p x η) = 0)
    (M bound : ℝ) (hM : 0 ≤ M) (hbound : 0 ≤ bound)
    (hAM : ∀ p x η, ‖complexCrossMeasurement (C x) (background p x) (V p x η)‖ ≤ M)
    (hdB : ∀ η, ‖d η‖ ≤ bound)

include hV

/-- The sampling operator CONSTRUCTED from the measured derivative amplitude
is the actual real cross response on one wide band. This retains the exact
factor two, physical Fourier normalization and uncut background
(`main:eq:canonical-identity`, `app:ch_mean_pairs:defn:mean-canonical`).
The hypotheses are the existing kernel constructor's primitive data and
continuity of the derivative amplitude, not a response-operator equality. -/
theorem real_bandKernelData_eq_measured_cross
    (j : Fin bands) (p : P) (f : WideBandL2 n j.val) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    realQuadratureChannel (wideBandKernelOperator D j.val (j, p)) f =ᵐ[volume]
      fun x ↦ C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x)
        ((2 * Real.pi) ^ (-(n : ℝ) / 2) •
          rawSliceBandIntegral (S p) (V p) (fun _ ↦ 1) (ζ p) (τ p)
            (weightedRadialBand d j.val) j.val f x)) := by
  dsimp only
  let A := fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η)
  let D := bandKernelData (J := bands) S A ζ τ d hS hA hζ hτ hτ₀ hd
    K hK hAK M bound hM hbound hAM hdB
  have hf := bandKernelData_wideOperator_ae_rawIntegral S A ζ τ d hS hA hζ hτ hτ₀ hd
    K hK hAK M bound hM hbound hAM hdB j p f
  filter_upwards [hf, Lp.coeFn_smul (2 : ℝ)
      (l2RealPart volume (wideBandKernelOperator D j.val (j, p) f)),
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL
      (wideBandKernelOperator D j.val (j, p) f)] with x hx htwo hre
  change ((2 : ℝ) • l2RealPart volume (wideBandKernelOperator D j.val (j, p) f)) x = _
  change (l2RealPart volume (wideBandKernelOperator D j.val (j, p) f)) x = _ at hre
  rw [htwo, Pi.smul_apply, hre, hx]
  have hSx : Continuous (S p x) :=
    hS.comp (f := fun η : Euclidean (n - 1) ↦ ((p, x), η)) (by fun_prop)
  have he := complexCrossMeasurement_rawSliceBandIntegral (S p) (V p) (ζ p) (τ p) d
    (C x) (background p x) j.val f x hSx (hV p x) hd
  change (2 : ℝ) • euclideanRealPart
    ((2 * Real.pi) ^ (-(n : ℝ) / 2) • rawSliceBandIntegral (S p)
      (fun y η ↦ complexCrossMeasurement (C x) (background p x) (V p y η))
      (fun _ ↦ 1) (ζ p) (τ p) (weightedRadialBand d j.val) j.val f x) = _
  rw [← he, ← (complexCrossMeasurement (C x) (background p x)).map_smul_of_tower,
    twice_real_complexCrossMeasurement]

/-- Identify every literal refined sampling prefix with the measured cross
response of the SAME finite wide-band derivative integral. The original
two-shell isometry and grouped projection are explicit; the background is
not projected or cut. This is the finite component-row identification for
`app:ch_mean_pairs:defn:mean-canonical`, before applying any adjoint or inverse. -/
theorem real_bandKernelData_prefix_eq_measured_cross
    (L : ℕ) (p : P) (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    let u := widePrefix n bands L ((wideRefinement n bands).symm v)
    realQuadratureChannel (refinedKernelPrefix D L p) v =ᵐ[volume]
      fun x ↦ C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x)
        (∑ j : Fin bands, (2 * Real.pi) ^ (-(n : ℝ) / 2) •
          rawSliceBandIntegral (S p) (V p) (fun _ ↦ 1) (ζ p) (τ p)
            (weightedRadialBand d j.val) j.val (u j) x)) := by
  dsimp only
  let A := fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η)
  let D := bandKernelData (J := bands) S A ζ τ d hS hA hζ hτ hτ₀ hd
    K hK hAK M bound hM hbound hAM hdB
  let u := widePrefix n bands L ((wideRefinement n bands).symm v)
  have he : realQuadratureChannel (refinedKernelPrefix D L p) v =
      ∑ j : Fin bands, realQuadratureChannel (wideBandKernelOperator D j.val (j, p))
        (u j) := by
    rw [realQuadratureChannel_apply, refinedKernelPrefix_eq_wideRow_projected]
    simp [wideBandKernelRow, NormalPerturbation.weightedRow_apply, u,
      Finset.smul_sum]
  change realQuadratureChannel (refinedKernelPrefix D L p) v =ᵐ[volume] _
  rw [he]
  refine (Lp.coeFn_finsetSum Finset.univ (fun j : Fin bands ↦
    realQuadratureChannel (wideBandKernelOperator D j.val (j, p)) (u j))).trans ?_
  have hsum := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦
    real_bandKernelData_eq_measured_cross S V C background ζ τ d hS hV hA hζ hτ hτ₀ hd
      K hK hAK M bound hM hbound hAM hdB j p (u j))
  refine hsum.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Finset.sum_apply]
  simp only [← CurrentMean.hermitianContinuousBilinear_apply, map_sum,
    Finset.smul_sum, u]

/-- Identify the existing smooth cross response with the constructed bounded
component on the ORIGINAL raw space. `hG` is the literal derivative-integral
output required from `CanonicalAtomRealization`, and `hbackground` fixes its
uncut zero atom on the measurement support. Their arbitrary extensions away
from that support do not enter. Neither hypothesis asserts a response or normal equality.
The result supplies `CurrentMean.completeCanonicalCorrection_toL2`'s `hraw`
for `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem smoothRawCrossResponse_toL2_eq_constructed_component
    (L : ℕ) (p : P)
    (base : CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (G : RefinedInput n bands →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hbackground : ∀ z, Cper z ≠ 0 → base.val z () =
      background p (centeredTorusRepresentative z))
    (hmeasurement : ∀ z, Cper z = C (centeredTorusRepresentative z))
    (hG : ∀ v z, Cper z ≠ 0 →
      let u := widePrefix n bands L ((wideRefinement n bands).symm v)
      (G v).val z () = ∑ j : Fin bands, (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        rawSliceBandIntegral (S p) (V p) (fun _ ↦ 1) (ζ p) (τ p)
          (weightedRadialBand d j.val) j.val (u j) (centeredTorusRepresentative z))
    (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    CurrentMean.smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v) =
      PeriodicLocalL2.transferOutputOperator
        (realQuadratureChannel (refinedKernelPrefix D L p)) v := by
  dsimp only
  let D := bandKernelData (J := bands) S
    (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
    ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
  have ha := real_bandKernelData_prefix_eq_measured_cross S V C background ζ τ d hS hV hA
    hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB L p v
  apply Lp.ext
  filter_upwards [CurrentMean.SmoothPeriodicFamily.componentL2_coe_ae ()
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v),
    PeriodicLocalL2.toTorus_coe (𝕜 := ℝ)
      (realQuadratureChannel (refinedKernelPrefix D L p) v),
    PeriodicLocalL2.measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      ha.restrict] with z hl hr hp
  change _ = (PeriodicLocalL2.toTorus (𝕜 := ℝ)
    (realQuadratureChannel (refinedKernelPrefix D L p) v)) z
  rw [CurrentMean.smoothResidualToL2, hl, CanonicalChange.smoothRawCrossResponse_apply,
    hr, hp]
  simp only [Function.comp_apply]
  rw [← hmeasurement z]
  by_cases hc : Cper z = 0
  · simp only [hc, zero_apply]
  · rw [hbackground z hc, hG v z hc]

/-- Match the sampling theorem's Fourier-normalized component with the
literal `RawPrimary` synthesis. The fixed inverse Fourier scalar is explicit
and independent of the sample weights. The finite wide bands reassemble to
the SAME raw integral, with the uncut background and factor two unchanged
(`app:ch_waves:eq:individual-representation`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem real_bandKernelData_prefix_eq_measured_rawIntegral
    (L : ℕ) (p : P) (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    let u := widePrefix n bands L ((wideRefinement n bands).symm v)
    ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
        realQuadratureChannel (refinedKernelPrefix D L p) v =ᵐ[volume]
      fun x ↦ C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x)
        (rawPrimaryDemodulatedIntegral (S p) (V p) (ζ p) (τ p) volume
          (weightedWideDensity d u) x)) := by
  dsimp only
  let D := bandKernelData (J := bands) S
    (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
    ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
  let u := widePrefix n bands L ((wideRefinement n bands).symm v)
  let c : ℝ := (2 * Real.pi) ^ (-(n : ℝ) / 2)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _).ne'
  filter_upwards [real_bandKernelData_prefix_eq_measured_cross S V C background ζ τ d
      hS hV hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB L p v,
    Lp.coeFn_smul c⁻¹ (realQuadratureChannel (refinedKernelPrefix D L p) v)] with x hx hs
  rw [hs, Pi.smul_apply, hx, ← Finset.smul_sum]
  have hSx : Continuous (S p x) :=
    hS.comp (f := fun η : Euclidean (n - 1) ↦ ((p, x), η)) (by fun_prop)
  have hsum := sum_rawSliceBandIntegral_eq_weightedWideDensity (S p) (V p) (fun _ ↦ 1)
    (ζ p) (τ p) hd.measurable hdB u x (fun _ _ ↦ ?_)
  · simp only [Complex.ofReal_one, one_smul] at hsum
    rw [hsum]
    have he (a : Matrix (Fin N) (Fin n) ℂ) :
        C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x) (c • a)) =
          c • C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x) a) := by
      simp only [← CurrentMean.hermitianContinuousBilinear_apply, map_smul]
      exact smul_comm _ _ _
    rw [he, inv_smul_smul₀ hc]
  · exact (show Continuous (fun η : Euclidean (n - 1) ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference (S p) (ζ p) (τ p) x η : ℂ)) •
        V p x (ζ p + τ p • η)) by
      have hVx := hV p x
      unfold rawPrimaryPhaseDifference
      fun_prop).continuousOn

/-- Identify the existing smooth cross response using exactly the raw
integral convention exported by `CanonicalAtomRealization`, without silently
adding the sampling theorem's Fourier scalar to its physical derivative.
The representation input is that producer's literal derivative formula; all
band reassembly and measured-row identification are proved here
(`app:ch_mean_pairs:defn:mean-canonical`, `main:eq:canonical-identity`). -/
theorem smoothRawCrossResponse_toL2_eq_rawIntegral_component
    (L : ℕ) (p : P)
    (base : CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (G : RefinedInput n bands →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hbackground : ∀ z, Cper z ≠ 0 → base.val z () =
      background p (centeredTorusRepresentative z))
    (hmeasurement : ∀ z, Cper z = C (centeredTorusRepresentative z))
    (hG : ∀ v z, Cper z ≠ 0 →
      (G v).val z () = rawPrimaryDemodulatedIntegral (S p) (V p) (ζ p) (τ p) volume
        (weightedWideDensity d (widePrefix n bands L ((wideRefinement n bands).symm v)))
          (centeredTorusRepresentative z))
    (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    CurrentMean.smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • PeriodicLocalL2.transferOutputOperator
        (realQuadratureChannel (refinedKernelPrefix D L p)) v := by
  dsimp only
  let D := bandKernelData (J := bands) S
    (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
    ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
  let c : ℝ := ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹
  have ha := real_bandKernelData_prefix_eq_measured_rawIntegral S V C background ζ τ d
    hS hV hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB L p v
  change _ = c • PeriodicLocalL2.toTorus (𝕜 := ℝ)
    (realQuadratureChannel (refinedKernelPrefix D L p) v)
  rw [← map_smul]
  apply Lp.ext
  filter_upwards [CurrentMean.SmoothPeriodicFamily.componentL2_coe_ae ()
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v),
    PeriodicLocalL2.toTorus_coe (𝕜 := ℝ)
      (c • realQuadratureChannel (refinedKernelPrefix D L p) v),
    PeriodicLocalL2.measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp ha.restrict]
      with z hl hr hp
  rw [CurrentMean.smoothResidualToL2, hl, CanonicalChange.smoothRawCrossResponse_apply, hr, hp]
  simp only [Function.comp_apply]
  rw [← hmeasurement z]
  by_cases hz : Cper z = 0
  · simp only [hz, zero_apply]
  · rw [hbackground z hz, hG v z hz]

end JanetCartan.CanonicalRowComparison
