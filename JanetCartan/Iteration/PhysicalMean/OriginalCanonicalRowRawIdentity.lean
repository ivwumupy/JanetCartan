module
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredMoment
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActiveBaseline
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampled
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampledBaseline
public meta import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowActualBridge
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredAmplitude
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
/-!
# The original zero-safe raw column

Reassemble the SAME whole annular G, with its full angular factor and κ,
into the original raw primary integral. Only the fixed Fourier constant
is cancelled. The original graph support identifies the native and retained
carriers in the active branch; the inactive branch is proved separately.
The prefix and sample transports retain the original unscaled baseline,
common measurement, selected shift, outer sample, and bounded A. Consumers:
`fixedSourceLinear_low_error` and `app:ch_mean_pairs:defn:mean-canonical`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition RawPrimary.MaskProfiles RawPrimary.SliceBounds
open PhysicalForwardMean NormalComparison OriginalMeanQuadraticProfiles.Actual
private theorem cancel_forward_scalar (s b d r h ψ e w v : ℂ) (hs : s ≠ 0) :
    b * (s * d * r) * h * e * (s⁻¹ * (ψ * w)) * v =
      b * ψ * (h * (d * r) * v * (e * w)) := by
  field_simp [hs]

/-- Exact raw scalar algebra of the actual forward slice. Only the fixed
nonzero Fourier convention cancels; the original carrier and detector remain
undivided (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem forwardSlice_band_eq_scaled_raw {n N J : ℕ}
    (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (Z : Euclidean 3) (ζ : Euclidean (n-1)) (τ b : ℝ)
    (φ : Euclidean (n-1) → Euclidean n → ℝ) (det : Euclidean (n-1) → ℝ)
    (j : RefinedIndex J) (η : Euclidean (n-1)) (x : Euclidean n) (v : ℂ) :
    ((fun a c ↦ physicalForwardKernel φ
      (fun η ↦ (b * singleBareScalarMask det (j,η)) * Real.sqrt ‖η‖)
      (forwardSlice ψ B Z ζ τ a c) x η * v) : Matrix (Fin N) (Fin n) ℂ) =
      (b * ψ x) • (((Real.sqrt ‖η‖ : ℂ) *
        weightedRadialBand (fun η ↦ (det η : ℂ)) j.1.val η * v) •
        (Complex.exp (Complex.I * (φ η x : ℂ)) • B (x,Z,ζ + τ • η))) := by
  have hc : (((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _).ne'
  simp only [neg_div] at hc
  ext a c
  simp only [physicalForwardKernel,sampledMomentKernel,star_star,forwardSlice,
    observedForwardAmplitude,forwardNormalization,singleBareScalarMask,
    weightedRadialBand,oscillatoryFactor,one_mul,neg_div,Complex.ofReal_mul,
    Complex.ofReal_inv,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  exact cancel_forward_scalar _ _ _ _ _ _ _ _ _ hc
open scoped Matrix.Norms.Frobenius
open PhysicalSamplingShells RawInputRealization
/-- Reassemble the SAME whole native annular response, keeping the observation
and carrier outside, not inside a reweighted input measure. -/
theorem forwardSlice_annuli_eq_scaled_raw {n N J : ℕ}
    (S : Euclidean n → Euclidean (n-1) → ℝ) (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (Z : Euclidean 3) (ζ : Euclidean (n-1)) (τ b : ℝ)
    (det : Euclidean (n-1) → ℝ) (d : Euclidean (n-1) → ℂ)
    (hd : Continuous d) (bound : ℝ) (hbound : 0 ≤ bound)
    (hdB : ∀ η, ‖d η‖ ≤ bound) (hdet : ∀ η, d η = (det η : ℂ))
    (v : RefinedInput n J) (x : Euclidean n)
    (hS : Continuous (S x)) (hB : Continuous (fun ξ ↦ B (x,Z,ξ))) :
    (∑ j : RefinedIndex J, (∫ η,
      ((fun a c ↦ physicalForwardKernel
        (fun η x ↦ rawPrimaryPhaseDifference S ζ τ x η)
        (fun η ↦ (b * singleBareScalarMask det (j,η)) * Real.sqrt ‖η‖)
        (forwardSlice ψ B Z ζ τ a c) x η * v j η) : Matrix (Fin N) (Fin n) ℂ)
      ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ)) =
      (b * ψ x) • rawPrimaryDemodulatedIntegral S (fun x ξ ↦ B (x,Z,ξ)) ζ τ volume
        (weightedWideDensity d ((wideRefinement n J).symm v)) x := by
  have he : d = fun η ↦ (det η : ℂ) := funext hdet
  rw [he] at hd hdB ⊢
  have hc : Continuous (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) •
        B (x,Z,ζ + τ • η)) := by
    have hshift : Continuous (fun η : Euclidean (n-1) ↦ ζ + τ • η) := by fun_prop
    have hphase : Continuous (fun η ↦ rawPrimaryPhaseDifference S ζ τ x η) :=
      ((hS.comp hshift).sub continuous_const).div_const τ
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp hphase))).smul (hB.comp hshift)
  have hr := OriginalMeanQuadraticProfilesTemplate.raw_integral_refined_annuli
    S (fun x ξ ↦ B (x,Z,ξ)) ζ τ hd.measurable hbound hdB v x
    (fun _ ↦ hc.continuousOn)
  rw [hr,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η ↦
    forwardSlice_band_eq_scaled_raw ψ B Z ζ τ b
      (fun η x ↦ rawPrimaryPhaseDifference S ζ τ x η) det j η x (v j η)

/-- Continuity of the fixed original physical phase section. -/
theorem continuous_original_phase_sections {n : ℕ} {P : Type*} [TopologicalSpace P]
    (S : P → Euclidean n → Euclidean (n-1) → ℝ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n-1) ↦ S q.1.1 q.1.2 q.2))
    (p : P) (x : Euclidean n) : Continuous (S p x) :=
  hS.comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)

/-- Continuity of the original cut matrix at a fixed native node. -/
theorem continuous_original_matrix_sections {n N : ℕ}
    (B : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (hB : Continuous B) (Z : Euclidean 3) (x : Euclidean n) :
    Continuous (fun ξ ↦ B (x,Z,ξ)) :=
  hB.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))

open ActualCarriers FrozenMenu
/-- The retained carrier equals the native graph on its original quarter-ball. -/
theorem retained_carrier_eq_of_original_graph {e : ℕ} {P : Patch (e+1)}
    {U : Set (Euclidean (e+1))} {hU : IsOpen U}
    (T : CurrentFullPhase.PatchQuantitativeFamily P U hU)
    (z₀ Z Zraw : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) (heq : Zraw = Z)
    (hgraph : (Zraw,T.reference.spatialPatch Zraw) ∈
      Metric.closedBall (z₀,T.reference.spatialPatch z₀) (ρ/4)) :
    Sampling.MeasuredAmplitude.extendedRetainedCarrier T z₀ hρ Z = T.reference.spatialPatch Z := by
  subst Zraw
  apply Sampling.MeasuredAmplitude.extendedRetainedCarrier_eq
  rw [← closedBall_prod_same] at hgraph
  exact Metric.closedBall_subset_closedBall (by linarith) hgraph.1

/-- The pre-existing whole-annular G theorem implies its exact full raw integral
without removing κ or dividing any original angular factor. -/
theorem scaled_raw_of_forward_realization {n N J : ℕ}
    (S : Euclidean n → Euclidean (n-1) → ℝ) (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (Z : Euclidean 3) (ζ : Euclidean (n-1)) (τ b : ℝ)
    (det : Euclidean (n-1) → ℝ) (d : Euclidean (n-1) → ℂ)
    (hd : Continuous d) (bound : ℝ) (hbound : 0 ≤ bound)
    (hdB : ∀ η, ‖d η‖ ≤ bound) (hdet : ∀ η, d η = (det η : ℂ))
    (hS : ∀ x, Continuous (S x)) (hB : ∀ x, Continuous (fun ξ ↦ B (x,Z,ξ)))
    (G : WideInput n J →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (ζnative : Euclidean (n-1)) (hcarrier : b ≠ 0 → ζ = ζnative)
    (hG : @ForwardAnnularRealization n N J G
      (fun u x ↦ rawPrimaryPhaseDifference S ζ τ x u.2)
      (fun u ↦ b * singleBareScalarMask det u)
      (fun a c _ η x ↦ forwardSlice ψ B Z ζnative τ a c η x))
    (v : RefinedInput n J) (z : Torus n) :
    (G ((wideRefinement n J).symm v)).val z () =
      (b * ψ (AmplitudeBound.centeredTorusRepresentative z)) •
        rawPrimaryDemodulatedIntegral S (fun x ξ ↦ B (x,Z,ξ)) ζ τ volume
          (weightedWideDensity d ((wideRefinement n J).symm v))
          (AmplitudeBound.centeredTorusRepresentative z) := by
  by_cases hb : b = 0
  · have hz := hG v z
    simp only [hb,physicalForwardKernel,sampledMomentKernel,zero_mul,Complex.ofReal_zero] at hz
    change _ = ∑ j : RefinedIndex J, (∫ _η,
      (0 : Matrix (Fin N) (Fin n) ℂ) ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ) at hz
    simpa only [hb,zero_mul,zero_smul,integral_zero,Finset.sum_const_zero] using hz
  · rw [← hcarrier hb] at hG
    exact (hG v z).trans (forwardSlice_annuli_eq_scaled_raw S ψ B Z ζ τ b det d hd bound hbound hdB hdet
      v (AmplitudeBound.centeredTorusRepresentative z) (hS _) (hB _))

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.forwardSlice_band_eq_scaled_raw
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.forwardSlice_annuli_eq_scaled_raw
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.scaled_raw_of_forward_realization

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open Sampling Sampling.RawKernel Sampling.MeanNormalBound SamplingKernelBounds
open RawInputPartition RawPrimary RawPrimary.SliceBounds AmplitudeBound CanonicalRowComparison
variable {n N : ℕ}
local instance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedSpace
local instance : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) :=
  ContinuousLinearMap.toNormedSpace
local instance : ContinuousENorm (Matrix (Fin N) (Fin n) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin N) (Fin n) ℂ) inferInstance).toContinuousENorm
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] {bands : ℕ}
variable
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (V : P → Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (background : P → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦ S q.1.1 q.1.2 q.2))
    (hV : ∀ p x, Continuous (V p x))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (background q.1.1 q.1.2) (V q.1.1 q.1.2 q.2)))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K → complexCrossMeasurement (C x) (background p x) (V p x η) = 0)
    (M bound : ℝ) (hM : 0 ≤ M) (hbound : 0 ≤ bound)
    (hAM : ∀ p x η, ‖complexCrossMeasurement (C x) (background p x) (V p x η)‖ ≤ M)
    (hdB : ∀ η, ‖d η‖ ≤ bound)
include hV
/-- Preserve the full original angular factor throughout the actual G identity.
Its inactive branch needs no baseline equality, and no factor is divided out.
Consumer: actual `hraw` of `fixedSourceLinear_low_error`
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem zero_safe_hraw_of_scaled_original_integral
    (L : ℕ) (p : P) (a : ℝ)
    (base : CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (G : RefinedInput n bands →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hbackground : a ≠ 0 → ∀ z, Cper z ≠ 0 →
      base.val z () = background p (centeredTorusRepresentative z))
    (hmeasurement : ∀ z, Cper z = C (centeredTorusRepresentative z))
    (hG : ∀ v z, Cper z ≠ 0 →
      (G v).val z () = a • rawPrimaryDemodulatedIntegral (S p) (V p) (ζ p) (τ p) volume
        (weightedWideDensity d (widePrefix n bands L ((wideRefinement n bands).symm v)))
        (centeredTorusRepresentative z))
    (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    CurrentMean.smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v) =
      a • (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
        PeriodicLocalL2.transferOutputOperator (realQuadratureChannel (refinedKernelPrefix D L p)) v) := by
  let D := bandKernelData (J := bands) S
    (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
    ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
  let c : ℝ := ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹
  have hb := real_bandKernelData_prefix_eq_measured_rawIntegral S V C background ζ τ d
    hS hV hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB L p v
  have hs : (a • (c • realQuadratureChannel (refinedKernelPrefix D L p) v) :
      Lp (Euclidean n) 2 (volume : Measure (Euclidean n))) =ᵐ[volume]
      fun x ↦ a • C x ((2 : ℝ) • CurrentMean.mixedHermitianTensor (background p x)
        (rawPrimaryDemodulatedIntegral (S p) (V p) (ζ p) (τ p) volume
          (weightedWideDensity d (widePrefix n bands L ((wideRefinement n bands).symm v))) x)) := by
    filter_upwards [hb,Lp.coeFn_smul a (c • realQuadratureChannel (refinedKernelPrefix D L p) v)] with x hx hax
    rw [hax,Pi.smul_apply,hx]
  change _ = a • c • PeriodicLocalL2.toTorus (𝕜 := ℝ)
    (realQuadratureChannel (refinedKernelPrefix D L p) v)
  rw [← map_smul,← map_smul]
  apply Lp.ext
  filter_upwards [CurrentMean.SmoothPeriodicFamily.componentL2_coe_ae ()
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ G) () v),
    PeriodicLocalL2.toTorus_coe (𝕜 := ℝ)
      (a • (c • realQuadratureChannel (refinedKernelPrefix D L p) v)),
    PeriodicLocalL2.measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp hs.restrict]
      with z hl hr hp
  rw [CurrentMean.smoothResidualToL2,hl,CanonicalChange.smoothRawCrossResponse_apply,hr,hp]
  simp only [Function.comp_apply]
  rw [← hmeasurement z]
  by_cases hz : Cper z = 0
  · simp only [hz,zero_apply,smul_zero]
  · rw [hG v z hz]
    by_cases ha : a = 0
    · simp only [ha,zero_smul,← CurrentMean.hermitianContinuousBilinear_apply,map_zero,smul_zero]
    · rw [hbackground ha z hz]
      simp only [← CurrentMean.hermitianContinuousBilinear_apply,map_smul]
      exact smul_comm _ _ _
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.zero_safe_hraw_of_scaled_original_integral

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition RawPrimary RawPrimary.SliceBounds Sampling SamplingKernelBounds CurrentMean
/-- Restrict the SAME whole G input to its original prefix after the scaled
raw integral has been proved. Observation is removed only on the original
nonzero measurement (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem prefix_scaled_raw_on_measurement {n N J : ℕ}
    (S : Euclidean n → Euclidean (n-1) → ℝ)
    (V : Euclidean n → Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ)
    (ζ : Euclidean (n-1)) (τ a : ℝ) (d : Euclidean (n-1) → ℂ)
    (ψ : Euclidean n → ℝ)
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (G : WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hG : ∀ w z, (G ((wideRefinement n J).symm w)).val z () =
      (a * ψ (AmplitudeBound.centeredTorusRepresentative z)) •
        rawPrimaryDemodulatedIntegral S V ζ τ volume
          (weightedWideDensity d ((wideRefinement n J).symm w))
          (AmplitudeBound.centeredTorusRepresentative z))
    (hψ : ∀ z, Cper z ≠ 0 → ψ (AmplitudeBound.centeredTorusRepresentative z) = 1)
    (L : ℕ) (v : RefinedInput n J) (z : Torus n) (hz : Cper z ≠ 0) :
    (canonicalWidePrefixRawMap G L v).val z () =
      a • rawPrimaryDemodulatedIntegral S V ζ τ volume
        (weightedWideDensity d (widePrefix n J L ((wideRefinement n J).symm v)))
        (AmplitudeBound.centeredTorusRepresentative z) := by
  change (G (widePrefix n J L ((wideRefinement n J).symm v))).val z () = _
  have h := hG (wideRefinement n J (widePrefix n J L ((wideRefinement n J).symm v))) z
  simpa only [LinearIsometryEquiv.symm_apply_apply,hψ z hz,mul_one] using h

/-- The exact restored scalar kernel gives the same restored real component,
not merely the same normal operator. -/
theorem real_prefix_factor {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D D0 : BandKernelData (Fin J × P) n) (L : ℕ) (p : P) (a c : ℝ)
    (h : refinedKernelPrefix D L p = a • refinedKernelPrefix D0 L p)
    (v : RefinedInput n J) :
    c • PeriodicLocalL2.transferOutputOperator (realQuadratureChannel (refinedKernelPrefix D L p)) v =
      a • (c • PeriodicLocalL2.transferOutputOperator
        (realQuadratureChannel (refinedKernelPrefix D0 L p)) v) := by
  rw [h]
  simp only [PeriodicLocalL2.transferOutputOperator,ContinuousLinearMap.comp_apply,
    realQuadratureChannel_apply,smul_apply,map_smul,smul_smul]
  congr 1
  ring
/-- The original observation equals one wherever the unchanged periodic
common measurement is nonzero. -/
theorem observation_on_common_periodic {n : ℕ}
    (ψ : Euclidean n → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hC : ∀ z, Cper z = C (AmplitudeBound.centeredTorusRepresentative z))
    (hψ : ∀ x, C x ≠ 0 → ψ x = 1) :
    ∀ z, Cper z ≠ 0 → ψ (AmplitudeBound.centeredTorusRepresentative z) = 1 := by
  intro z hz
  apply hψ
  rwa [← hC z]

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.prefix_scaled_raw_on_measurement
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.real_prefix_factor

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open SeparatedSampling RawInputPartition Sampling SamplingKernelBounds CanonicalRowComparison
open OriginalCanonicalSampled CurrentMean PeriodicLocalL2
variable {n : ℕ}
local instance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedSpace
local instance : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) :=
  ContinuousLinearMap.toNormedSpace
/-- Collect the actual pointwise raw action on the SAME original sample.
Membership of that sample supplies the original outer-support proof; no
new selection, nonzero weight, or normal-only identity is used. Consumer:
`fixedSourceLinear_low_error`, `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem sampled_hraw_of_original_components {ι : Type*} {N J p : ℕ}
    (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (base : ∀ i : ι, (Fin 3 → Fin (p+1)) → ∀ z : Point,
      z ∈ tsupport (ψ i) → SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (G : ι → (Fin 3 → Fin (p+1)) → Point → WideInput n J →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (D : ι → BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n)
    (L : ℕ) (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (hraw : ∀ i c z hz (v : RefinedInput n J),
      smoothResidualToL2 n
        (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n J)
          (base i c z hz) Cper hCper (fun _ ↦ canonicalWidePrefixRawMap (G i c z) L) () v) =
        ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
          transferOutputOperator (realQuadratureChannel (refinedKernelPrefix (D i) L (c,z))) v)
    (i : SampleIndex p B ψ w h U) (v : RefinedInput n J) :
    smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : SampleIndex p B ψ w h U ↦ RefinedInput n J)
        (sampledPositiveBaseline B ψ w h U base) Cper hCper
        (sampledPrefixDerivative B ψ w h U G L) i v) =
      rawIntegralSampledComponent B ψ w h U
        (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)) i v := by
  have hi := hraw i.1 (color p i.2.val.1) (node h (U i.1) i.2)
    (sample_in_outer_support B ψ w h U i) v
  simpa only [sampledPositiveBaseline,sampledPrefixDerivative,sampledDerivative,
    CanonicalChange.smoothRawCrossResponse,rawIntegralSampledComponent,
    periodicSampledComponent,sampledComponent,smul_apply,
    transferOutputOperator,ContinuousLinearMap.comp_apply] using hi
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.sampled_hraw_of_original_components

public meta section
open Lean Meta Elab Command
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
open OriginalBackgroundHermitianTemplate
private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def actual := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def part (h : Expr) (j : Nat) : Expr :=
  Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "raw forward: expected original constant"
  let info ← getConstInfo name
  let some value := info.value? (allowOpaque := true) | throwError "raw forward: missing checked body {name}"
  return ((value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private def named (e : Expr) : MetaM (Array (Name × Expr)) := do
  let .const name levels := e.getAppFn | throwError "raw forward: missing native constant"
  let info ← getConstInfo name
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  let mut out := #[]
  for arg in e.getAppArgs do
    let .forallE label _ rest _ := type.consumeMData
      | throwError "raw forward: argument ABI exhausted at {name}"
    out := out.push (label,arg)
    type := rest.instantiate1 arg
  return out
private def get (xs : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let some pair := xs.find? (fun q => q.1 == key)
    | throwError "raw forward: original argument {key} missing"
  return pair.2
private def store (suffix : Name) (params : Array Expr) (proof : Expr)
    (target : Option Expr := none) : MetaM Unit := do
  let inferred ← inferType proof
  let expected := target.getD inferred
  let type ← instantiateMVars (← mkForallFVars params expected)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let env ← getEnv
  for e in #[proof,inferred,expected,type,value] do
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "actual raw forward missing {missing.toList}"
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw forward contains open geometry or proof data"
  let name := ns ++ suffix
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Closed original-data step in the zero-safe raw column and SAME original sample identity (app:ch_mean_pairs:defn:mean-canonical); no changed scalar kernel, baseline, carrier, shift, or sample."
  logInfo m!"checked actual native{params.size} raw forward field {suffix}; full original data retained"

elab "publish_actual_scaled_raw_forward " mode:num : command => liftTermElabM do
  withActualRow fun d => do
    forallBoundedTelescope (← inferType d.native64[61]!) (some 1) fun colors _ => do
      withLocalDeclNoLocalInstanceUpdate `node .default
          (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
        let color := colors[0]!
        let params := d.parameters ++ #[color,node]
        let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
        unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData 45 do
          throwError "actual raw forward: original corrected45 spine changed"
        let r := raw.getAppArgs
        let colored ← openApp raw
        unless colored.isAppOf `JanetCartan.CanonicalAtomRealization.coloredCanonicalCrossBandData do
          throwError "actual raw forward: missing original colored cross constructor"
        let fields ← named colored
        let n := d.raw13[0]!
        let N := d.raw13[1]!
        let J ← get fields `J
        let p ← mkAppM ``Prod.mk #[color,node]
        let P ← inferType p
        let top ← synthInstance (← mkAppM ``TopologicalSpace #[P])
        let Sall ← get fields `S
        let S := mkApp Sall p
        let hS := mkAppN (mkConst ``continuous_original_phase_sections [.zero])
          #[n,P,top,Sall,← get fields `hS,p]
        let slice ← bodyAt (actual ++ `forwardAmplitude) params
        unless slice.isAppOfArity (actual ++ `forwardSlice) 7 do
          throwError "actual raw forward: original observed slice7 changed"
        let s := slice.getAppArgs
        let ψ := s[2]!
        let B := s[3]!
        let Z := s[4]!
        let ζnative := s[5]!
        let ζ := mkApp (← get fields `carrier) p
        let τ := s[6]!
        let hBc ← mkAppM ``ContDiff.continuous
          #[app `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles.cutAmplitude_contDiff
            (d.parameters.push color)]
        let hB := mkAppN (mkConst ``continuous_original_matrix_sections) #[n,N,B,hBc,Z]
        let rowType ← inferType d.row
        unless rowType.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
          throwError "actual raw forward: native selected index22 changed"
        let hfactor := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel_factor
          (rowType.getAppArgs ++ #[d.row,J,app (ns ++ `D) d.parameters])
        let factorAt ← forallBoundedTelescope (← inferType hfactor) (some 1) fun j _ =>
          mkLambdaFVars j (mkAppN hfactor #[j[0]!,color,node])
        let b ← forallBoundedTelescope (← inferType factorAt) (some 3) fun args eq => do
          unless eq.isAppOfArity ``Eq 3 do throwError "actual raw forward: factor equality changed"
          let rhs := eq.getAppArgs[2]!
          unless rhs.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw forward: scalar factor changed"
          let scalar := rhs.getAppArgs[4]!
          unless scalar.isAppOfArity ``Complex.ofReal 1 do throwError "actual raw forward: nonreal factor"
          let b := scalar.getAppArgs[0]!
          if (b.find? (args.contains ·)).isSome then throwError "actual raw factor depends on frequency"
          return b
        let nativeG ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalActual.G params
        unless nativeG.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
          throwError "actual raw forward: native G65 changed"
        let gn := nativeG.getAppArgs
        let family := gn[:61].toArray
        let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
        let nativeRow := app (wave ++ `original_sample_row) family
        let cutoff := app `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row
          (gn[:22].toArray.push nativeRow)
        let hsupp := app (wave ++ `Whole.inner_factor_support) (family.push node)
        let .forallE _ nz mem _ ← inferType hsupp
          | throwError "actual raw forward: native active support missing"
        let par := mem.getAppArgs[4]!
        let bne ← mkAppM ``Ne #[b,← mkNumeral (mkConst ``Real) 0]
        unless ← isDefEq bne nz do throwError "actual raw forward: active factor mismatch"
        let hcarrier ← withLocalDeclNoLocalInstanceUpdate `hActive .default bne fun ha => do
          let hgraph := mkAppN (part cutoff 3) #[par,mkApp hsupp ha]
          let gm ← inferType hgraph
          let Zraw := gm.getAppArgs[4]!.getAppArgs[2]!
          let heq := app ``JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate.outer_sampling_node #[node]
          let h := mkAppN (mkConst ``retained_carrier_eq_of_original_graph)
            #[r[0]!,r[2]!,r[3]!,r[4]!,r[5]!,r[34]!,Z,Zraw,r[35]!,r[36]!,heq,hgraph]
          mkLambdaFVars #[ha] h
        let some conic := r[39]!.find? (·.isAppOfArity `JanetCartan.Sampling.originalConicDetector 5)
          | throwError "actual raw forward: original conic mask missing"
        let det := app `JanetCartan.PhysicalForwardMean.originalForwardDetector conic.getAppArgs
        let hm0 := app `JanetCartan.PhysicalForwardMean.ofReal_originalForwardDetector conic.getAppArgs
        let hm ← forallBoundedTelescope (← inferType hm0) (some 1) fun η _ => do
          mkLambdaFVars η (← mkAppM ``Eq.symm #[mkAppN hm0 η])
        if mode.getNat == 0 then
          store `raw_carrier_eq_on_active params hcarrier
          return
        if mode.getNat == 1 then
          store `raw_phase_sections_continuous params hS
          return
        if mode.getNat == 2 then
          store `raw_matrix_sections_continuous params hB
          return
        let hG := if mode.getNat == 3 then
          app (actual ++ `unprefixed_forward_realization) params
          else app (ns ++ `forward_annular_raw_dictionary) params
        let args := #[n,N,J,S,ψ,B,Z,ζ,τ,b,det,← get fields `mask,← get fields `hd,
          ← get fields `Md,← get fields `hMd,← get fields `hdb,hm,
          app (ns ++ `raw_phase_sections_continuous) params,
          app (ns ++ `raw_matrix_sections_continuous) params,
          app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G params,ζnative,
          app (ns ++ `raw_carrier_eq_on_active) params,hG]
        let name := ``scaled_raw_of_forward_realization
        let mut expected := (← getConstInfo name).type
        let mut dictionaryType := mkSort .zero
        for k in [:args.size] do
          let .forallE _ domain rest _ := expected.consumeMData
            | throwError "actual raw forward: theorem ABI exhausted at {k}"
          IO.println s!"actual raw forward checking factor {k}"
          unless ← isDefEq (← inferType args[k]!) domain do
            throwError "actual raw forward factor type mismatch at {k}"
          if k == 22 then dictionaryType := domain
          expected := rest.instantiate1 args[k]!
        if mode.getNat == 3 then
          store `forward_annular_raw_dictionary params hG (some dictionaryType)
        else if mode.getNat == 4 then
          store `G_scaled_raw_integral params (mkAppN (mkConst name) args)
        else throwError "actual raw forward: unknown producer stage"
publish_actual_scaled_raw_forward 0
publish_actual_scaled_raw_forward 1
publish_actual_scaled_raw_forward 2
publish_actual_scaled_raw_forward 3
publish_actual_scaled_raw_forward 4
end JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.raw_carrier_eq_on_active
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.raw_phase_sections_continuous
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.raw_matrix_sections_continuous
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.forward_annular_raw_dictionary
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.G_scaled_raw_integral

public meta section
open Lean Meta Elab Command
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
open OriginalBackgroundHermitianTemplate
private def applyNativeKnown (name : Name) (fields : Array (Name × Expr))
    (stop : Name := `v) : MetaM Expr := do
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  let mut term := mkConst name levels
  for _ in [:64] do
    let .forallE key domain rest bi := type.consumeMData
      | throwError "actual raw component: missing final native input"
    let key := key.eraseMacroScopes
    if key == stop then return term
    let value ← match fields.find? (fun q => q.1 == key) with
      | some (_,value) => pure value
      | none => do
        if bi == .instImplicit then
          synthInstance domain
        else
          throwError "actual raw component: original field {key} missing"
    IO.println s!"actual raw component checking {key}"
    unless ← isDefEq (← inferType value) domain do
      throwError "actual raw component: original field {key} type mismatch"
    type := rest.instantiate1 value
    term := mkApp term value
  throwError "actual raw component: unexpected oversized consumer ABI"

elab "publish_actual_raw_component " mode:num : command => liftTermElabM do
  withActualRow fun d => do
    let baseline := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.positiveBaseline d.parameters
    forallBoundedTelescope (← inferType baseline) (some 3) fun extra _ => do
      let params := d.parameters ++ extra
      unless params.size == 54 do throwError "actual raw component: positive baseline54 changed"
      let color := extra[0]!
      let node := extra[1]!
      let native := d.parameters ++ #[color,node]
      withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
        let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
        unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData 45 do
          throwError "actual raw component: corrected45 data changed"
        let colored ← openApp raw
        let cf ← named colored
        let rawBand ← openApp colored
        unless rawBand.isAppOf `JanetCartan.Sampling.RawKernel.bandKernelData do
          throwError "actual raw component: original band-data constructor missing"
        let bf ← named rawBand
        let n := d.raw13[0]!
        let N := d.raw13[1]!
        let J ← get cf `J
        let p ← mkAppM ``Prod.mk #[color,node]
        let P ← inferType p
        let S ← get bf `S
        let A ← get cf `A
        let hA ← get cf `hA
        let colorFn ← get cf `color
        let nodeFn ← get cf `node
        let ζ ← get bf `ζ
        let τ ← get bf `τ
        let V ← forallBoundedTelescope (← inferType S) (some 3) fun pxη _ => do
          let i := pxη[0]!
          let point ← mkAppM ``Prod.mk #[pxη[1]!,← mkAppM ``Prod.mk #[mkApp nodeFn i,pxη[2]!]]
          mkLambdaFVars pxη (mkAppN A #[mkApp colorFn i,point])
        let background ← forallBoundedTelescope (← inferType S) (some 2) fun px _ => do
          let i := px[0]!
          let point ← mkAppM ``Prod.mk #[px[1]!,← mkAppM ``Prod.mk #[mkApp nodeFn i,mkApp ζ i]]
          mkLambdaFVars px (mkAppN A #[mkApp colorFn i,point])
        let hV ← forallBoundedTelescope (← inferType S) (some 2) fun px _ => do
          let i := px[0]!
          let h := mkAppN (mkConst ``continuous_original_matrix_sections)
            #[n,N,mkApp A (mkApp colorFn i),mkApp hA (mkApp colorFn i),mkApp nodeFn i,px[1]!]
          mkLambdaFVars px h
        if mode.getNat == 0 then
          store `raw_cross_sections_continuous native hV
          return
        let hV := app (ns ++ `raw_cross_sections_continuous) native
        let D0 := app (ns ++ `D) d.parameters
        let rowType ← inferType d.row
        unless rowType.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
          throwError "actual raw component: selected index22 changed"
        let fixed := rowType.getAppArgs
        let kernelArgs := fixed ++ #[d.row,J,D0]
        let D := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel kernelArgs
        let hk := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel_prefix_factor
          (kernelArgs ++ #[L,color,node])
        let ht ← inferType hk
        unless ht.isAppOfArity ``Eq 3 do throwError "actual raw component: prefix factor equality changed"
        let rhs := ht.getAppArgs[2]!
        unless rhs.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw component: original real factor missing"
        let a := rhs.getAppArgs[4]!
        let meas := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
        let xs := d.parameters[:50].toArray
        let C ← get cf `C
        let Cper := app (meas ++ `Cper) xs
        let hCper := app (meas ++ `Cper_smooth) xs
        let hmeasurement := app (meas ++ `Cper_native) xs
        let slice ← bodyAt (actual ++ `forwardAmplitude) native
        let ψ := slice.getAppArgs[2]!
        let hψ := mkAppN (mkConst ``observation_on_common_periodic)
          #[n,ψ,C,Cper,hmeasurement,app (meas ++ `observation_eq_one) xs]
        let G := app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G native
        let m := mkApp (mkConst ``Fin) N
        let fm ← synthInstance (← mkAppM ``Fintype #[m])
        let Gprefix := mkAppN (mkConst `JanetCartan.CurrentMean.canonicalWidePrefixRawMap [.zero])
          #[n,J,m,fm,G,L]
        let hG := mkAppN (mkConst ``prefix_scaled_raw_on_measurement)
          #[n,N,J,mkApp S p,mkApp V p,mkApp ζ p,mkApp τ p,a,← get bf `d,ψ,Cper,G,
            app (ns ++ `G_scaled_raw_integral) native,hψ,L]
        if mode.getNat == 1 then
          store `Gprefix_scaled_raw_on_measurement (native.push L) hG
          return
        let hG := app (ns ++ `Gprefix_scaled_raw_on_measurement) (native.push L)
        let hbackground := app `JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline.positiveBaseline_eq_cutAmplitude params
        let mut fields := #[(`n,n),(`N,N),(`P,P),(`bands,J),(`S,S),(`V,V),(`C,C),
          (`background,background),(`hV,hV),(`bound,← get bf `B),(`hbound,← get bf `hB),
          (`L,L),(`p,p),(`a,a),(`base,mkAppN baseline extra),(`Cper,Cper),(`hCper,hCper),
          (`G,Gprefix),(`hbackground,hbackground),(`hmeasurement,hmeasurement),(`hG,hG)]
        for key in #[`ζ,`τ,`d,`hS,`hA,`hζ,`hτ,`hτ₀,`hd,`K,`hK,`hAK,`M,`hM,`hAM,`hdB] do
          fields := fields.push (key,← get bf key)
        if mode.getNat == 2 then
          let prefixProof ← applyNativeKnown ``zero_safe_hraw_of_scaled_original_integral fields `hbackground
          let .forallE _ domain _ _ ← inferType prefixProof
            | throwError "actual raw component: active background consumer changed"
          store `raw_background_dictionary (params.push L) hbackground (some domain)
          return
        fields := fields.map fun pair => if pair.1 == `hbackground then
          (pair.1,app (ns ++ `raw_background_dictionary) (params.push L)) else pair
        if mode.getNat == 3 then
          let hsafe ← applyNativeKnown ``zero_safe_hraw_of_scaled_original_integral fields
          store `hraw_scaled_component (params.push L) hsafe
          return
        unless mode.getNat == 4 do throwError "actual raw component: unknown cache stage"
        let hsafe := app (ns ++ `hraw_scaled_component) (params.push L)
        let top ← synthInstance (← mkAppM ``TopologicalSpace #[P])
        let first ← synthInstance (mkAppN (mkConst ``FirstCountableTopology [.zero]) #[P,top])
        let compact ← synthInstance (mkAppN (mkConst ``LocallyCompactSpace [.zero]) #[P,top])
        let proof ← forallBoundedTelescope (← inferType hsafe) (some 1) fun vs _ => do
          let hr := mkAppN hsafe vs
          let rt ← whnf (← inferType hr)
          let right := rt.getAppArgs[2]!
          unless right.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw component: outer raw factor missing"
          let inner := right.getAppArgs[5]!
          unless inner.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw component: fixed Fourier scalar missing"
          let c := inner.getAppArgs[4]!
          let hf := mkAppN (mkConst ``real_prefix_factor [.zero])
            #[n,J,P,top,first,compact,D,D0,L,p,a,c,hk,vs[0]!]
          mkLambdaFVars vs (← mkAppM ``Eq.trans #[hr,← mkAppM ``Eq.symm #[hf]])
        store `hraw_original_component (params.push L) proof
publish_actual_raw_component 0
publish_actual_raw_component 1
publish_actual_raw_component 2
publish_actual_raw_component 3
publish_actual_raw_component 4
end JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.raw_cross_sections_continuous
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.Gprefix_scaled_raw_on_measurement
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.raw_background_dictionary
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.hraw_scaled_component
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.hraw_original_component

public meta section
open Lean Meta Elab Command
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
open OriginalBackgroundHermitianTemplate
private def outerArity : Expr → Nat
  | .forallE _ _ rest _ => outerArity rest + 1
  | .mdata _ rest => outerArity rest
  | _ => 0
private def exposeOriginalRawAliases (type : Expr) : MetaM Expr := do
  let mut type := type
  for (name,arity) in #[(`JanetCartan.PhysicalMean.OriginalBackgroundHermitian.ψ,50),
      (`JanetCartan.PhysicalSampling.OriginalOuterWeights.Index,22),(ns ++ `Dout,50)] do
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true)
      | throwError "selected actual raw: original alias body missing {name}"
    type := type.replace fun e =>
      if e.isAppOfArity name arity then
        some (((body.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta)
      else none
  return type
private def applyUntilOriginalIndex (name : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  let mut term := mkConst name levels
  for _ in [:64] do
    let .forallE key domain rest bi := type.consumeMData
      | throwError "selected actual raw: missing original outer index"
    let key := key.eraseMacroScopes
    if key == `i then return term
    let value ← match fields.find? (fun q => q.1 == key) with
      | some (_,value) => pure value
      | none => do
        if bi == .instImplicit then
          synthInstance domain
        else
          throwError "selected actual raw: exact original field {key} missing"
    unless ← isDefEq (← exposeOriginalRawAliases (← inferType value)) (← exposeOriginalRawAliases domain) do
      throwError "selected actual raw: exact original field {key} type mismatch\nactual: {← inferType value}\nexpected: {domain}"
    type := rest.instantiate1 value
    term := mkApp term value
  throwError "selected actual raw: changed consumer ABI"

elab "publish_selected_actual_raw_identity" : command => liftTermElabM do
  OriginalPeriodicBackgroundTemplate.withActualCanonicalSample fun xs ξ sampleIndex J _fI _hU _hξ => do
    unless sampleIndex.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "selected actual raw: unchanged sample index7 missing"
    let sa := sampleIndex.getAppArgs
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      let I := sa[0]!
      unless I.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
        throwError "selected actual raw: selected static index22 changed"
      let fixed := I.getAppArgs
      let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
      let B := app (outer ++ `B) fixed
      let ψ := app (outer ++ `ψ) fixed
      let n := mkApp (mkConst ``Nat.succ) xs[0]!
      let N := app `JanetCartan.embeddingDimension #[n]
      let base := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.positiveBaseline xs
      let G := app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G xs
      let meas := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
      let hraw ← forallBoundedTelescope (← inferType base) (some 4) fun extra _ => do
        mkLambdaFVars extra (app (ns ++ `hraw_original_component) (xs ++ extra |>.push L))
      let known := #[(`n,n),(`ι,I),(`N,N),(`J,J),(`p,sa[1]!),(`B,B),(`ψ,ψ),
        (`w,sa[4]!),(`h,sa[5]!),(`U,sa[6]!),(`base,base),(`G,G),
        (`D,app (ns ++ `Dout) xs),(`L,L),(`Cper,app (meas ++ `Cper) xs),
        (`hCper,app (meas ++ `Cper_smooth) xs),(`hraw,hraw)]
      let proof ← applyUntilOriginalIndex ``sampled_hraw_of_original_components known
      let params := xs.push L
      let sampled := `JanetCartan.PhysicalMean.OriginalCanonicalSampled
      let sampleParams := xs.push ξ
      let namedBase := app (sampled ++ `base) sampleParams
      let namedG := app (sampled ++ `Gprefix) (sampleParams.push L)
      let namedA := app (ns ++ `A) (sampleParams.push L)
      let mut target ← inferType proof
      let replacements := #[
        (`JanetCartan.PhysicalMean.OriginalCanonicalSampled.sampledPositiveBaseline,namedBase,0),
        (`JanetCartan.PhysicalMean.OriginalCanonicalSampled.sampledPrefixDerivative,namedG,1),
        (`JanetCartan.CanonicalRowComparison.rawIntegralSampledComponent,namedA,1)]
      for (name,term,drop) in replacements do
        let arity := outerArity (← getConstInfo name).type - drop
        let some old := target.find? (·.isAppOfArity name arity)
          | throwError "selected actual raw: original field {name} absent from target"
        let namedBody ← openApp term
        unless ← isDefEq (← exposeOriginalRawAliases old) (← exposeOriginalRawAliases namedBody) do
          throwError "selected actual raw: named original field {name} changed"
        target := target.replace fun e => if e == old then some term else none
      for name in #[sampled ++ `base,sampled ++ `Gprefix,ns ++ `A,
          `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift] do
        unless (target.find? (·.isAppOf name)).isSome do
          throwError "selected actual raw lost exact original data {name}"
      store `hraw_original_sample params proof (some target)
publish_selected_actual_raw_identity
end JanetCartan.PhysicalMean.OriginalCanonicalRow.RawForwardGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.hraw_original_sample
