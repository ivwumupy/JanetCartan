module

public import JanetCartan.Iteration.PhysicalMean.MomentKernel
public import JanetCartan.Iteration.PhysicalMean.MomentPhysicalProfiles
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.FiniteRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Actual modified sampled rows on the original source measure

For `app:ch_mean_pairs:eq:raw-adjoint-moments`, the source space is the SAME
native disjoint union of original sample/band/frequency shells. The operators
below are constructed from their literal kernels. The original scalar test
bounds them after changing only the physical amplitude; no component norm,
number of samples, number of bands or input-frequency derivative is used.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels CompactCarrierKernel NormalComparison
open AmplitudeBound AmplitudeBound.PaperEstimates

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- The exact scalar entry kernel with the original phase, half-derivative
mask and square-root sample weights (`app:ch_mean_pairs:eq:raw-adjoint-moments`).
The forward amplitude is conjugated so the IBP adjoint amplitude is `a`. -/
def sampledMomentKernel (φ : X → Euclidean n → ℝ) (m : X → ℝ)
    (a : X → Euclidean n → ℂ) (x : Euclidean n) (u : X) : ℂ :=
  (m u : ℂ) * oscillatoryFactor 1 (φ u x) * star (a u x)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- Only joint continuity, not parameter derivative bounds, constructs the
literal modified sampled kernel (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem continuous_sampledMomentKernel
    (φ : X → Euclidean n → ℝ) (m : X → ℝ) (a : X → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m)
    (ha : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (sampledMomentKernel φ m a)) := by
  exact ((Complex.continuous_ofReal.comp (hm.comp continuous_snd)).mul
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (hφ.comp continuous_swap)))).cexp).mul
        (ha.comp continuous_swap).star

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- The original compact frequency mask and measurement support construct
joint compact support, uniformly over the sampled entries. -/
theorem hasCompactSupport_sampledMomentKernel
    (φ : X → Euclidean n → ℝ) (m : X → ℝ) (a : X → Euclidean n → ℂ)
    (hms : HasCompactSupport m) {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ u, tsupport (a u) ⊆ K) :
    HasCompactSupport (Function.uncurry (sampledMomentKernel φ m a)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hK.prod hms)
  intro p hp
  constructor
  · by_contra hx
    exact hp (by simp [Function.uncurry, sampledMomentKernel,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (has p.2 h))])
  · by_contra hu
    exact hp (by simp [Function.uncurry, sampledMomentKernel, image_eq_zero_of_notMem_tsupport hu])

variable (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : X → Euclidean n → ℝ) (m : X → ℝ) (a : X → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m)
    (ha : Continuous (Function.uncurry a)) (hms : HasCompactSupport m)
    {K : Set (Euclidean n)} (hK : IsCompact K) (has : ∀ u, tsupport (a u) ⊆ K)

/-- Construct the modified row on the SAME native input and physical output,
using the original full phase and masks. Its sharp norm is proved separately,
not imposed when constructing the continuous map. -/
def sampledMomentOperator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  compactKernelOperator (continuous_sampledMomentKernel φ m a hφ hm ha)
    (hasCompactSupport_sampledMomentKernel φ m a hms hK has)

/-- The constructed modified row has the literal original forward integral
on its entire source Hilbert space. -/
theorem sampledMomentOperator_ae_kernel (f : Lp ℂ 2 μ) :
    sampledMomentOperator μ φ m a hφ hm ha hms hK has f =ᵐ[volume]
      fun x ↦ ∫ u, sampledMomentKernel φ m a x u * f u ∂μ :=
  compactKernelOperator_ae_integral _ _ f

/-- Its actual Hilbert adjoint is the literal compact integral used by the
fixed IBP templates; the same raw input weights remain untouched. -/
theorem sampledMomentOperator_adjoint_ae (v : Euclidean n → ℂ) (hv : MemLp v 2 volume) :
    (sampledMomentOperator μ φ m a hφ hm ha hms hK has).adjoint (hv.toLp v) =ᵐ[μ]
      fun u ↦ (m u : ℂ) * chartAdjoint (φ u) (a u) v :=
  sampledScalarRow_adjoint_ae_chart μ _ _
    (continuous_sampledMomentKernel φ m a hφ hm ha)
    (hasCompactSupport_sampledMomentKernel φ m a hms hK has)
    (sampledMomentOperator_ae_kernel μ φ m a hφ hm ha hms hK has) m φ a (fun _ _ ↦ rfl) v hv

private theorem coordinateDerivList_star (js : List (Fin n)) (f : Euclidean n → ℂ) :
    euclideanCoordinateDerivList js (fun y ↦ star (f y)) =
      fun y ↦ star (euclideanCoordinateDerivList js f y) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [euclideanCoordinateDerivList, ih, fderiv_star,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

/-- The scalar auxiliary row bounds the actual modified row, with only
physical derivatives through `ell`. All source masks and weights belong to
the SAME original `T`; no sample-by-sample norm sum occurs
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_sampledMomentOperator_le_scalarTest
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχa : ∀ u x, a u x ≠ 0 → χ x = 1)
    (R A : ℝ) (hA : 0 ≤ A)
    (hasmooth : ∀ u, ContDiff ℝ ∞ (a u))
    (habox : ∀ u, SupportedInCenteredBox R (a u))
    (hjet : ∀ u (is : List (Fin n)), is.length ≤ n / 2 + 1 → ∀ x,
      ‖euclideanCoordinateDerivList is (a u) x‖ ≤ A)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ) :
    ‖sampledMomentOperator μ φ m a hφ hm ha hms hK has‖ ≤
      finiteRowAmplitudeConstant n R * ‖T‖ * A := by
  apply norm_integralRowAmplitudeOperator_le_of_finiteRegularity R (fun u x ↦ star (a u x))
    ha.star.stronglyMeasurable (fun u ↦ ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp
      (hasmooth u)).of_le (by simp))
    (fun u x hx ↦ habox u x (fun hz ↦ hx (by change star (a u x) = 0; rw [hz, star_zero]))) A hA
    (fun u is his x ↦ by simpa only [coordinateDerivList_star, norm_star] using hjet u is his x)
    T (sampledMomentOperator μ φ m a hφ hm ha hms hK has)
    (sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)))
  · intro f
    exact Filter.Eventually.of_forall (fun x ↦ integrable_compactKernel_mul_L2
      (continuous_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hφ hm
        (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)))
      (hasCompactSupport_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hms hχs
        (fun _ ↦ by
          apply closure_mono
          intro x hx
          exact fun hz ↦ hx (by change (χ x : ℂ) = 0; rw [hz, Complex.ofReal_zero]))) f x)
  · exact hT
  · intro f
    filter_upwards [sampledMomentOperator_ae_kernel μ φ m a hφ hm ha hms hK has f] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hz : a u x = 0
    · simp [sampledMomentKernel, hz]
    · simp only [sampledMomentKernel, hχa u x hz, Complex.ofReal_one, star_one, mul_one]
      ring

private theorem coordinateDerivList_zero (js : List (Fin n)) :
    euclideanCoordinateDerivList js (fun _ : Euclidean n ↦ (0 : ℂ)) = 0 := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [euclideanCoordinateDerivList, ih, fderiv_zero, Pi.zero_apply, zero_apply]
      rfl

/-- The scalar tester needs physical jets only on the ORIGINAL active input
mask. The measurable indicator used in the proof does not change the kernel,
input measure, phase or cutoff. In particular no derivative or norm of that
indicator occurs (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_sampledMomentOperator_le_scalarTest_onMask
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχa : ∀ u x, a u x ≠ 0 → χ x = 1)
    (R A : ℝ) (hA : 0 ≤ A)
    (hasmooth : ∀ u, ContDiff ℝ ∞ (a u))
    (habox : ∀ u, SupportedInCenteredBox R (a u))
    (hjet : ∀ u, m u ≠ 0 → ∀ is : List (Fin n), is.length ≤ n / 2 + 1 → ∀ x,
      ‖euclideanCoordinateDerivList is (a u) x‖ ≤ A)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ) :
    ‖sampledMomentOperator μ φ m a hφ hm ha hms hK has‖ ≤
      finiteRowAmplitudeConstant n R * ‖T‖ * A := by
  classical
  let b := fun u x ↦ if m u = 0 then (0 : ℂ) else star (a u x)
  have hbm : StronglyMeasurable (Function.uncurry b) :=
    StronglyMeasurable.ite
      (measurableSet_eq_fun (hm.measurable.comp measurable_fst) measurable_const)
      stronglyMeasurable_const ha.star.stronglyMeasurable
  have hbs (u) : ContDiff ℝ (↑(n / 2 + 1)) (b u) := by
    by_cases hu : m u = 0
    · simp only [b, hu, ite_true]
      exact contDiff_const
    · simp only [b, ite_eq_right hu]
      exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hasmooth u)).of_le (by simp)
  have hbb (u) : SupportedInCenteredBox R (b u) := by
    intro x hx
    by_cases hu : m u = 0
    · exact False.elim (hx (by simp only [b, hu, ite_true]))
    · apply habox u x
      intro hz
      exact hx (by simp only [b, ite_eq_right hu, hz, star_zero])
  have hbj (u) (is : List (Fin n)) (his : is.length ≤ n / 2 + 1) (x) :
      ‖euclideanCoordinateDerivList is (b u) x‖ ≤ A := by
    by_cases hu : m u = 0
    · simpa only [b, hu, ite_true, coordinateDerivList_zero, Pi.zero_apply, norm_zero] using hA
    · simpa only [b, ite_eq_right hu, coordinateDerivList_star, norm_star] using hjet u hu is his x
  apply norm_integralRowAmplitudeOperator_le_of_finiteRegularity R b hbm hbs hbb A hA hbj
    T (sampledMomentOperator μ φ m a hφ hm ha hms hK has)
    (sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)))
  · intro f
    exact Filter.Eventually.of_forall (fun x ↦ integrable_compactKernel_mul_L2
      (continuous_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hφ hm
        (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)))
      (hasCompactSupport_sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) hms hχs
        (fun _ ↦ by
          apply closure_mono
          intro x hx
          exact fun hz ↦ hx (by change (χ x : ℂ) = 0; rw [hz, Complex.ofReal_zero]))) f x)
  · exact hT
  · intro f
    filter_upwards [sampledMomentOperator_ae_kernel μ φ m a hφ hm ha hms hK has f] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : m u = 0
    · simp only [sampledMomentKernel, b, hu, ite_true, Complex.ofReal_zero, zero_mul, mul_zero]
    · by_cases hz : a u x = 0
      · simp only [sampledMomentKernel, b, ite_eq_right hu, hz, star_zero, mul_zero, zero_mul]
      · simp only [sampledMomentKernel, b, ite_eq_right hu, hχa u x hz, Complex.ofReal_one, star_one, mul_one]
        ring

end JanetCartan.PhysicalMean
