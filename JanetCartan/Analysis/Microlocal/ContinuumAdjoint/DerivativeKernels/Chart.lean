module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Literal
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure

/-!
# The literal adjoint in a measurement chart

For `app:ch_background:prop:bg-adjoint`, transfer the actual torus measurement
integral to Euclidean Lebesgue measure and split its vector contraction into
scalar chart adjoints. The carrier measure and physical frequency are unchanged.
Only chart compatibility and the original measurement support are inputs to
the transfer; no integral identity or operator bound is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

/-- The phase of the literal row, expressed in physical measurement coordinates
(`app:ch_background:eq:bg-T`). -/
def carrierChartPhase (d : CarrierData n N) (z : CarrierParameter)
    (x : Euclidean n) (η : Euclidean (n - 1)) : ℝ :=
  inner ℝ (d.transportedPosition x z) η

/-- The full real measured amplitude in the physical chart. The measurement
cutoff is a genuine Euclidean function; every other factor is the literal
factor from `carrierAmplitude` (`app:ch_background:eq:bg-T`). -/
def carrierChartAmplitude (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1)) : Euclidean n :=
  (χ x * d.angularCutoff z (‖η‖⁻¹ • η) * d.highCutoff ‖η‖ * Real.sqrt ‖η‖ *
    ‖d.normalField x z‖ ^ 2) • reducedCovector d x (d.covector x z)

/-- The actual scalar amplitudes consumed by `adjointDerivativeExpansion`;
the real kernel components acquire no additional conjugation
(`app:ch_background:prop:bg-adjoint`). -/
def carrierChartComponent (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (j : Fin n) : AdjointAmplitude n :=
  fun z x η ↦ (carrierChartAmplitude d χ z x η j : ℂ)

/-- Every component retains the measurement cutoff support, before any
initial-variable cutoff (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierChartComponent_eq_zero (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (j : Fin n) (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1))
    (hχ : χ x = 0) : carrierChartComponent d χ j z x η = 0 := by
  simp [carrierChartComponent, carrierChartAmplitude, hχ]

/-- Exact Haar-to-Lebesgue transfer of the literal carrier adjoint. The datum
may be any extension agreeing on the physical measurement chart, so a smooth
compact extension can be used for subsequent integrations by parts
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierAdjointIntegral_eq_chartIntegral
    (d : CarrierData n N) {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (χ : Euclidean n → ℝ) (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (w : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hw : ∀ x ∈ d.outputChart, w (centeredTorusRepresentative x) = v x)
    (u : CarrierVariable n) :
    carrierAdjointIntegral d v u = ∫ x,
      oscillatoryFactor (-1) (carrierChartPhase d u.1 x u.2) *
        inner ℂ (euclideanComplexInclusion (carrierChartAmplitude d χ u.1 x u.2)) (w x) := by
  rw [carrierAdjointIntegral_eq]
  calc
    _ = ∫ x : Torus n,
        oscillatoryFactor (-1) (carrierChartPhase d u.1 (centeredTorusRepresentative x) u.2) *
          inner ℂ (euclideanComplexInclusion
            (carrierChartAmplitude d χ u.1 (centeredTorusRepresentative x) u.2))
            (w (centeredTorusRepresentative x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ d.outputChart
      · simp only [measuredAdjointAmplitude, indicator_of_mem hx]
        rw [hw x hx]
        simp only [carrierPhase, carrierChartPhase, carrierAmplitude,
          carrierChartAmplitude, hpoint x hx, hcut x hx]
      · have hk : centeredTorusRepresentative x ∉ K := by
          simpa only [hchart, torusChart, mem_preimage] using hx
        simp [measuredAdjointAmplitude, hx, carrierChartAmplitude,
          hχ _ hk]
    _ = _ := integral_representative_of_supported hcell (fun x ↦
      oscillatoryFactor (-1) (carrierChartPhase d u.1 x u.2) *
        inner ℂ (euclideanComplexInclusion (carrierChartAmplitude d χ u.1 x u.2)) (w x)) (by
      intro x hx
      simp [carrierChartAmplitude, hχ x hx])

/-- The literal vector adjoint is the finite sum of the scalar chart adjoints
used by the derivative recursion. Smoothness and compact measurement support
prove integrability before the finite sum is moved out of the integral
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierAdjointIntegral_eq_sum_chartAdjoint
    (d : CarrierData n N) {K S : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hS : IsCompact S) (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (χ : Euclidean n → ℝ) (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (w : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hw : ∀ x ∈ d.outputChart, w (centeredTorusRepresentative x) = v x)
    (hws : ∀ j, Continuous (fun x ↦ w x j))
    (ha : ∀ j, SmoothSupportedAdjointAmplitude S (carrierChartComponent d χ j))
    (hΦ : ∀ z η, ContDiff ℝ ∞ (fun x ↦ carrierChartPhase d z x η))
    (u : CarrierVariable n) :
    carrierAdjointIntegral d v u = ∑ j : Fin n,
      chartAdjoint (fun x ↦ carrierChartPhase d u.1 x u.2)
        (fun x ↦ carrierChartComponent d χ j u.1 x u.2) (fun x ↦ w x j) := by
  rw [carrierAdjointIntegral_eq_chartIntegral d hcell hchart hpoint χ hχ hcut v w hw u]
  have hi (j : Fin n) : Integrable (fun x ↦
      oscillatoryFactor (-1) (carrierChartPhase d u.1 x u.2) *
        (carrierChartComponent d χ j u.1 x u.2 * w x j)) :=
    integrable_chartAdjoint (hΦ u.1 u.2)
      (((ha j).smooth u.2).comp (contDiff_const.prodMk contDiff_id)).continuous (hws j)
      (hS.of_isClosed_subset isClosed_closure ((ha j).tsupport_subset hS.isClosed u.1 u.2))
  simp only [PiLp.inner_apply, euclideanComplexInclusion_apply, RCLike.inner_apply,
    Complex.conj_ofReal, mul_comm (w _ _), Finset.mul_sum]
  exact integral_finsetSum _ (fun j _ ↦ hi j)

/-- Ordered initial/carrier derivatives commute with the finite measured
component sum on smooth data (`app:ch_background:prop:bg-adjoint`). -/
theorem applyInitialCarrierDerivativeList_component_sum
    (f : Fin n → CarrierVariable n → ℂ)
    (hf : ∀ j η, ContDiff ℝ ∞ (fun z ↦ f j (z, η)))
    (ds : List (InitialCarrierDerivative n)) (u : CarrierVariable n) :
    applyInitialCarrierDerivativeList ds (fun v ↦ ∑ j, f j v) u =
      ∑ j, applyInitialCarrierDerivativeList ds (f j) u := by
  induction ds generalizing u with
  | nil => rfl
  | cons d ds ih =>
    simp only [applyInitialCarrierDerivativeList]
    rw [show applyInitialCarrierDerivativeList ds (fun v ↦ ∑ j, f j v) =
      (fun v ↦ ∑ j, applyInitialCarrierDerivativeList ds (f j) v) from funext ih]
    cases d with
    | initial h => simp only [applyInitialCarrierDerivative, Finset.mul_sum]
    | carrier h =>
      simp only [applyInitialCarrierDerivative]
      rw [fderiv_fun_sum (fun j _ ↦
        (contDiff_applyInitialCarrierDerivativeList (hf j) ds u.2).differentiable
          (by simp) u.1)]
      simp only [sum_apply]

/-- The complete ordered derivative expansion starts at the literal torus
adjoint, with the actual full measured component amplitudes. The hypotheses
are chart compatibility, compact measurement support, smoothness, and the two
rectangular phase identities; derivative interchange is proved by `Iteration`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem carrierAdjointIntegral_derivative_expansion
    (d : CarrierData n N) {K S : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hS : IsCompact S) (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (χ : Euclidean n → ℝ) (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (w : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hw : ∀ x ∈ d.outputChart, w (centeredTorusRepresentative x) = v x)
    (hws : ∀ j, ContDiff ℝ ∞ (fun x ↦ w x j))
    (ha : ∀ j, SmoothSupportedAdjointAmplitude S (carrierChartComponent d χ j))
    (hΦ : ∀ η, ContDiff ℝ ∞
      (fun p : CarrierParameter × Euclidean n ↦ carrierChartPhase d p.1 p.2 η))
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (hphaseL : ∀ z x η h, x ∈ S → inner ℝ h η =
      fderiv ℝ (fun y ↦ carrierChartPhase d z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ S →
      fderiv ℝ (fun z ↦ carrierChartPhase d z x η) z h =
      fderiv ℝ (fun y ↦ carrierChartPhase d z y η) x (V z x h))
    (ds : List (InitialCarrierDerivative n)) (u : CarrierVariable n) :
    applyInitialCarrierDerivativeList ds (carrierAdjointIntegral d v) u =
      ∑ j : Fin n, ((adjointDerivativeExpansion L V ds (carrierChartComponent d χ j)).map
        (fun t ↦ t.realize (carrierChartPhase d) (fun x ↦ w x j) u)).sum := by
  have he : carrierAdjointIntegral d v = fun u ↦ ∑ j : Fin n,
      chartAdjoint (fun x ↦ carrierChartPhase d u.1 x u.2)
        (fun x ↦ carrierChartComponent d χ j u.1 x u.2) (fun x ↦ w x j) :=
    funext (carrierAdjointIntegral_eq_sum_chartAdjoint d hcell hS hchart hpoint χ hχ hcut
      v w hw (fun j ↦ (hws j).continuous) ha
      (fun z η ↦ (hΦ η).comp (contDiff_const.prodMk contDiff_id)))
  rw [he, applyInitialCarrierDerivativeList_component_sum _
    (fun j η ↦ contDiff_chartAdjoint_carrier hS (ha j) hΦ (hws j) η)]
  exact Finset.sum_congr rfl (fun j _ ↦
    applyInitialCarrierDerivativeList_chartAdjoint hS (ha j) hL hV hΦ
      hphaseL hphaseV (hws j) ds u)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
