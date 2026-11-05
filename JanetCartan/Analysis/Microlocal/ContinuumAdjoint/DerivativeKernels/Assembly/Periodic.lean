module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Literal
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PeriodicTransfer

/-!
# The literal periodic carrier adjoint in the shared raw Sobolev space

This is the final domain assembly for `app:ch_background:prop:bg-adjoint`.
The conic normal construction, derivative expansion, fixed-reserve estimates,
and density extension produce the Euclidean operator; the checked periodic
localization then supplies the original Haar-domain operator. No operator
estimate or Fourier derivative interchange is an input to this theorem.

The consumer `jc-continuum-initial-adjoint` must instantiate the primitive
phase, conic geometry, support and coefficient profiles and compose with its
original inverse. The reserve 2(n+1) is independent of the integer order.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel Pseudodifferential CarrierSobolev
open PeriodicLocalL2 AmplitudeBound
variable {n N : ℕ}

/-- The literal representative identifies the constructed periodic operator
with the consumer's original adjoint, independently of the Sobolev order
or the chosen bounds (`app:ch_background:prop:bg-adjoint`). -/
theorem literalCarrierAdjointOperator_unique (d : CarrierData n N)
    (T S : PeriodicL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n)
    (hT : ∀ v, T v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v)
    (hS : ∀ v, S v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) : T = S := by
  ext1 v
  exact Lp.ext ((hT v).trans (hS v).symm)

set_option maxHeartbeats 1600000 in
/-- The literal carrier adjoint on every periodic vector Hˢ datum, before
physical initial cutoffs (`app:ch_background:prop:bg-adjoint`). The constant
precedes both the shared high coefficient budget and the datum. Every raw
and modified-operator estimate is discharged from original primitive jets,
with one fixed symbol reserve 2(n+1), including at order zero. -/
theorem exists_literalCarrierAdjoint_periodic_raw_bound
    (d : CarrierData n N) (χ : Euclidean n → ℝ)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    {r₀ : ℝ} (hr₀ : r₀ < 1 / 2) (hK : K ⊆ DifferentialChart.chartBox r₀)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (hΦ : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ (carrierChartPhase d) p.1 p.2.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (ha : ∀ j η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ carrierChartNormalizedComponent d χ j p.1 p.2 η))
    (hr : ∀ j, PrimitiveRegularity g
      (frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d χ j)) (fun _ ↦ 1))
    (hsupp : ∀ j z x η, frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
      (carrierChartNormalizedComponent d χ j) z x η ≠ 0 →
      z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖)
    (L : CarrierParameter → Euclidean n → Euclidean (n-1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ V p.1 p.2 h))
    (he : MeasurePreserving g.coordinates volume (volume.prod volume))
    (hei : Continuous g.coordinates.symm)
    (hdom : ∀ x y v w,
      ((chartCarrierVariable g.coordinates v w).1, x,
        (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((chartCarrierVariable g.coordinates v w).1, y,
        (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω ρ →
      w ∈ g.domain x y v)
    (hf : ContinuousOn g.push g.inputDomain)
    (hD : ∀ x y v, MeasurableSet (g.domain x y v))
    (hΨ : ∀ x y v w, w ∈ g.domain x y v →
      HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v w) (g.domain x y v) w)
    (hinj : ∀ x y v, InjOn (g.forward x y v) (g.domain x y v))
    (hU : ∀ x y v w, w ∈ g.domain x y v → g.inverse x y v (g.forward x y v w) = w)
    (hphase : ∀ x y v w, w ∈ g.domain x y v →
      (carrierChartPhase d) (chartCarrierVariable g.coordinates v w).1 x
          (chartCarrierVariable g.coordinates v w).2 -
        (carrierChartPhase d) (chartCarrierVariable g.coordinates v w).1 y
          (chartCarrierVariable g.coordinates v w).2 = inner ℝ (x-y) (g.forward x y v w))
    (hn : 0 < n)
    (hΩunit : Ω ⊆ {η | ‖η‖ = 1})
    (hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (hclosed : IsClosed (g.push '' J)) (himage : g.push '' J ⊆ g.outputDomain)
    (W : ℕ → ℝ) (D : Fin n → List (InitialCarrierDerivative n) → ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ j ds i, 0 ≤ D j ds i)
    (hphaseL : ∀ z x η h, x ∈ X → inner ℝ h η =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ X → fderiv ℝ (fun w ↦ (carrierChartPhase d) w x η) z h =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (V z x h))
    (s : ℕ) :
    ∃ C ≥ 0, ∀ H : ℝ, 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U → {η | ‖η‖ = 1} ⊆ U →
      (∀ j R, ρ ≤ R → ∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ carrierChartNormalizedComponent d χ j p.1.1 p.1.2 (R • p.2)) (p,η)) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor d.highCutoff (R • p.2)) p) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ i ≤ (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor d.highCutoff (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ j (ds : List (InitialCarrierDerivative n)), ds.length ≤ s →
        ∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ ds.length + (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          carrierChartNormalizedComponent d χ j p.1.1 p.1.2 (R • p.2)) p‖ ≤ D j ds i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ l (ds : List (InitialCarrierDerivative n)), ds.length ≤ s →
        ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ d ∈ ds, ∀ j i,
        i ≤ ds.length + (2*(n+1)) →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ D l ds i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      ∃ T : PeriodicL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n,
        (∀ v, T v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) ∧
        ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (T (PeriodicSobolevSpace.toL2 s v)) ∧
          rawSobolevNorm s (T (PeriodicSobolevSpace.toL2 s v)) ≤
            C * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  obtain ⟨C, hC, hb⟩ := exists_literalCarrierAdjoint_chart_raw_bound d χ hcell hchart hpoint
    hχ hcut hΦ g σ ρ B c J X Z Ω hg hX hZ hΩ ha hr hsupp L V hL hV he hei hdom hf
    hD hΨ hinj hU hphase hn hΩunit hJ hclosed himage W D hW hDpos hphaseL hphaseV s
  obtain ⟨K_s, hKs, htransfer⟩ := exists_periodicCarrierOperator_raw_bound (n := n) hr₀ s
  refine ⟨K_s * C, mul_nonneg (le_trans zero_le_one hKs) hC, ?_⟩
  intro H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff
  obtain ⟨U₀, hrep, hbound⟩ := hb H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff
  exact ⟨periodicCarrierOperator U₀,
    htransfer d hK hchart U₀ hrep C H hC (le_trans zero_le_one hH) hbound⟩

end JanetCartan.ContinuumAdjoint.DerivativeKernels
