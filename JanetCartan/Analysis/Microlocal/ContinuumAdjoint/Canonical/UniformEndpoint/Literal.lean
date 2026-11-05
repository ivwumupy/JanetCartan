module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.AllOrders
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Literal

/-!
# Uniform finite vector assembly of the literal adjoint

Uniform quantifier-order deductions for `app:ch_background:prop:bg-adjoint`
and the exact trades in `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
open ContinuumRow DerivativeKernels DerivativeKernels.ModifiedNormalSymbol
open TransportKernel Pseudodifferential AmplitudeBound FourierIntegral
open CarrierSobolev
open PeriodicLocalL2
variable {n N : ℕ}

set_option maxHeartbeats 1600000 in
/-- Uniform finite vector assembly of the literal adjoint. The constant precedes the varying phase, conic maps,
amplitude and trade fields. Consumed by the next uniform assembly layer
for `app:ch_background:prop:bg-adjoint`; no operator bound is assumed. -/
theorem exists_uniform_literalCarrierAdjoint_chart_raw_bound
    (χ : Euclidean n → ℝ)
    {K : Set (Euclidean n)}
    (hcell : K ⊆ halfOpenCell n)
    (hχ : ∀ x ∉ K, χ x = 0)
    (ρ B c : ℝ)
    (J : Set (JointVariables n))
    (X : Set (Euclidean n))
    (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hX : IsCompact X)
    (hZ : IsCompact Z)
    (hΩ : IsCompact Ω)
    (hn : 0 < n)
    (hΩunit : Ω ⊆ {η | ‖η‖ = 1})
    (W : ℕ → ℝ)
    (D : Fin n → List (InitialCarrierDerivative n) → ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i)
    (hDpos : ∀ j ds i, 0 ≤ D j ds i)
    (s : ℕ)
    (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ C ≥ 0, ∀
    (d : CarrierData n N)
    (_hchart : d.outputChart = torusChart K)
    (_hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (_hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (_hΦ : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ (carrierChartPhase d) p.1 p.2.1 p.2.2))
    (g : Chart n)
    (σ : JetRescaling g)
    (_hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (_ha : ∀ j η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ carrierChartNormalizedComponent d χ j p.1 p.2 η))
    (_hr : ∀ j, PrimitiveRegularity g
      (frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d χ j)) (fun _ ↦ 1))
    (_hsupp : ∀ j z x η, frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
      (carrierChartNormalizedComponent d χ j) z x η ≠ 0 →
      z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖)
    (L : CarrierParameter → Euclidean n → Euclidean (n-1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (_hL : ∀ h, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ L p.1 p.2 h))
    (_hV : ∀ h, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ V p.1 p.2 h))
    (_he : MeasurePreserving g.coordinates volume (volume.prod volume))
    (_hei : Continuous g.coordinates.symm)
    (_hdom : ∀ x y v w,
      ((chartCarrierVariable g.coordinates v w).1, x,
        (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((chartCarrierVariable g.coordinates v w).1, y,
        (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω ρ →
      w ∈ g.domain x y v)
    (_hf : ContinuousOn g.push g.inputDomain)
    (_hD : ∀ x y v, MeasurableSet (g.domain x y v))
    (_hΨ : ∀ x y v w, w ∈ g.domain x y v →
      HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v w) (g.domain x y v) w)
    (_hinj : ∀ x y v, InjOn (g.forward x y v) (g.domain x y v))
    (_hU : ∀ x y v w, w ∈ g.domain x y v → g.inverse x y v (g.forward x y v w) = w)
    (_hphase : ∀ x y v w, w ∈ g.domain x y v →
      (carrierChartPhase d) (chartCarrierVariable g.coordinates v w).1 x
          (chartCarrierVariable g.coordinates v w).2 -
        (carrierChartPhase d) (chartCarrierVariable g.coordinates v w).1 y
          (chartCarrierVariable g.coordinates v w).2 = inner ℝ (x-y) (g.forward x y v w))
    (_hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (_hclosed : IsClosed (g.push '' J))
    (_himage : g.push '' J ⊆ g.outputDomain)
    (_hphaseL : ∀ z x η h, x ∈ X → inner ℝ h η =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (L z x h))
    (_hphaseV : ∀ z x η h, x ∈ X → fderiv ℝ (fun w ↦ (carrierChartPhase d) w x η) z h =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (V z x h)),
    ∀ H : ℝ, 1 ≤ H →
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
      ∃ U₀ : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2 →L[ℂ] CarrierL2 n,
        (∀ f, U₀ f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
          (fun x ↦ f (centeredTorusRepresentative x))) ∧
        ∀ f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2,
          MemVectorFourierSobolev s f → MemRawSobolev s (U₀ f) ∧
          rawSobolevNorm s (U₀ f) ≤
            C * (vectorFourierSobolevNorm s f + H * ‖f‖) := by
  classical
  have hex (j : Fin n) := exists_uniform_chartAdjoint_all_orders_raw_bound
    ρ B c J X Z Ω hX hZ hΩ hn hΩunit W (D j) hW (hDpos j) s hρ hc
  choose C hC hb using hex
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro d hchart hpoint hcut hΦ g σ hg ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage hphaseL hphaseV H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff
  have hop (j : Fin n) := hb j (carrierChartPhase d) hΦ g σ hg
    (carrierChartNormalizedComponent d χ j) d.highCutoff (ha j) (hr j) (hsupp j)
    L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage hphaseL hphaseV H hH U hUopen hunit (hlocal j) hrad hradBound
    (hamp j) (hcoeff j)
  choose U₀ hUa hraw using hop
  refine ⟨carrierComponentOperator U₀, ?_, ?_⟩
  · intro f
    have hfull (j : Fin n) : SmoothSupportedAdjointAmplitude X (carrierChartComponent d χ j) := by
      refine ⟨?_, ?_⟩
      · intro η
        rw [carrierChartComponent_eq_frequencyScale]
        exact contDiff_const.mul (ha j η)
      · intro z x η hx
        rw [carrierChartComponent_eq_frequencyScale]
        by_contra hne
        exact hx (hsupp j z x η hne).2.1
    rw [carrierComponentOperator_apply]
    apply (Lp.coeFn_finsetSum _ _).trans
    have hrep := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦
      hUa j (finiteL2CoordinateIsometry volume f j))
    apply hrep.trans
    filter_upwards [] with u
    symm
    simpa only [carrierChartComponent_eq_frequencyScale, Finset.sum_apply] using
      carrierAdjointIntegral_eq_sum_chartAdjoint_L2 d hcell hX hchart hpoint χ hχ hcut
        (fun x ↦ f (centeredTorusRepresentative x)) f (fun _ _ ↦ rfl) hfull
        (fun z η ↦ hΦ.comp (f := fun x : Euclidean n ↦ (z, x, η))
          (show ContDiff ℝ ∞ (fun x : Euclidean n ↦ (z, x, η)) from
          contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))) u
  · exact carrierComponentOperator_raw_bound U₀ s C H hC (le_trans zero_le_one hH) hraw

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
