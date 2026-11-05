module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.AllOrders
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Components

/-!
# Quantitative assembly of the literal carrier adjoint

For `app:ch_background:prop:bg-adjoint`, instantiate every scalar estimate
with the literal full carrier components and then contract their finite vector
sum. This proves the estimate on Euclidean Hˢ chart data and identifies the
output with the original Haar integral. The chart equality is proved, and
no component operator estimate is a hypothesis. Periodic source localization
is a further comparison, not an identification of the two input measures.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel Pseudodifferential CarrierSobolev
open PeriodicLocalL2 AmplitudeBound
variable {n N : ℕ}

set_option maxHeartbeats 1600000 in
/-- The literal vector carrier adjoint has the raw Hˢ estimate on all
Euclidean vector Hˢ chart data (`app:ch_background:prop:bg-adjoint`). Every
scalar low bound and derivative estimate is constructed from original jets.
The output is the literal torus adjoint of the displayed chart representative;
the right side uses the actual Euclidean vector Fourier Sobolev norm. -/
theorem exists_literalCarrierAdjoint_chart_raw_bound
    (d : CarrierData n N) (χ : Euclidean n → ℝ)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
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
      ∃ U₀ : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2 →L[ℂ] CarrierL2 n,
        (∀ f, U₀ f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
          (fun x ↦ f (centeredTorusRepresentative x))) ∧
        ∀ f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin n)) 2,
          MemVectorFourierSobolev s f → MemRawSobolev s (U₀ f) ∧
          rawSobolevNorm s (U₀ f) ≤
            C * (vectorFourierSobolevNorm s f + H * ‖f‖) := by
  classical
  have hex (j : Fin n) := exists_chartAdjoint_all_orders_raw_bound (carrierChartPhase d) hΦ
    g σ ρ B c J X Z Ω hg hX hZ hΩ (carrierChartNormalizedComponent d χ j)
    d.highCutoff (ha j) (hr j) (hsupp j) L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
    hΩunit hJ hclosed himage W (D j) hW (hDpos j) hphaseL hphaseV s
  choose C hC hb using hex
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff
  have hop (j : Fin n) := hb j H hH U hUopen hunit (hlocal j) hrad hradBound
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

end JanetCartan.ContinuumAdjoint.DerivativeKernels
