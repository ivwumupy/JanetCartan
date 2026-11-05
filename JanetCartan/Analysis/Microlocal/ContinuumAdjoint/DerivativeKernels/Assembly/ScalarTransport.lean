module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.TransportComponents

/-!
# Periodic raw adjoint bound from the original scalar transport

This final specialization of `app:ch_background:prop:bg-adjoint` uses the
literal normal field r(z,Y) times its flow factor and geometric normal. It
derives the jets of its squared norm, angular mask, and full component before
invoking the proved conic-normal, derivative and periodic-domain assemblies.
The one common high budget is linear in the final estimate, including s=0.

The actual Hamilton/leading-wave producers must supply the primitive formula,
smoothness, conic support, exact phase identities and finite-low/high jet
profiles. The consumer `jc-continuum-initial-adjoint` instantiates those inputs
and composes with its original inverse; no new inverse is chosen here.
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
/-- The literal Haar-domain adjoint satisfies the raw Hˢ bound from the
original scalar r, flow, angular mask and geometric coefficient profiles
(`app:ch_background:prop:bg-adjoint`). The square in the normal amplitude
is retained, but introduces no second high norm. The reserve 2(n+1), or
2(n+1)+1 for geometry-map baselines, is independent of s. Neither a composite
amplitude profile nor any operator bound is a premise. -/
theorem exists_scalarTransportCarrierAdjoint_periodic_raw_bound
    (d : CarrierData n N) (χ : Euclidean n → ℝ)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    {r₀ : ℝ} (hr₀ : r₀ < 1 / 2) (hK : K ⊆ DifferentialChart.chartBox r₀)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hχ : ∀ x ∉ K, χ x = 0)
    (hcut : ∀ x ∈ d.outputChart, d.measurementCutoff x = χ (centeredTorusRepresentative x))
    (ν : AdjointJetPoint n → Euclidean N)
    (r : CarrierParameter × Euclidean (n-1) → ℝ) (flow : AdjointJetPoint n → ℝ)
    (hν : ∀ z x, d.normalField x z =
      (r (z, d.transportedPosition x z) * flow (z,x)) • ν (z,x))
    (hc : ∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d χ ν j))
    (hmask : ContDiff ℝ ∞
      (fun p : CarrierParameter × Euclidean (n-1) ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hscalar : ContDiff ℝ ∞ (fun p ↦ (r p : ℂ)))
    (hflow : ContDiff ℝ ∞ (fun p ↦ (flow p : ℂ)))
    (hY : ContDiff ℝ ∞
      (fun p : AdjointJetPoint n ↦ (p.1, d.transportedPosition p.2 p.1)))
    (hΦ : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ (carrierChartPhase d) p.1 p.2.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
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
    (W P₀ N₀ A₀ B₀ F₀ : ℕ → ℝ) (C₀ : Fin n → ℕ → ℝ)
    (D : List (InitialCarrierDerivative n) → ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i) (hC₀ : ∀ j i, 0 ≤ C₀ j i)
    (hP₀ : ∀ i, 0 ≤ P₀ i) (hN₀ : ∀ i, 0 ≤ N₀ i)
    (hA₀ : ∀ i, 0 ≤ A₀ i) (hB₀ : ∀ i, 0 ≤ B₀ i)
    (hF₀ : ∀ i, 0 ≤ F₀ i) (hDpos : ∀ ds i, 0 ≤ D ds i)
    (hphaseL : ∀ z x η h, x ∈ X → inner ℝ h η =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ X → fderiv ℝ (fun w ↦ (carrierChartPhase d) w x η) z h =
      fderiv ℝ (fun y ↦ (carrierChartPhase d) z y η) x (V z x h))
    (s : ℕ) :
    ∃ C ≥ 0, ∀ H : ℝ, 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U → {η | ‖η‖ = 1} ⊆ U →
      (∀ R, ρ ≤ R → ∀ η ∈ U, ∀ p,
        ContDiffAt ℝ ∞ (adjointAngularGraph R) (p,η)) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor d.highCutoff (R • p.2)) p) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ i ≤ (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor d.highCutoff (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ j p, ∀ i ≤ s + 2*(n+1),
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d χ ν j) p‖ ≤
          C₀ j i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ s + 2*(n+1),
        ‖iteratedFDeriv ℝ i
          (fun v : CarrierParameter × Euclidean (n-1) ↦ (d.angularCutoff v.1 v.2 : ℂ))
          (adjointAngularGraph R p)‖ ≤
          P₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i, 1 ≤ i → i ≤ s + 2*(n+1) →
        ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤
          N₀ i * H ^ (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ p : AdjointJetPoint n, ∀ i ≤ s + 2*(n+1),
        ‖iteratedFDeriv ℝ i (fun p ↦ (r p : ℂ))
          (p.1, d.transportedPosition p.2 p.1)‖ ≤
          A₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ p : AdjointJetPoint n, ∀ i, 1 ≤ i → i ≤ s + 2*(n+1) →
        ‖iteratedFDeriv ℝ i
          (fun p : AdjointJetPoint n ↦ (p.1, d.transportedPosition p.2 p.1)) p‖ ≤
          B₀ i * H ^ (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ p : AdjointJetPoint n, ∀ i ≤ s + 2*(n+1),
        ‖iteratedFDeriv ℝ i (fun p ↦ (flow p : ℂ)) p‖ ≤
          F₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      (∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
        ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ e ∈ ds, ∀ j i,
        i ≤ ds.length + (2*(n+1)) →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V e j p.1) p‖ ≤
          D ds i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / (max s 1 : ℕ))) →
      ∃ T : PeriodicL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n,
        (∀ v, T v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) ∧
        ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (T (PeriodicSobolevSpace.toL2 s v)) ∧
          rawSobolevNorm s (T (PeriodicSobolevSpace.toL2 s v)) ≤
            C * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  let P (j : Fin n) := transportSymbolJetBudget (C₀ j) P₀ N₀
    (adjointLeibnizBudget A₀ A₀) B₀ (adjointLeibnizBudget F₀ F₀)
  have hP (j : Fin n) : ∀ i, 0 ≤ P j i := transportSymbolJetBudget_nonneg
    _ _ _ _ _ _ (hC₀ j) hP₀ hN₀ (adjointLeibnizBudget_nonneg hA₀ hA₀) hB₀
    (adjointLeibnizBudget_nonneg hF₀ hF₀)
  have heq := carrierChartNormalizedComponent_eq_scalarTransport d χ ν r flow hν
  have ha (j : Fin n) (η) : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦
      carrierChartNormalizedComponent d χ j p.1 p.2 η) := by
    rw [heq j]
    exact contDiff_normalizedTransportAmplitude _ _ _ _ _ (hc j)
      (fun θ ↦ hmask.comp (contDiff_fst.prodMk contDiff_const))
      (hscalar.pow 2) hY (hflow.pow 2) η
  obtain ⟨C, hC, hb⟩ := exists_literalCarrierAdjoint_periodic_raw_bound d χ hcell hr₀ hK
    hchart hpoint hχ hcut hΦ g σ ρ B c J X Z Ω hg hX hZ hΩ ha hr hsupp
    L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn hΩunit hJ hclosed himage W
    (fun j ds i ↦ P j i + D ds i) hW
    (fun j ds i ↦ add_nonneg (hP j i) (hDpos ds i)) hphaseL hphaseV s
  refine ⟨C, hC, ?_⟩
  intro H hH U hUopen hunit hN hrad hradBound hgeom hmaskP hNN hrA hYB hflowF hcoeff
  have hT : (0 : ℝ) < (max s 1 : ℕ) := by exact_mod_cast (show 0 < max s 1 by omega)
  have hY' : ContDiff ℝ ∞
      (adjointScalarGraph (fun p : AdjointJetPoint n ↦ d.transportedPosition p.2 p.1)) :=
    hY.comp contDiff_fst
  have hf' : ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦ (flow p.1 : ℂ) ^ 2) :=
    (hflow.pow 2).comp contDiff_fst
  refine hb H hH U hUopen hunit ?_ hrad hradBound ?_ ?_
  · intro j R hR η hη p
    rw [heq j]
    exact contDiffAt_normalizedTransportAmplitude_symbol
      (carrierChartGeometryComponent d χ ν j) (fun z θ ↦ (d.angularCutoff z θ : ℂ))
      (fun p ↦ (r p : ℂ) ^ 2) (fun p ↦ d.transportedPosition p.2 p.1)
      (fun p ↦ (flow p : ℂ) ^ 2) R (p,η)
      ((hc j).comp contDiff_fst).contDiffAt hmask.contDiffAt (hN R hR η hη p)
      (hscalar.pow 2).contDiffAt hY'.contDiffAt hf'.contDiffAt
  · intro j ds hds R hR p hp i hi
    have hi' : i ≤ s + 2*(n+1) := hi.trans (Nat.add_le_add_right hds _)
    rw [heq j]
    have hjet := normalizedTransportAmplitude_symbol_reserve_profile
      (carrierChartGeometryComponent d χ ν j) (fun z θ ↦ (d.angularCutoff z θ : ℂ))
      (fun p ↦ (r p : ℂ) ^ 2) (fun p ↦ d.transportedPosition p.2 p.1)
      (fun p ↦ (flow p : ℂ) ^ 2) R p
      (2*(n+1)) i ((hc j).comp contDiff_fst).contDiffAt hmask.contDiffAt
      (hN R hR p.2 (hunit hp) p.1) (hscalar.pow 2).contDiffAt hY'.contDiffAt hf'.contDiffAt
      (C₀ j) P₀ N₀ (adjointLeibnizBudget A₀ A₀) B₀ (adjointLeibnizBudget F₀ F₀)
      (hC₀ j) hP₀ hN₀ (adjointLeibnizBudget_nonneg hA₀ hA₀) hB₀
      (adjointLeibnizBudget_nonneg hF₀ hF₀) hH hT
      (fun k hk ↦ (adjoint_spatial_jet_lift_bound _ (hc j) k p).trans
        (hgeom j p.1 k (hk.trans hi')))
      (fun k hk ↦ hmaskP R hR p hp k (hk.trans hi'))
      (fun k hk hk' ↦ hNN R hR p hp k hk (hk'.trans hi'))
      (fun k hk ↦ adjoint_scalar_square_reserve_profile _ hscalar.contDiffAt
        (2*(n+1)) k A₀ hA₀ hH hT
        (fun l hl ↦ hrA p.1 l (hl.trans (hk.trans hi'))))
      (fun k hk hk' ↦ (adjoint_spatial_jet_lift_bound _ hY k p).trans
        (hYB p.1 k hk (hk'.trans hi')))
      (fun k hk ↦ (adjoint_spatial_jet_lift_bound _ (hflow.pow 2) k p).trans
        (adjoint_scalar_square_reserve_profile _ hflow.contDiffAt (2*(n+1)) k F₀ hF₀ hH hT
          (fun l hl ↦ hflowF p.1 l (hl.trans (hk.trans hi')))))
    exact hjet.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hDpos ds i))
      (Real.rpow_nonneg (le_trans zero_le_one hH) _))
  · intro j ds hds p hp e he j' i hi
    exact (hcoeff ds hds p hp e he j' i hi).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hP j i))
        (Real.rpow_nonneg (le_trans zero_le_one hH) _))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
