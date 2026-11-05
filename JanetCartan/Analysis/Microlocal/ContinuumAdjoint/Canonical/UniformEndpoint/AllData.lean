module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.Compact
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.AllData

/-!
# Uniform extension to all Euclidean Sobolev data

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
variable {n N : ℕ}

set_option maxHeartbeats 1600000 in
/-- Uniform extension to all Euclidean Sobolev data. The constant precedes the varying phase, conic maps,
amplitude and trade fields. Consumed by the next uniform assembly layer
for `app:ch_background:prop:bg-adjoint`; no operator bound is assumed. -/
theorem exists_uniform_chartAdjoint_raw_bound
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
    (D : List (InitialCarrierDerivative n) → ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i)
    (hDpos : ∀ ds i, 0 ≤ D ds i)
    (s : ℕ)
    (hs : 0 < s)
    (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ C ≥ 0, ∀
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (_hΦ : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ Φ p.1 p.2.1 p.2.2))
    (g : Chart n)
    (σ : JetRescaling g)
    (_hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (a : AdjointAmplitude n)
    (χ : ℝ → ℝ)
    (_ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (_hr : PrimitiveRegularity g
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) (fun _ ↦ 1))
    (_hsupp : ∀ z x η, frequencyScaleAmplitude (halfOrderRadialFactor χ) a z x η ≠ 0 →
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
      Φ (chartCarrierVariable g.coordinates v w).1 x
          (chartCarrierVariable g.coordinates v w).2 -
        Φ (chartCarrierVariable g.coordinates v w).1 y
          (chartCarrierVariable g.coordinates v w).2 = inner ℝ (x-y) (g.forward x y v w))
    (_hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (_hclosed : IsClosed (g.push '' J))
    (_himage : g.push '' J ⊆ g.outputDomain)
    (_hphaseL : ∀ z x η h, x ∈ X → inner ℝ h η =
      fderiv ℝ (fun y ↦ Φ z y η) x (L z x h))
    (_hphaseV : ∀ z x η h, x ∈ X → fderiv ℝ (fun w ↦ Φ w x η) z h =
      fderiv ℝ (fun y ↦ Φ z y η) x (V z x h)),
    ∀ H : ℝ, 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U → {η | ‖η‖ = 1} ⊆ U →
      (∀ R, ρ ≤ R → ∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ i ≤ (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
        ∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ ds.length + (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ D ds i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / s)) →
      (∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
        ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ d ∈ ds, ∀ j i,
        i ≤ ds.length + (2*(n+1)) →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ D ds i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / s)) →
      ∃ U₀ : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        (∀ f, U₀ f =ᵐ[carrierMeasure n] fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2)
            (fun x ↦ frequencyScaleAmplitude (halfOrderRadialFactor χ) a u.1 x u.2) f) ∧
        ∀ f : Lp (α := Euclidean n) ℂ 2, MemFourierSobolev s f →
          MemPhysicalSobolev s (partialUnitaryInverse n (U₀ f)) ∧
          physicalSobolevNorm s (partialUnitaryInverse n (U₀ f)) ≤
            C * (fourierSobolevNorm s f + H * ‖f‖) := by
  obtain ⟨C, hC, hcompact⟩ := exists_uniform_chartAdjoint_compact_raw_bound
    ρ B c J X Z Ω hX hZ hΩ hn hΩunit W D hW hDpos s hs hρ hc
  refine ⟨C, hC, ?_⟩
  intro Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage hphaseL hphaseV
  have hcompact' := hcompact Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf
    hD hΨ hinj hU hphase hJ hclosed himage hphaseL hphaseV
  intro H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff
  let t : AdjointDerivativeTerm n :=
    ⟨frequencyScaleAmplitude (halfOrderRadialFactor χ) a, []⟩
  have ht : t ∈ adjointDerivativeExpansion L V []
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) := by
    simp [adjointDerivativeExpansion, t]
  have hΦc : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2) :=
    hΦ.continuous.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
  obtain ⟨_, _, hop⟩ := exists_expansion_primitive_L2_operator Φ hΦc g σ ρ B c J X Z Ω
    hg hX hZ hΩ a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
    hΩunit hJ hclosed himage [] t ht W (D []) hW (hDpos [])
  obtain ⟨U₀, _, hUa, _⟩ := hop H s hH (by exact_mod_cast hs) U hUopen hunit
    hlocal hrad hradBound
    (by simpa [t] using hamp [] (Nat.zero_le s)) (by simp)
  refine ⟨U₀, hUa, ?_⟩
  apply memPhysicalSobolev_partialUnitaryInverse_of_compactSmooth_bound U₀ s C H
  intro v hv hvs
  let f : Lp (α := Euclidean n) ℂ 2 :=
    (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
  obtain ⟨hb, hm, hbound⟩ := hcompact' H hH U hUopen hunit hlocal hrad hradBound
    hamp hcoeff v hv hvs
  have hrep : U₀ f = hb.toLp _ := by
    apply Lp.ext
    apply (hUa f).trans
    apply Filter.EventuallyEq.trans _ hb.coeFn_toLp.symm
    filter_upwards [] with u
    unfold chartAdjoint
    apply integral_congr_ae
    filter_upwards [(hv.continuous.memLp_of_hasCompactSupport hvs).coeFn_toLp] with x hx
    simp only [f] at hx ⊢
    rw [hx]
  change MemPhysicalSobolev s (partialUnitaryInverse n (U₀ f)) ∧ _
  rw [hrep]
  exact ⟨hm, hbound⟩

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
