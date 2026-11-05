module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.Conic
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.ExpansionProfiles
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Operators

/-!
# Uniform primitive bounds for every expansion operator

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
variable {n N : ℕ}

set_option maxHeartbeats 1600000 in
/-- Uniform primitive bounds for every expansion operator. The constant precedes the varying phase, conic maps,
amplitude and trade fields. Consumed by the next uniform assembly layer
for `app:ch_background:prop:bg-adjoint`; no operator bound is assumed. -/
theorem exists_uniform_expansion_primitive_L2_operator
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
    (ds : List (InitialCarrierDerivative n))
    (W D : ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i)
    (hDpos : ∀ i, 0 ≤ D i)
    (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ C ≥ 0, ∀
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (_hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
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
    (t : AdjointDerivativeTerm n)
    (_ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a)),
    ∀ (H T : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U → {η | ‖η‖ = 1} ⊆ U →
      (∀ R, ρ ≤ R → ∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ i ≤ (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ ds.length - t.dataDerivatives.length + (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ D i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / T)) →
      (∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ d ∈ ds, ∀ j i,
        i ≤ ds.length - t.dataDerivatives.length + (2*(n+1)) →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ D i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / T)) →
      ∃ U : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        ‖U‖ ≤ C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) ∧
        (∀ f, U f =ᵐ[carrierMeasure n] fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ t.amplitude u.1 x u.2) f) ∧
      ∀ f : Lp (α := Euclidean n) ℂ 2,
        MemLp (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n) ∧
        (eLpNorm (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n)).toReal ≤
          C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) * ‖f‖ := by
  obtain ⟨K, hK, hop⟩ := exists_geometryUniform_supportedExpansion_L2_operator
    ρ B c hρ hc J X Z Ω hX hZ hΩ hn
  obtain ⟨A, hA, hsymbol⟩ := exists_uniform_expansion_reserve_symbol_bound
    ds (2*(n+1)) W D hW hDpos
  refine ⟨K*A, mul_nonneg hK hA, ?_⟩
  intro Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage t ht
  have hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j) := by
    intro d j
    cases d with
    | initial h =>
      exact Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL h))
    | carrier h =>
      exact Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hV h))
  have hop' := hop Φ hΦ g σ hg
    (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) hr hsupp L V hL hV
    he hei hdom hf hD hΨ hinj hU hphase
  intro H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff
  obtain ⟨hcompact, hs, hbuf⟩ := adjointDerivativeExpansion_conic_properties L V ds
    (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) hX hZ hΩ hρ hsupp
    g J hJ hclosed himage t ht
  have hres : PrimitiveAmplitudeReserve g (2*(n+1)) ρ
      (A * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T))
      X (Prod.snd '' Z) Z Ω J t.amplitude := by
    refine ⟨mul_nonneg hA (Real.rpow_nonneg (le_trans zero_le_one hH) _),
      hcompact, hZ, hΩ, hΩunit, hs, hbuf, ?_⟩
    intro R hR p hp q hq
    rw [norm_iteratedFDeriv_scaledOriginalAmplitude]
    exact hsymbol L V a ha hfield χ t ht H T R hH hT U hU (hlocal R hR)
      ((p.1,p.2.1),p.2.2) (hunit hp) (hrad R hR _ hp) (hradBound R hR _ hp)
      (hamp R hR _ hp) (hcoeff _ hp) q hq
  obtain ⟨U₀, hUn, hUa, hb⟩ := hop' ds t ht _ hres
  refine ⟨U₀, by simpa only [mul_assoc] using hUn, hUa, ?_⟩
  intro f
  exact ⟨(hb f).1, by simpa only [mul_assoc] using (hb f).2⟩


end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
