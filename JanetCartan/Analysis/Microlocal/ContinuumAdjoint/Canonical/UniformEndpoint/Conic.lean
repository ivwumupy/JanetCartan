module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.LowAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Conic

/-!
# Uniform low bound for all supported derivative terms

The normal/PDO constant is chosen before the phase, conic chart, rescaling,
original amplitude and trade fields. The literal regularized supports are the
same as in the existing derivative assembly. The remaining amplitude-reserve
hypothesis is supplied from primitive profiles by the finite expansion estimate;
it is not a premise of the intended scalar-transport endpoint.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
open ContinuumRow DerivativeKernels DerivativeKernels.ModifiedNormalSymbol
open TransportKernel AmplitudeBound FourierIntegral
variable {n : ℕ}

/-- All actual derivative terms share the same geometry-only low constant,
chosen before their original amplitude and trade fields as well as the phase
and conic maps. This strengthens the order of choices in
`DerivativeKernels.exists_supportedExpansion_L2_operator` and is consumed by
the uniform raw Sobolev assembly (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_geometryUniform_supportedExpansion_L2_operator
    (ρ B c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω) (hn : 0 < n) :
    ∃ K ≥ 0,
      ∀ (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
        (_hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
        (g : Chart n) (σ : JetRescaling g)
        (_hg : PrimitiveJetGeometry g σ (2*(n+1)) ρ B c J (Prod.snd '' Z))
    (a : AdjointAmplitude n) (_hr : PrimitiveRegularity g a (fun _ ↦ 1))
    (_hsupp : ∀ z x η, a z x η ≠ 0 →
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
    , ∀ ds (t : AdjointDerivativeTerm n),
      t ∈ adjointDerivativeExpansion L V ds a → ∀ A,
      PrimitiveAmplitudeReserve g (2*(n+1)) ρ A X (Prod.snd '' Z) Z Ω J t.amplitude →
      ∃ U : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        ‖U‖ ≤ K * A ∧
        (∀ f, U f =ᵐ[carrierMeasure n] fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ t.amplitude u.1 x u.2) f) ∧
      ∀ f : Lp (α := Euclidean n) ℂ 2,
        MemLp (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n) ∧
        (eLpNorm (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n)).toReal ≤ K * A * ‖f‖ := by
  obtain ⟨K, hK, hb⟩ := exists_geometryUniform_modifiedAdjoint_L2_bound
    ρ B c hρ hc J (Prod.snd '' Z) X hX Z Ω hn
  refine ⟨K, hK, ?_⟩
  intro Φ hΦ g σ hg a hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase
    ds t ht A hA
  let P := adjointConicBuffer X Z Ω ρ
  have hP : IsClosed P := isClosed_adjointConicBuffer hX.isClosed hZ.isClosed
    hΩ.isClosed hg.threshold_pos
  have hc := regularizedExpansionSupport_continuity hr P hdom hf
  obtain ⟨U, hUn, hUa, hbound, _⟩ := hb Φ hΦ g σ hg t.amplitude A
    (primitiveRegularity_adjointDerivativeExpansion hr hL hV ds t ht) hA he
    (regularizedExpansionChartSupport g P)
    (isCompact_regularizedExpansionChartSupport g hr.coordinates.continuous hei hP)
    (regularizedExpansionChartSupport_domain g P hdom)
    (fun k ↦ (hc k).1) (fun k ↦ (hc k).2.1) (fun k ↦ (hc k).2.2.1)
    hD hΨ hinj hU
    (modifiedNormalDensity_expansion_zero_off L V ds a hP hsupp t ht g)
    hphase (regularizedExpansionSourceSupport g P)
    (isCompact_regularizedExpansionSourceSupport g hr.coordinates.continuous hei hP
      hX (fun _ hp ↦ hp.2.1))
    (fun k x y v w hw ↦ regularizedExpansionChartSupport_source g P k x y (v,w) hw)
    (fun k ↦ (hc k).2.2.2)
  exact ⟨U, hUn, hUa, hbound⟩

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
