module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Reserve

/-!
# Apply the conic normal bound on common expansion supports

The regularized supports used in `app:ch_background:prop:bg-adjoint` are built
once from the original closed conic buffer. The low bound then applies to all
actual expansion terms. The reserve input of this intermediate lemma is
produced from original jets by `exists_expansion_primitiveAmplitudeReserve`;
it is not a hypothesis of the final primitive-profile deduction.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel
variable {n : ℕ}

/-- Apply the checked normal/PDO/regularization proof to the actual expansion,
discharging its smoothness and all regularized support obligations from the
original amplitude and one common conic buffer. Consumed together with
`exists_expansion_primitiveAmplitudeReserve` in the raw bound of
`app:ch_background:prop:bg-adjoint`. No operator bound is an input. -/
theorem exists_supportedExpansion_L2_operator
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (a : AdjointAmplitude n) (hr : PrimitiveRegularity g a (fun _ ↦ 1))
    (hsupp : ∀ z x η, a z x η ≠ 0 →
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
      Φ (chartCarrierVariable g.coordinates v w).1 x
          (chartCarrierVariable g.coordinates v w).2 -
        Φ (chartCarrierVariable g.coordinates v w).1 y
          (chartCarrierVariable g.coordinates v w).2 = inner ℝ (x-y) (g.forward x y v w))
    (hn : 0 < n) :
    ∃ K ≥ 0, ∀ ds (t : AdjointDerivativeTerm n),
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
  obtain ⟨K, hK, hb⟩ := exists_modifiedAdjoint_L2_bound Φ hΦ g σ ρ B c J
    (Prod.snd '' Z) hg X hX Z Ω hn
  refine ⟨K, hK, ?_⟩
  intro ds t ht A hA
  let P := adjointConicBuffer X Z Ω ρ
  have hP : IsClosed P := isClosed_adjointConicBuffer hX.isClosed hZ.isClosed
    hΩ.isClosed hg.threshold_pos
  have hc := regularizedExpansionSupport_continuity hr P hdom hf
  obtain ⟨U, hUn, hUa, hbound, _⟩ := hb t.amplitude A
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

/-- The function-level consequence of `exists_supportedExpansion_L2_operator`,
consumed by the term estimates for `app:ch_background:prop:bg-adjoint`. -/
theorem exists_supportedExpansion_L2_bound
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (a : AdjointAmplitude n) (hr : PrimitiveRegularity g a (fun _ ↦ 1))
    (hsupp : ∀ z x η, a z x η ≠ 0 →
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
      Φ (chartCarrierVariable g.coordinates v w).1 x
          (chartCarrierVariable g.coordinates v w).2 -
        Φ (chartCarrierVariable g.coordinates v w).1 y
          (chartCarrierVariable g.coordinates v w).2 = inner ℝ (x-y) (g.forward x y v w))
    (hn : 0 < n) :
    ∃ K ≥ 0, ∀ ds (t : AdjointDerivativeTerm n),
      t ∈ adjointDerivativeExpansion L V ds a → ∀ A,
      PrimitiveAmplitudeReserve g (2*(n+1)) ρ A X (Prod.snd '' Z) Z Ω J t.amplitude →
      ∀ f : Lp (α := Euclidean n) ℂ 2,
        MemLp (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n) ∧
        (eLpNorm (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n)).toReal ≤ K * A * ‖f‖ := by
  obtain ⟨K, hK, hb⟩ := exists_supportedExpansion_L2_operator Φ hΦ g σ ρ B c J X Z Ω
    hg hX hZ hΩ a hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
  refine ⟨K, hK, ?_⟩
  intro ds t ht A hA f
  obtain ⟨_, _, _, hbound⟩ := hb ds t ht A hA
  exact hbound f

end JanetCartan.ContinuumAdjoint.DerivativeKernels
