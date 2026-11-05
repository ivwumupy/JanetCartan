module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Operators
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Weights

/-!
# Order-zero raw adjoint bound

The empty expansion gives the raw estimate on all measurement L² data at
order zero in `app:ch_background:prop:bg-adjoint`. Only the fixed primitive
symbol reserve is used, without any high budget or derivatives of the datum.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel CarrierSobolev
variable {n : ℕ}

/-- The order-zero raw estimate on all Euclidean measurement L² data for
`app:ch_background:prop:bg-adjoint`. Compact conic regularization constructs
the original adjoint class; partial radian synthesis is an isometry. No
operator estimate is assumed, and the only quantitative amplitude input is
the original fixed low profile through order 2(n+1). -/
theorem exists_chartAdjoint_zero_raw_operator
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (a : AdjointAmplitude n) (χ : ℝ → ℝ)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hr : PrimitiveRegularity g
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) (fun _ ↦ 1))
    (hsupp : ∀ z x η, frequencyScaleAmplitude (halfOrderRadialFactor χ) a z x η ≠ 0 →
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
    (hn : 0 < n)
    (hΩunit : Ω ⊆ {η | ‖η‖ = 1})
    (hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (hclosed : IsClosed (g.push '' J)) (himage : g.push '' J ⊆ g.outputDomain)
    (W D : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ i, 0 ≤ D i) :
    ∃ C ≥ 0,
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
        ∀ i ≤ 2*(n+1),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ D i) →
      ∃ U₀ : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        ‖U₀‖ ≤ C ∧ ∀ f, U₀ f =ᵐ[carrierMeasure n] fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2)
            (fun x ↦ frequencyScaleAmplitude (halfOrderRadialFactor χ) a u.1 x u.2) f := by
  let t : AdjointDerivativeTerm n :=
    ⟨frequencyScaleAmplitude (halfOrderRadialFactor χ) a, []⟩
  have ht : t ∈ adjointDerivativeExpansion L V []
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) := by
    simp [adjointDerivativeExpansion, t]
  obtain ⟨C, hC, hop⟩ := exists_expansion_primitive_L2_operator Φ hΦ g σ ρ B c J X Z Ω
    hg hX hZ hΩ a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
    hΩunit hJ hclosed himage [] t ht W D hW hDpos
  refine ⟨C, hC, ?_⟩
  intro U hU hunit hlocal hrad hradBound hamp
  obtain ⟨U₀, hUn, hUa, _⟩ := hop 1 1 le_rfl zero_lt_one U hU hunit hlocal hrad hradBound
    (by simpa [t] using hamp) (by simp)
  exact ⟨U₀, by simpa [t] using hUn, hUa⟩

/-- The order-zero raw norm bound for the literal integral representative,
from `exists_chartAdjoint_zero_raw_operator`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_chartAdjoint_zero_raw_bound
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (g : Chart n) (σ : JetRescaling g) (ρ B c : ℝ)
    (J : Set (JointVariables n)) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1)))
    (hg : PrimitiveJetGeometry g σ (2 * (n+1)) ρ B c J (Prod.snd '' Z))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (a : AdjointAmplitude n) (χ : ℝ → ℝ)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hr : PrimitiveRegularity g
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) (fun _ ↦ 1))
    (hsupp : ∀ z x η, frequencyScaleAmplitude (halfOrderRadialFactor χ) a z x η ≠ 0 →
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
    (hn : 0 < n)
    (hΩunit : Ω ⊆ {η | ‖η‖ = 1})
    (hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (hclosed : IsClosed (g.push '' J)) (himage : g.push '' J ⊆ g.outputDomain)
    (W D : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ i, 0 ≤ D i) :
    ∃ C ≥ 0,
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
        ∀ i ≤ 2*(n+1),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ D i) →
      ∀ f : Lp (α := Euclidean n) ℂ 2,
      let b : CarrierVariable n → ℂ := fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
        (fun x ↦ frequencyScaleAmplitude (halfOrderRadialFactor χ) a u.1 x u.2) f
      ∃ hb : MemLp b 2 (carrierMeasure n),
        MemPhysicalSobolev 0 (partialUnitaryInverse n (hb.toLp b)) ∧
        physicalSobolevNorm 0 (partialUnitaryInverse n (hb.toLp b)) ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hop⟩ := exists_chartAdjoint_zero_raw_operator Φ hΦ g σ ρ B c J X Z Ω
    hg hX hZ hΩ a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
    hΩunit hJ hclosed himage W D hW hDpos
  refine ⟨C, hC, ?_⟩
  intro U hU hunit hlocal hrad hradBound hamp f
  obtain ⟨U₀, hUn, hUa⟩ := hop U hU hunit hlocal hrad hradBound hamp
  have hm := (Lp.memLp (U₀ f)).ae_eq (hUa f)
  refine ⟨hm, memPhysicalSobolev_zero _, ?_⟩
  have heq : hm.toLp _ = U₀ f := Lp.ext (hm.coeFn_toLp.trans (hUa f).symm)
  rw [heq, physicalSobolevNorm_zero, (partialUnitaryInverse n).norm_map]
  exact (U₀.le_opNorm f).trans (mul_le_mul_of_nonneg_right hUn (norm_nonneg f))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
