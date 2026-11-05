module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Conic

/-!
# Modified-operator bounds from original primitive profiles

For `app:ch_background:prop:bg-adjoint`, the original normalized amplitude and
L,V profiles produce the bound for each actual modified operator. The constant
precedes the high budget, interpolation order, and datum. Both common support
regularization and the exact degree-one conic normal are discharged by the
checked producers. Actual geometry and its primitive profiles remain inputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel
variable {n : ℕ}

/-- The generated operator L² bound in `app:ch_background:prop:bg-adjoint`,
with fixed reserve 2(n+1) and coefficient excess length(ds)-k. All amplitude
hypotheses concern the original normalized symbol; neither generated reserves
nor modified-operator estimates are inputs. -/
theorem exists_expansion_primitive_L2_operator
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
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (W D : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ i, 0 ≤ D i) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
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
  have hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j) := by
    intro d j
    cases d with
    | initial h =>
      exact Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL h))
    | carrier h =>
      exact Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hV h))
  obtain ⟨K, hK, hop⟩ := exists_supportedExpansion_L2_operator Φ hΦ g σ ρ B c J X Z Ω
    hg hX hZ hΩ (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) hr hsupp
    L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
  obtain ⟨C, hC, hc⟩ := exists_expansion_primitiveAmplitudeReserve L V a ha hfield
    ds χ t ht (2*(n+1)) W D hW hDpos g ρ X Z Ω J hX hZ hΩ hΩunit
    hg.threshold_pos hsupp hJ hclosed himage
  refine ⟨K*C, mul_nonneg hK hC, ?_⟩
  intro H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff
  have hres := hc H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff
  obtain ⟨U, hUn, hUa, hb⟩ := hop ds t ht _ hres
  refine ⟨U, by simpa only [mul_assoc] using hUn, hUa, ?_⟩
  intro f
  exact ⟨(hb f).1, by simpa only [mul_assoc] using (hb f).2⟩

/-- The integral bound supplied by the same bounded realization in
`exists_expansion_primitive_L2_operator` (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_expansion_primitive_L2_bound
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
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (W D : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ i, 0 ≤ D i) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
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
      ∀ f : Lp (α := Euclidean n) ℂ 2,
        MemLp (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n) ∧
        (eLpNorm (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
          (fun x ↦ t.amplitude u.1 x u.2) f) 2 (carrierMeasure n)).toReal ≤
          C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_expansion_primitive_L2_operator Φ hΦ g σ ρ B c J X Z Ω
    hg hX hZ hΩ a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn
    hΩunit hJ hclosed himage ds t ht W D hW hDpos
  refine ⟨C, hC, ?_⟩
  intro H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff f
  obtain ⟨_, _, _, hbound⟩ := hb H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff
  exact hbound f

end JanetCartan.ContinuumAdjoint.DerivativeKernels
