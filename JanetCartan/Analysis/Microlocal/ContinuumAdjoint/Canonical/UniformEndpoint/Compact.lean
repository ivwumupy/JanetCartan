module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.Terms
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Compact

/-!
# Uniform finite summation on smooth compact data

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
/-- Uniform finite summation on smooth compact data. The constant precedes the varying phase, conic maps,
amplitude and trade fields. Consumed by the next uniform assembly layer
for `app:ch_background:prop:bg-adjoint`; no operator bound is assumed. -/
theorem exists_uniform_chartAdjoint_compact_raw_bound
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
      ∀ (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvs : HasCompactSupport v),
      let f : Lp (α := Euclidean n) ℂ 2 := (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
      let b : CarrierVariable n → ℂ := fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
        (fun x ↦ frequencyScaleAmplitude (halfOrderRadialFactor χ) a u.1 x u.2) v
      ∃ hb : MemLp b 2 (carrierMeasure n),
        MemPhysicalSobolev s (partialUnitaryInverse n (hb.toLp b)) ∧
        physicalSobolevNorm s (partialUnitaryInverse n (hb.toLp b)) ≤
          C * (fourierSobolevNorm s f + H * ‖f‖) := by
  classical
  have hex (ds : List (InitialCarrierDerivative n)) (hds : ds.length ≤ s) :=
    exists_uniform_expansion_primitive_term_bound ρ B c J X Z Ω hX hZ hΩ hn hΩunit
      ds W (D ds) hW (hDpos ds) s hs hds hρ hc
  choose C hC hb using hex
  let Cword (w : CarrierDerivativeIndex n s) : ℝ :=
    ((n+1) ^ (physicalDerivativeWord w).length : ℕ) *
      C (physicalDerivativeWord w) (physicalDerivativeWord_length_le w)
  have hCword (w : CarrierDerivativeIndex n s) : 0 ≤ Cword w :=
    mul_nonneg (Nat.cast_nonneg _) (hC _ _)
  refine ⟨(4 * Real.pi)^s * ∑ w, Cword w,
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun w _ ↦ hCword w)), ?_⟩
  intro Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage hphaseL hphaseV
  let a₀ := frequencyScaleAmplitude (halfOrderRadialFactor χ) a
  have hΦc : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2) :=
    hΦ.continuous.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
  intro H hH U hUopen hunit hlocal hrad hradBound hamp hcoeff v hv hvs
  dsimp only
  let f : Lp (α := Euclidean n) ℂ 2 := (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
  let E := fourierSobolevNorm s f + H * ‖f‖
  have hterm (ds : List (InitialCarrierDerivative n)) (hds : ds.length ≤ s)
      (t : {t // t ∈ adjointDerivativeExpansion L V ds a₀}) :
      MemLp (t.val.realize Φ v) 2 (carrierMeasure n) ∧
      (eLpNorm (t.val.realize Φ v) 2 (carrierMeasure n)).toReal ≤ C ds hds * E := by
    apply hb ds hds Φ hΦc g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf
      hD hΨ hinj hU hphase hJ hclosed himage t.val t.property H hH U hUopen hunit hlocal hrad hradBound
    · intro R hR p hp i hi
      exact hamp ds hds R hR p hp i
        (hi.trans (Nat.add_le_add_right (Nat.sub_le _ _) _))
    · intro p hp d hd j i hi
      exact hcoeff ds hds p hp d hd j i
        (hi.trans (Nat.add_le_add_right (Nat.sub_le _ _) _))
    · exact hv
    · exact hvs
  have hsupp' : ∀ z x η, x ∉ X → a₀ z x η = 0 := by
    intro z x η hx
    by_contra hnz
    exact hx (hsupp z x η hnz).2.1
  obtain ⟨hm, hmem, hbound⟩ := exists_memLp_chartAdjoint_physicalSobolevNorm_le_expansion
    s hX hr.amplitude hsupp' hL hV hΦ hphaseL hphaseV hv
    (fun ds hds t ht ↦ (hterm ds hds ⟨t,ht⟩).1)
  refine ⟨hm, hmem, hbound.trans ?_⟩
  have hw (w : CarrierDerivativeIndex n s) :
      ((adjointDerivativeExpansion L V (physicalDerivativeWord w) a₀).map
        (fun t ↦ (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal)).sum ≤ Cword w * E := by
    let ts := adjointDerivativeExpansion L V (physicalDerivativeWord w) a₀
    calc
      _ = (ts.attach.map (fun t ↦ (eLpNorm (t.val.realize Φ v) 2 (carrierMeasure n)).toReal)).sum := by simp [ts]
      _ ≤ (ts.attach.map (fun _ ↦ C (physicalDerivativeWord w)
          (physicalDerivativeWord_length_le w) * E)).sum :=
        List.sum_le_sum (fun t _ ↦ (hterm _ _ t).2)
      _ = Cword w * E := by
        simp only [List.map_const', List.sum_replicate, List.length_attach,
          ts, length_adjointDerivativeExpansion]
        dsimp only [Cword]
        push_cast
        ring
  calc
    _ ≤ (4 * Real.pi)^s * ∑ w, Cword w * E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ ↦ hw w)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
