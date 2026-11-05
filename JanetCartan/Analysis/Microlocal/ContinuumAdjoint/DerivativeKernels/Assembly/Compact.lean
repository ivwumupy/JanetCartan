module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Terms
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives

/-!
# Raw adjoint Sobolev estimate on compact smooth data

Assemble the actual modified conic operators, joint coefficient/data
interpolation, and partial radian Fourier weak derivatives for
`app:ch_background:prop:bg-adjoint`. All derivatives occur before physical
initial cutoffs, using the shared carrier measure and physical Sobolev norm.
The original primitive profiles and conic geometry remain conditional inputs.
`Assembly.AllData` extends this same operator to all Sobolev data, and
`Assembly.Literal` instantiates the literal vector carrier components.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel Pseudodifferential CarrierSobolev
variable {n : ℕ}

/-- Positive integer raw Sobolev bound for the actual chart adjoint in
`app:ch_background:prop:bg-adjoint`, on smooth compact data. A single symbol
reserve 2(n+1) works for every s. Constants precede H and the datum. The
normalized amplitude and the trade fields are the only jet inputs; modified
operator estimates, weak derivatives, and their summation are all proved.
Profiles may depend on the derivative word, as its arbitrary directional
vectors need not have norm one. Only finitely many coordinate words enter C. -/
theorem exists_chartAdjoint_compact_raw_bound
    (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
    (hΦ : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ Φ p.1 p.2.1 p.2.2))
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
    (W : ℕ → ℝ) (D : List (InitialCarrierDerivative n) → ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i) (hDpos : ∀ ds i, 0 ≤ D ds i)
    (hphaseL : ∀ z x η h, x ∈ X → inner ℝ h η =
      fderiv ℝ (fun y ↦ Φ z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ X → fderiv ℝ (fun w ↦ Φ w x η) z h =
      fderiv ℝ (fun y ↦ Φ z y η) x (V z x h))
    (s : ℕ) (hs : 0 < s) :
    ∃ C ≥ 0, ∀ H : ℝ, 1 ≤ H →
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
  let a₀ := frequencyScaleAmplitude (halfOrderRadialFactor χ) a
  have hΦc : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2) :=
    hΦ.continuous.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
  have hex (ds : List (InitialCarrierDerivative n)) (hds : ds.length ≤ s)
      (t : {t // t ∈ adjointDerivativeExpansion L V ds a₀}) :=
    exists_expansion_primitive_term_bound Φ hΦc g σ ρ B c J X Z Ω hg hX hZ hΩ
      a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hn hΩunit
      hJ hclosed himage ds t.val t.property W (D ds) hW (hDpos ds) s hs hds
  choose C hC hb using hex
  let Cword (w : CarrierDerivativeIndex n s) : ℝ :=
    ((adjointDerivativeExpansion L V (physicalDerivativeWord w) a₀).attach.map
      (C (physicalDerivativeWord w) (physicalDerivativeWord_length_le w))).sum
  have hCword (w : CarrierDerivativeIndex n s) : 0 ≤ Cword w :=
    List.sum_nonneg (by intro x hx; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx; exact hC _ _ t)
  refine ⟨(4 * Real.pi)^s * ∑ w, Cword w,
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun w _ ↦ hCword w)), ?_⟩
  intro H hH U hU hunit hlocal hrad hradBound hamp hcoeff v hv hvs
  dsimp only
  let f : Lp (α := Euclidean n) ℂ 2 := (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
  let E := fourierSobolevNorm s f + H * ‖f‖
  have hterm (ds : List (InitialCarrierDerivative n)) (hds : ds.length ≤ s)
      (t : {t // t ∈ adjointDerivativeExpansion L V ds a₀}) :
      MemLp (t.val.realize Φ v) 2 (carrierMeasure n) ∧
      (eLpNorm (t.val.realize Φ v) 2 (carrierMeasure n)).toReal ≤ C ds hds t * E := by
    apply hb ds hds t H hH U hU hunit hlocal hrad hradBound
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
      _ ≤ (ts.attach.map (fun t ↦ C (physicalDerivativeWord w)
          (physicalDerivativeWord_length_le w) t * E)).sum :=
        List.sum_le_sum (fun t _ ↦ (hterm _ _ t).2)
      _ = Cword w * E := by simp [Cword, ts, List.sum_map_mul_right]
  calc
    _ ≤ (4 * Real.pi)^s * ∑ w, Cword w * E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ ↦ hw w)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end JanetCartan.ContinuumAdjoint.DerivativeKernels
