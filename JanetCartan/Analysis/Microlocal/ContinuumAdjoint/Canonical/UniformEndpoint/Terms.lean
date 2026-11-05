module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.Operators
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Terms

/-!
# Uniform interpolation for the actual adjoint terms

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
/-- Uniform interpolation for the actual adjoint terms. The constant precedes the varying phase, conic maps,
amplitude and trade fields. Consumed by the next uniform assembly layer
for `app:ch_background:prop:bg-adjoint`; no operator bound is assumed. -/
theorem exists_uniform_expansion_primitive_term_bound
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
    (s : ℕ)
    (hs : 0 < s)
    (hds : ds.length ≤ s)
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
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ ds.length - t.dataDerivatives.length + (2*(n+1)),
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ D i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / s)) →
      (∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ d ∈ ds, ∀ j i,
        i ≤ ds.length - t.dataDerivatives.length + (2*(n+1)) →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ D i * H ^ (((i-(2*(n+1)) : ℕ) : ℝ) / s)) →
      ∀ (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvs : HasCompactSupport v),
      let f : Lp (α := Euclidean n) ℂ 2 := (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
      MemLp (t.realize Φ v) 2 (carrierMeasure n) ∧
        (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal ≤
          C * (fourierSobolevNorm s f + H * ‖f‖) := by
  obtain ⟨C, hC, hop⟩ := exists_uniform_expansion_primitive_L2_operator
    ρ B c J X Z Ω hX hZ hΩ hn hΩunit ds W D hW hDpos hρ hc
  refine ⟨C * (2 * Real.pi) ^ s, by positivity, ?_⟩
  intro Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ hinj hU hphase hJ hclosed himage t ht
  have hop' := hop Φ hΦ g σ hg a χ ha hr hsupp L V hL hV he hei hdom hf hD hΨ
    hinj hU hphase hJ hclosed himage t ht
  intro H hH U hU hunit hlocal hrad hradBound hamp hcoeff v hv hvs
  dsimp only
  let f : Lp (α := Euclidean n) ℂ 2 := (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
  let w := euclideanCoordinateDerivList t.dataDerivatives v
  have hw : MemLp w 2 volume :=
    (contDiff_euclideanCoordinateDerivList hv _).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordinateDerivList hvs _)
  let fw := hw.toLp w
  have heq : (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2)
      (fun x ↦ t.amplitude u.1 x u.2) fw) = t.realize Φ v := by
    funext u
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    exact congrArg (fun z ↦ NormalComparison.oscillatoryFactor (-1) (Φ u.1 x u.2) *
      (t.amplitude u.1 x u.2 * z)) hx
  obtain ⟨_, _, _, hopBound⟩ := hop' H s hH (by exact_mod_cast hs) U hU hunit
    hlocal hrad hradBound hamp hcoeff
  obtain ⟨hm, hb⟩ := hopBound fw
  rw [heq] at hm hb
  refine ⟨hm, ?_⟩
  have hfw : ‖fw‖ ≤ (2 * Real.pi) ^ t.dataDerivatives.length *
      fourierSobolevNorm t.dataDerivatives.length f := by
    simpa only [Nat.cast_zero, zero_add, fourierSobolevNorm_zero] using
      fourierSobolevNorm_coordinateDerivList_toLp_le t.dataDerivatives 0 v hv hvs
  have hk := (dataDerivatives_length_le_expansion L V ds _ t ht).trans hds
  have hexp : H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / s) ≤
      H ^ (((s - t.dataDerivatives.length : ℕ) : ℝ) / s) :=
    Real.rpow_le_rpow_of_exponent_le hH
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hds _)
        (Nat.cast_nonneg s))
  have hi := adjoint_coefficient_data_interpolate hs hk 1 zero_le_one
    (le_trans zero_le_one hH) (R := 1) (A := H ^
      (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / s))
    (by simpa using hexp) f (memFourierSobolev_nat_toLp s v hv hvs)
  simp only [Real.sqrt_one, one_mul] at hi
  calc
    _ ≤ C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / s) * ‖fw‖ := hb
    _ ≤ C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / s) *
        ((2 * Real.pi) ^ t.dataDerivatives.length * fourierSobolevNorm t.dataDerivatives.length f) :=
      mul_le_mul_of_nonneg_left hfw (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
    _ = (C * (2 * Real.pi) ^ t.dataDerivatives.length) *
        (H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / s) *
          fourierSobolevNorm t.dataDerivatives.length f) := by ring
    _ ≤ (C * (2 * Real.pi) ^ t.dataDerivatives.length) *
        (fourierSobolevNorm s f + H * ‖f‖) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (add_nonneg (fourierSobolevNorm_nonneg _ _) (mul_nonneg (by linarith) (norm_nonneg _)))
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [Real.two_le_pi]) hk) hC

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
