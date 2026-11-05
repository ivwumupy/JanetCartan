module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.NormalSymbols
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.RegularizedBound

/-!
# Uniform compact adjoints before phase and chart

The constant in the actual normal/PDO estimate precedes all varying phase and
conic chart data. The original half-order amplitude, carrier measure and Fourier
normalization are preserved. Consumer: removal of regularization for the uniform
endpoint in `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
open ContinuumRow DerivativeKernels DerivativeKernels.ModifiedNormalSymbol
open TransportKernel AmplitudeBound FourierIntegral
variable {n : ℕ}

/-- The compact modified adjoint bound, with its constant fixed before the phase,
forward/inverse chart, rescaling, amplitude and regularizer. All normal identity
and integrability requirements are proved by the existing literal normal theorem;
only its primitive hypotheses remain (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_geometryUniform_modifiedCarrierOperator_adjoint_bound
    (ρ B c : ℝ) (hc : 0 < c)
    (L : Set (JointVariables n)) (V : Set (Euclidean 2))
    (X : Set (Euclidean n)) (hX : IsCompact X) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ) (hn : 0 < n)
    (R : ℝ) (hXR : ∀ x ∈ X, ∀ i, |x i| ≤ R) :
    ∃ Q ≥ 0,
      ∀ (Φ : CarrierParameter → Euclidean n → Euclidean (n-1) → ℝ)
        (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
        (g : Chart n) (s : JetRescaling g)
        (_hg : PrimitiveJetGeometry g s (2*(n+1)) ρ B c L V),
      ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ)
      (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
      (hm : Continuous m) (hms : HasCompactSupport m)
      (has : ∀ u : CarrierVariable n, ∀ x, x ∉ X → a u.1 x u.2 = 0)
      (_hr : PrimitiveRegularity g a m)
      (_hamp : PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X V Z Ω L a)
      (_hmj : PrimitiveRegularizerReserve (2 * (n + 1)) ρ M m)
    (_he : MeasurePreserving g.coordinates volume (volume.prod volume))
    (C : Euclidean n → Euclidean n → Set (Euclidean 2 × Euclidean n))
    (_hC : ∀ x y, IsCompact (C x y))
    (_hCD : ∀ x y p, p ∈ C x y → p.2 ∈ g.domain x y p.1)
    (_hΨc : ∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) (C x y))
    (_hUc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.inverse x y p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) '' C x y))
    (_hJc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.jacobian x y p.1 p.2)
      (C x y))
    (_hD : ∀ x y v, MeasurableSet (g.domain x y v))
    (_hΨ : ∀ x y v t, t ∈ g.domain x y v →
      HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v t) (g.domain x y v) t)
    (_hinj : ∀ x y v, InjOn (g.forward x y v) (g.domain x y v))
    (_hU : ∀ x y v t, t ∈ g.domain x y v → g.inverse x y v (g.forward x y v t) = t)
    (_hJ : ∀ x y v t, t ∈ g.domain x y v → (g.jacobian x y v t).det ≠ 0)
    (_hsupp : ∀ x y p, p ∉ C x y → modifiedNormalDensity a m x y
      (TransportKernel.chartCarrierVariable g.coordinates p.1 p.2) = 0)
    (_hphase : ∀ x y v t, t ∈ g.domain x y v →
      Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 x
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 -
        Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 y
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 =
          inner ℝ (x - y) (g.forward x y v t))
    (S : Euclidean n → Set (SourceChartVariables n)) (_hS : ∀ x, IsCompact (S x))
    (_hSC : ∀ x y v t, (v, t) ∈ C x y → (y, v, t) ∈ S x)
    (_hSf : ∀ x, ContinuousOn (fun p : SourceChartVariables n ↦
      g.forward x p.1 p.2.1 p.2.2) (S x))
    , ‖(modifiedCarrierOperator Φ a m hΦ ha hm hms hX has).adjoint‖ ≤ Q * A := by
  obtain ⟨D, hD, hd⟩ := exists_uniform_graphNormalAmplitudeBounds (n := n) B c hc V M R
  refine ⟨Real.sqrt (fixedBoxAmplitudeConstant n R * D), Real.sqrt_nonneg _, ?_⟩
  intro Φ hΦ g s hg a m A ha hm hms has hr hamp hmj he C hC hCD hΨc hUc hJc hDmeas
    hΨ hinj hU hJ hsupp hphase S hS hSC hSf
  have hb := hd hg hXR a m A hr hamp hmj
  have hbound := norm_modifiedCarrierOperator_adjoint_le Φ a m hΦ ha hm hms hX has
    g hr.coordinates.continuous he C hC hCD hΨc hUc hJc hDmeas hΨ hinj hU hJ
    hsupp hphase S hS hSC hSf hn R (D * A^2) (mul_nonneg hD (sq_nonneg A)) hb
  convert hbound using 1
  rw [← mul_assoc, Real.sqrt_mul (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hD),
    Real.sqrt_sq hamp.budget_nonneg]

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
