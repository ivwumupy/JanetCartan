module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.PDONormal
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactImage

/-!
# Low bounds for actual compact modified carrier adjoints

For `app:ch_background:prop:bg-adjoint`, identify the actual regularized normal
with the normalized PDO and apply the checked scalar entry of its matrix bound.
All Fubini and realization premises are discharged from primitive compact
support and genuine conic-chart hypotheses.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ContinuumNormal AmplitudeBound FourierIntegral ModifiedNormalSymbol

variable {n : ℕ}
  (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
  (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
  (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
  (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
  (hm : Continuous m) (hms : HasCompactSupport m)
  {K : Set (Euclidean n)} (hK : IsCompact K)
  (has : ∀ u : CarrierVariable n, ∀ x, x ∉ K → a u.1 x u.2 = 0)

/-- The actual compact modified adjoint satisfies the low L² estimate once
its primitive symbol producer supplies the finite matrix jets. This theorem
discharges the normal identity and every source/frequency integrability premise;
no operator bound is assumed (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_modifiedCarrierOperator_adjoint_le
    (g : ModifiedNormalSymbol.Chart n) (hec : Continuous g.coordinates)
    (he : MeasurePreserving g.coordinates volume (volume.prod volume))
    (C : Euclidean n → Euclidean n → Set (Euclidean 2 × Euclidean n))
    (hC : ∀ x y, IsCompact (C x y))
    (hCD : ∀ x y p, p ∈ C x y → p.2 ∈ g.domain x y p.1)
    (hΨc : ∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) (C x y))
    (hUc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.inverse x y p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) '' C x y))
    (hJc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.jacobian x y p.1 p.2)
      (C x y))
    (hD : ∀ x y v, MeasurableSet (g.domain x y v))
    (hΨ : ∀ x y v t, t ∈ g.domain x y v →
      HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v t) (g.domain x y v) t)
    (hinj : ∀ x y v, InjOn (g.forward x y v) (g.domain x y v))
    (hU : ∀ x y v t, t ∈ g.domain x y v → g.inverse x y v (g.forward x y v t) = t)
    (hJ : ∀ x y v t, t ∈ g.domain x y v → (g.jacobian x y v t).det ≠ 0)
    (hsupp : ∀ x y p, p ∉ C x y → modifiedNormalDensity a m x y
      (TransportKernel.chartCarrierVariable g.coordinates p.1 p.2) = 0)
    (hphase : ∀ x y v t, t ∈ g.domain x y v →
      Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 x
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 -
        Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 y
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 =
          inner ℝ (x - y) (g.forward x y v t))
    (S : Euclidean n → Set (SourceChartVariables n)) (hS : ∀ x, IsCompact (S x))
    (hSC : ∀ x y v t, (v, t) ∈ C x y → (y, v, t) ∈ S x)
    (hSf : ∀ x, ContinuousOn (fun p : SourceChartVariables n ↦
      g.forward x p.1 p.2.1 p.2.2) (S x))
    (hn : 0 < n) (R M : ℝ) (hM : 0 ≤ M)
    (hb : GraphNormalAmplitudeBounds (matrixAmplitude g a m) R M) :
    ‖(modifiedCarrierOperator Φ a m hΦ ha hm hms hK has).adjoint‖ ≤
      Real.sqrt (fixedBoxAmplitudeConstant n R * M) := by
  apply norm_scalarCarrierAdjoint_of_compact_normal hn R M hM
    (matrixAmplitude g a m) hb
  · intro x
    apply hasCompactSupport_matrixAmplitude_source_frequency g a m x (S x)
      (hS x) (hSf x) (hU x)
    intro p hp
    apply hsupp x p.1 (p.2.1, p.2.2)
    exact fun hc ↦ hp (hSC x p.1 p.2.1 p.2.2 hc)
  · intro f
    have hi := modifiedCarrierOperator_normal_fullAmplitude_ae Φ a m hΦ ha hm hms hK has
      g.coordinates hec he g.domain g.forward g.inverse g.jacobian C hC hCD
      hΨc hUc hJc hD hΨ hinj hU hJ hsupp hphase f
    filter_upwards [hi] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1
    change (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
      physicalAmplitude g a m (x, y, k)) = _
    rw [physical_integral_eq_cycles]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [Real.fourierChar_apply, matrixAmplitude, positionAmplitude,
      freezingOutputProjection_pairedPosition, freezingSourceProjection_pairedPosition]

/-- The low constant is chosen before the arbitrary modified amplitude and
compact regularizer. Primitive half-order jets, weighted conic inverse and
Jacobian jets, and primitive support imply the actual adjoint bound. All
normal and PDO hypotheses are discharged, with budget linear in `A`
(`app:ch_background:prop:bg-adjoint`). Removal of regularization is separate. -/
theorem exists_uniform_modifiedCarrierOperator_adjoint_bound
    (g : Chart n) (s : JetRescaling g) (ρ B c : ℝ)
    (L : Set (JointVariables n)) (V : Set (Euclidean 2))
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L V)
    (X : Set (Euclidean n)) (hX : IsCompact X) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ) (hn : 0 < n)
    (R : ℝ) (hXR : ∀ x ∈ X, ∀ i, |x i| ≤ R) :
    ∃ Q ≥ 0, ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ)
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
  obtain ⟨D, hD, hd⟩ := hg.exists_graphNormalAmplitudeBounds X Z Ω M hXR
  refine ⟨Real.sqrt (fixedBoxAmplitudeConstant n R * D), Real.sqrt_nonneg _, ?_⟩
  intro a m A ha hm hms has hr hamp hmj he C hC hCD hΨc hUc hJc hDmeas
    hΨ hinj hU hJ hsupp hphase S hS hSC hSf
  have hb := hd a m A hr hamp hmj
  have hbound := norm_modifiedCarrierOperator_adjoint_le Φ a m hΦ ha hm hms hX has
    g hr.coordinates.continuous he C hC hCD hΨc hUc hJc hDmeas hΨ hinj hU hJ
    hsupp hphase S hS hSC hSf hn R (D * A^2) (mul_nonneg hD (sq_nonneg A)) hb
  convert hbound using 1
  rw [← mul_assoc, Real.sqrt_mul (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hD),
    Real.sqrt_sq hamp.budget_nonneg]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
