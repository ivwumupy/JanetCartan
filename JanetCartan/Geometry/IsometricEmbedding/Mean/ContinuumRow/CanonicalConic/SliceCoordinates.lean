module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.JacobianBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Basic

/-!
# Literal volume and determinant matching for the canonical carrier

Use the retained orthogonal physical coordinates also to encode the integration
slice `(s,η)`. This preserves the original product Lebesgue measure exactly.
The physical derivative is conjugate to the adapted derivative, so their
absolute determinants agree without a normalization factor (`bg-jacobian`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Volume-preserving coordinates for the actual `(s,η)` substitution. The
underlying coordinates are the SAME orthogonal coordinates used by the retained
Hamilton chart (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def adaptedSliceCoordinates : TransportSliceCoordinates n where
  equiv := (physicalCoordinates T).toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1)))
  measurePreserving := (WithLp.volume_preserving_ofLp ℝ (Euclidean (n - 1))).comp
    (physicalCoordinates T).measurePreserving

/-- Coordinate matching is literal, with no scaling of the initial measure
(`app:ch_background:eq:bg-Psi`). -/
@[simp] theorem adaptedSliceCoordinates_apply (x : Euclidean n) :
    (adaptedSliceCoordinates T).equiv x = (physicalCoordinates T x).ofLp := rfl

/-- The measurable coordinates used by `TransportKernel.ChartInputs`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def kernelSliceCoordinates : Euclidean n ≃ᵐ (ℝ × Euclidean (n - 1)) :=
  (adaptedSliceCoordinates T).equiv.toHomeomorph.toMeasurableEquiv

/-- The kernel's coordinate identification preserves `ds dη` exactly
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem kernelSliceCoordinates_measurePreserving :
    MeasurePreserving (kernelSliceCoordinates T) volume (volume.prod volume) :=
  (adaptedSliceCoordinates T).measurePreserving

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The physical slice map is conjugate to the actual adapted map, preserving
both physical positions and the original spectator (`app:ch_background:eq:bg-Psi`). -/
theorem transportSliceForward_eq_adapted (p : InputVariables n) :
    transportSliceForward (adaptedSliceCoordinates T) (transportPosition T Q) p =
      (adaptedSliceCoordinates T).equiv.symm ∘
        adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2) ∘
          (adaptedSliceCoordinates T).equiv := by
  funext x
  apply (adaptedSliceCoordinates T).equiv.injective
  rw [Function.comp_apply, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Exact equality of physical and adapted derivative determinants. This is
used to supply `SymbolInputs.jacobian_eq`, not a desired symbol estimate
(`app:ch_background:eq:bg-jacobian`). -/
theorem transportSliceDifferential_det_eq (p : InputVariables n)
    (hd : DifferentiableAt ℝ (adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2))
      (p.2.1.1, p.2.2)) :
    (transportSliceDifferential (adaptedSliceCoordinates T) (transportPosition T Q) p).det =
      (fderiv ℝ (adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2)) (p.2.1.1, p.2.2)).det := by
  let c := (adaptedSliceCoordinates T).equiv
  let f := adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2)
  let u := (p.2.1.1, p.2.2)
  have hd' : HasFDerivAt f (fderiv ℝ f u) (c (c.symm u)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hd.hasFDerivAt
  have hc := c.symm.hasFDerivAt.comp (c.symm u)
    (hd'.comp (c.symm u) c.hasFDerivAt)
  have he : transportSliceDifferential (adaptedSliceCoordinates T) (transportPosition T Q) p =
      c.symm.toContinuousLinearMap.comp ((fderiv ℝ f u).comp c.toContinuousLinearMap) := by
    rw [transportSliceDifferential, transportSliceForward_eq_adapted]
    exact hc.fderiv
  rw [he]
  exact LinearMap.det_conj (fderiv ℝ f u).toLinearMap c.symm.toLinearEquiv

/-- Exact identification with the literal measure-normalized Jacobian used
by the global carrier producer (`app:ch_background:eq:bg-jacobian`). -/
theorem transportAbsoluteJacobian_eq_adaptedJacobian (p : InputVariables n)
    (hd : DifferentiableAt ℝ (adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2))
      (p.2.1.1, p.2.2)) :
    transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p =
      adaptedJacobian T Q (p.2.1.2, p.1.1, p.1.2) (p.2.1.1, p.2.2) := by
  exact congrArg abs (transportSliceDifferential_det_eq T Q p hd)

/-- The adapted output product norm is bounded by the physical Euclidean
norm; the orthogonal identification retains the paper's frequency convention
(`app:ch_background:eq:bg-Psi`). -/
theorem adaptedTransportChart_norm_le_physical
    (p : Euclidean 2 × Euclidean n × Euclidean n) (u : ℝ × Euclidean (n - 1)) :
    ‖adaptedTransportChart T Q p u‖ ≤
      ‖transportAveragedGradient (transportPosition T Q) ((p.2.1, p.2.2), (u.1, p.1), u.2)‖ := by
  rw [← (physicalCoordinates T).norm_map
    (transportAveragedGradient (transportPosition T Q) ((p.2.1, p.2.2), (u.1, p.1), u.2))]
  exact max_le (WithLp.norm_fst_le ℝ _) (WithLp.norm_snd_le ℝ _)

/-- The converse physical comparison has one fixed coordinate norm, chosen
before the immersion (`app:ch_background:eq:bg-Psi`). -/
theorem physicalTransportChart_norm_le_adapted
    (p : Euclidean 2 × Euclidean n × Euclidean n) (u : ℝ × Euclidean (n - 1)) :
    ‖transportAveragedGradient (transportPosition T Q) ((p.2.1, p.2.2), (u.1, p.1), u.2)‖ ≤
      ‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖ *
        ‖adaptedTransportChart T Q p u‖ := by
  have he : transportAveragedGradient (transportPosition T Q)
      ((p.2.1, p.2.2), (u.1, p.1), u.2) =
        (adaptedSliceCoordinates T).equiv.symm (adaptedTransportChart T Q p u) := by
    apply (adaptedSliceCoordinates T).equiv.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [he]
  exact (adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap.le_opNorm _

end JanetCartan.ContinuumRow.CanonicalConic
