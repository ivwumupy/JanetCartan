module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Forward

/-!
# Identify the actual physical transport chart

The averaged gradient of the literal row is the zero-epsilon full phase chart,
conjugated by the retained orthogonal physical coordinates. This is the
geometric connection needed to instantiate the conic inverse in
`app:ch_background:eq:bg-Psi`; the identity does not assume a chart or an
oscillatory operator estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Orthogonal transformation of the literal physical phase gradient.
This identifies the same functions even where total derivatives are zero
by convention (`app:ch_background:eq:bg-Psi`). -/
theorem gradient_transportPosition (x : Euclidean n) (z : CarrierParameter)
    (η : Euclidean (n - 1)) :
    physicalCoordinates T (gradient (fun y ↦ inner ℝ (transportPosition T Q (y, z)) η) x) =
      gradient (Comparison.modulationPhase (ActualPhase.current T Q) (ActualPhase.spatialCarrier T)
        0 z.2 (z.1, η)) (physicalCoordinates T x) := by
  let e := physicalCoordinates T
  let f := Comparison.modulationPhase (ActualPhase.current T Q) (ActualPhase.spatialCarrier T)
    0 z.2 (z.1, η)
  have he : (fun y ↦ inner ℝ (transportPosition T Q (y, z)) η) = f ∘ e := by
    funext y
    exact transportPosition_inner_eq_comparison T Q y z η
  rw [he]
  change e (gradient (f ∘ e) x) = gradient f (e x)
  apply ext_inner_right ℝ
  intro v
  rw [e.inner_map_eq_flip, inner_gradient_left, inner_gradient_left]
  have hd : fderiv ℝ (f ∘ e) x =
      (fderiv ℝ f (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap :=
    e.toContinuousLinearEquiv.comp_right_fderiv
  rw [hd]
  change (fderiv ℝ f (e x)) (e (e.symm v)) = (fderiv ℝ f (e x)) v
  rw [e.apply_symm_apply]

/-- Exact identification of the physical averaged gradient with the released
zero-epsilon full chart. Both positions, the distinguished carrier coordinate,
and both spectators are retained (`app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_eq_fullChart (p : InputVariables n) :
    (physicalCoordinates T (transportAveragedGradient (transportPosition T Q) p)).ofLp =
      Comparison.fullChart (ActualPhase.current T Q) (ActualPhase.spatialCarrier T)
        0 p.2.1.2 (physicalCoordinates T p.1.1) (physicalCoordinates T p.1.2)
          (p.2.1.1, p.2.2) := by
  unfold transportAveragedGradient
  have hi := (physicalCoordinates T).toLinearIsometry.intervalIntegral_comp_comm
    (fun t : ℝ ↦ gradient (fun x ↦ inner ℝ (transportPosition T Q (x, p.2.1)) p.2.2)
      (p.1.2 + t • (p.1.1 - p.1.2))) (a := 0) (b := 1) (μ := MeasureTheory.volume)
  change (∫ t in (0 : ℝ)..1, physicalCoordinates T
      (gradient (fun x ↦ inner ℝ (transportPosition T Q (x, p.2.1)) p.2.2)
        (p.1.2 + t • (p.1.1 - p.1.2)))) = physicalCoordinates T
      (∫ t in (0 : ℝ)..1,
        gradient (fun x ↦ inner ℝ (transportPosition T Q (x, p.2.1)) p.2.2)
          (p.1.2 + t • (p.1.1 - p.1.2))) at hi
  rw [← hi]
  simp_rw [gradient_transportPosition T Q]
  simp only [map_add, map_smul, map_sub]
  rfl

/-- The literal two-point phase identity, with its spatial regularity proved
from the actual Hamilton family (`app:ch_background:eq:bg-Psi`). -/
theorem transportPosition_sub_eq_inner_averagedGradient
    {c C : ℝ} (hP : P.IsValid c C)
    {x y : Euclidean n} (hx : x ∈ ball 0 T.family.radius)
    (hy : y ∈ ball 0 T.family.radius) {z : CarrierParameter}
    (hz : parameter z ∈ parameterInterior (3 * P.radius / 2))
    (η : Euclidean (n - 1)) :
    inner ℝ (transportPosition T Q (x, z)) η -
        inner ℝ (transportPosition T Q (y, z)) η =
      inner ℝ (x - y)
        (transportAveragedGradient (transportPosition T Q) ((x, y), z, η)) := by
  have hY : ContDiffOn ℝ ∞ (fun x ↦ transportPosition T Q (x, z))
      (ball 0 T.family.radius) :=
    (transportPosition_smooth T Q hP).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ h ↦ ⟨h, hz⟩)
  have hphase : ContDiffOn ℝ 1 (fun x ↦ inner ℝ (transportPosition T Q (x, z)) η)
      (ball 0 T.family.radius) :=
    (hY.of_le (by simp)).inner ℝ contDiffOn_const
  have hh := phase_sub_eq_inner_averagedPhaseGradient
    (S := fun (u : CarrierVariable n) x ↦ inner ℝ (transportPosition T Q (x, u.1)) u.2)
    (p := (z, η))
    isOpen_ball (convex_ball _ _) hphase hx hy
  exact hh.trans (real_inner_comm _ _)

end JanetCartan.ContinuumRow.CanonicalCarrier
