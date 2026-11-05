module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Quotient.Inverse

/-!
# Fixed forward quotient cutoffs in the original joint coordinates

The literal product norms are retained throughout. The smaller full/transverse
physical and data boxes fit the cutoff plateaus; the open epsilon buffers are
not removed. The regularity producer is `exists_actual_regular_quotient_buffers`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers CurrentFullPhase FrozenMenu
open FullPhaseCharts ActualPhase ActualComparison ActualEstimates InverseEstimates

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Center of the literal full forward norm ball in `app:eq:uniform-high-coeff`. -/
def fullForwardCenter (z : Euclidean 3) (η : Euclidean (n - 1)) : FullQuotientInput n :=
  ((0, spectatorCenter z, 0, 0), (z 0, η))

/-- Center of the literal transverse forward norm ball, including time and
carrier spectators (`app:eq:uniform-high-coeff`). -/
def transverseForwardCenter (z : Euclidean 3) (η : Euclidean (n - 1)) :
    TransverseQuotientInput n := ((0, (spectatorCenter z, 0, z 0), 0, 0), η)

/-- The literal full forward coefficient of `currentQuotientCoefficientNorm`
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullForwardCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    FullQuotientInput n → ℝ × Euclidean (n - 1) :=
  Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T))

/-- The literal transverse forward coefficient, with the original fixed
coordinate regrouping (`app:ch_seed:prop:seed-phase-charts`). -/
def transverseForwardCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    TransverseQuotientInput n → Euclidean (n - 1) :=
  fun q ↦ transverseChartFamily (current T Q) (spatialCarrier T)
    (transverseParameterReindex q.1) q.2

/-- First epsilon derivative of the actual full forward coefficient
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullForwardEpsilonCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) : FullQuotientInput n → ℝ × Euclidean (n - 1) :=
  fun q ↦ deriv (fun ε ↦ fullForwardCoefficient T Q ((ε,q.1.2),q.2)) q.1.1

/-- First epsilon derivative of the actual transverse forward coefficient
(`app:ch_seed:prop:seed-phase-charts`). -/
def transverseForwardEpsilonCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) : TransverseQuotientInput n → Euclidean (n - 1) :=
  fun q ↦ deriv (fun ε ↦ transverseForwardCoefficient T Q ((ε,q.1.2),q.2)) q.1.1

/-- The full working boxes, including the entire inverse data chart, fit the
forward plateau in their original norm (`app:ch_seed:prop:seed-phase-charts`). -/
theorem full_forward_workingBox_subset (z : Euclidean 3) (η : Euclidean (n - 1))
    {r s e ρ : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrρ : 4 * r ≤ ρ) (heρ : 2 * e ≤ ρ) :
    fullParameterBox z (s / 2) e ×ˢ dataBox z η (2 * r) ⊆
      closedBall (fullForwardCenter z η) (ρ / 2) := by
  exact full_chartBox_subset_ball z η hs hsr
    (by linarith : 2 * r ≤ ρ / 2) (by linarith : e ≤ ρ / 2)

/-- The transverse physical/data boxes fit the plateau, including the entire
inverse data chart (`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverse_forward_workingBox_subset (z : Euclidean 3) (η : Euclidean (n - 1))
    {r s e ρ : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrρ : 4 * r ≤ ρ) (heρ : 2 * e ≤ ρ) :
    transversePrimitiveBox z (s / 2) e ×ˢ closedBall η (2 * r) ⊆
      closedBall (transverseForwardCenter z η) (ρ / 2) := by
  exact transverse_chartBox_subset_ball z η hs hsr
    (by linarith : 2 * r ≤ ρ / 2) (by linarith : e ≤ ρ / 2)

/-- Fixed full forward cutoff for the two actual coefficients. The same-order
bound uses their literal norm ball. The actual regularity premise is supplied by
`exists_full_regular_inverse_phase_bounds` (`app:eq:uniform-high-coeff`). -/
theorem exists_full_forward_quotient_cutoff (z : Euclidean 3) (η : Euclidean (n - 1))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ χ : FullQuotientInput n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball (fullForwardCenter z η) ρ ∧
      closedBall (fullForwardCenter z η) (ρ / 2) ⊆ interior {x | χ x = 1} ∧
      (∀ f : FullQuotientInput n → ℝ × Euclidean (n - 1),
        (∀ x ∈ closedBall (fullForwardCenter z η) ρ, ContDiffAt ℝ ∞ f x) →
        ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧
        EqOn (fun x ↦ χ x • f x) f (closedBall (fullForwardCenter z η) (ρ / 2)) ∧
        tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ) ∧
      ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
        ∀ m (f : FullQuotientInput n → ℝ × Euclidean (n - 1)),
          (∀ x ∈ closedBall (fullForwardCenter z η) ρ, ContDiffAt ℝ ∞ f x) →
          cNorm univ m (fun x ↦ χ x • f x) ≤
            D m * cNorm (closedBall (fullForwardCenter z η) ρ) m f :=
  exists_quotient_coefficient_cutoff (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith : ρ / 2 < ρ))
    (isCompact_closedBall _ _) ball_subset_closedBall

/-- Fixed transverse forward cutoff on the literal primitive coordinates.
The actual regularity producer is `exists_transverse_regular_inverse_phase_bounds`
(`app:eq:uniform-high-coeff`). -/
theorem exists_transverse_forward_quotient_cutoff (z : Euclidean 3) (η : Euclidean (n - 1))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ χ : TransverseQuotientInput n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball (transverseForwardCenter z η) ρ ∧
      closedBall (transverseForwardCenter z η) (ρ / 2) ⊆ interior {x | χ x = 1} ∧
      (∀ f : TransverseQuotientInput n → Euclidean (n - 1),
        (∀ x ∈ closedBall (transverseForwardCenter z η) ρ, ContDiffAt ℝ ∞ f x) →
        ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧
        EqOn (fun x ↦ χ x • f x) f (closedBall (transverseForwardCenter z η) (ρ / 2)) ∧
        tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ) ∧
      ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
        ∀ m (f : TransverseQuotientInput n → Euclidean (n - 1)),
          (∀ x ∈ closedBall (transverseForwardCenter z η) ρ, ContDiffAt ℝ ∞ f x) →
          cNorm univ m (fun x ↦ χ x • f x) ≤
            D m * cNorm (closedBall (transverseForwardCenter z η) ρ) m f :=
  exists_quotient_coefficient_cutoff (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith : ρ / 2 < ρ))
    (isCompact_closedBall _ _) ball_subset_closedBall

/-- All four extended forward seminorms in the original joint product norms
(`app:eq:uniform-high-coeff`). -/
def extendedForwardQuotientNorm (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (χF : FullQuotientInput n → ℝ) (χT : TransverseQuotientInput n → ℝ) (m : ℕ) : ℝ :=
  (cNorm univ m (fun x ↦ χF x • fullForwardCoefficient T Q x) +
    cNorm univ m (fun x ↦ χF x • fullForwardEpsilonCoefficient T Q x)) +
  (cNorm univ m (fun x ↦ χT x • transverseForwardCoefficient T Q x) +
    cNorm univ m (fun x ↦ χT x • transverseForwardEpsilonCoefficient T Q x))

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
