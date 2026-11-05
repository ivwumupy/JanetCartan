module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedSourceAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Physical frame admission from the original coefficient extension

The common initializer retains the whole Hamilton state domain inside the
coefficient ball. Hence the actual physical stress and its prescribed affine
extension agree near every point of the closed frame ball. Their derivative
seminorms agree at every order, so the selected family's phase margin admits
the physical stress used by `exists_retainedHistoryCanonicalSampling`.

No new stress field or reference is selected. The source is
`app:ch_regular:eq:coefficient-extension` and `app:ch_seed:setup:seed-current`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open ProtectedFlow ProjectedStressFrame GeometricProfile
open ActualCarriers FrozenMenu CurrentFullPhase

/-- Every stress seminorm on the initializer's original closed frame ball
is unchanged by the supplied coefficient extension. The retained state-domain
buffer gives neighborhood equality even at its boundary
(`app:ch_regular:eq:coefficient-extension`, `app:ch_seed:setup:seed-current`). -/
theorem cNorm_projectedStress_sub_eq_extended_on_stateBall
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (ext : BallExtension.Parameters (Euclidean n)) (hext : ext.center = 0)
    (hphysical : ∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ ball 0 ext.radius)
    (F : Euclidean n → Euclidean N) (m : ℕ) :
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
        (projectedStress F - fun _ ↦ cubeStress n) =
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
        (extendedProjectedStress ext F - fun _ ↦ cubeStress n) := by
  apply cNorm_eq_of_eventuallyEq
  intro x hx
  have hxball := frameBall_subset_of_stateDomain T.data.localReference hphysical hx
  filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
  have hy' : y ∈ closedBall ext.center ext.radius := by
    rw [hext]
    exact ball_subset_closedBall hy
  exact congrArg (fun Q ↦ Q - cubeStress n) (affineFrameExtension_eqOn ext (projectedStress F) hy').symm

/-- The actual extended-coefficient phase margin admits the SAME physical
stress to the canonical atom's original subtype. Geometry gives smoothness;
the exact seminorm equality transfers the threshold without changing it
(`app:ch_mean_pairs:defn:mean-canonical`, `app:ch_response:cor:current-atoms`). -/
theorem physicalProjectedStress_admitted_of_extended
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (ext : BallExtension.Parameters (Euclidean n)) (hext : ext.center = 0)
    (hphysical : ∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ ball 0 ext.radius)
    (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hsmall : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (extendedProjectedStress ext F - fun _ ↦ cubeStress n) < T.family.threshold) :
    ContDiffOn ℝ ∞ (projectedStress F) U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
  refine ⟨contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), ?_⟩
  rw [cNorm_projectedStress_sub_eq_extended_on_stateBall T ext hext hphysical F]
  exact hsmall

end JanetCartan.CanonicalAtomRealization
