module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.LocalFrameAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# The literal projected frame and its coefficient extension

Apply original-target uniqueness using exactly the initializer's physical
coefficient ball and inner transverse state ball. In particular, the extension
radius is the original `b`, not the later source-cutoff radius
(`app:ch_regular:eq:coefficient-extension`, `app:lem:common-hamilton-phase`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference ProjectedStressFrame ProtectedFlow

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- On the original coefficient ball the two actual frames agree on an OPEN
neighborhood of every retained state. This also identifies all coefficient
jets used by the reduced source (`app:ch_regular:eq:coefficient-extension`). -/
theorem projectedStress_extended_eqOn_ball
    (F : Euclidean n → Euclidean N) (ext : BallExtension.Parameters (Euclidean n))
    {b : ℝ} (hcenter : ext.center = 0) (hradius : ext.radius = b) :
    EqOn (projectedStress F) (extendedProjectedStress ext F) (ball (0 : Euclidean n) b) := by
  intro x hx
  apply (affineFrameExtension_eqOn ext (projectedStress F) ?_).symm
  simpa only [hcenter, hradius] using ball_subset_closedBall hx

/-- Extending the admitted frame on the ORIGINAL coefficient ball preserves
its exact low seminorm on the retained state ball. Thus the second admission
is proved from the first, without choosing another threshold or history
(`app:ch_regular:eq:coefficient-extension`, `app:lem:common-hamilton-phase`). -/
theorem exists_admitted_affineFrameExtension
    (ext : BallExtension.Parameters (Euclidean n))
    {b : ℝ} (hcenter : ext.center = 0) (hradius : ext.radius = b)
    (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hphysical : ∀ z ∈ T.data.localReference.stateDomain,
      z.1 ∈ ball (0 : Euclidean n) b)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    ∃ Q' : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q'.1 = affineFrameExtension ext Q.1 ∧
      ∀ m : ℕ, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
          (Q'.1 - fun _ ↦ cubeStress n) =
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
          (Q.1 - fun _ ↦ cubeStress n) := by
  have hsmooth : ContDiff ℝ ∞ (affineFrameExtension ext Q.1) :=
    contDiff_affineFrameExtension ext (Q.2.1.mono (by simpa only [hcenter, hradius] using hBU))
  have hball := frameBall_subset_of_stateDomain T.data.localReference hphysical
  have he : EqOn (affineFrameExtension ext Q.1) Q.1 (ball (0 : Euclidean n) b) := by
    intro x hx
    exact affineFrameExtension_eqOn ext Q.1
      (by simpa only [hcenter, hradius] using ball_subset_closedBall hx)
  have hnorm (m : ℕ) :
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
          (affineFrameExtension ext Q.1 - fun _ ↦ cubeStress n) =
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
          (Q.1 - fun _ ↦ cubeStress n) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Set.image_congr
    intro x hx
    have hh : (affineFrameExtension ext Q.1 - fun _ ↦ cubeStress n) =ᶠ[nhds x]
        (Q.1 - fun _ ↦ cubeStress n) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hball hx))
        (fun y hy ↦ by simp only [Pi.sub_apply, he hy])
    exact congrArg norm ((hh.iteratedFDeriv ℝ k).eq_of_nhds)
  exact ⟨⟨affineFrameExtension ext Q.1, hsmooth.contDiffOn,
    (hnorm 6).trans_lt Q.2.2⟩, rfl, hnorm⟩

/-- The raw and extended Hamilton charts coincide on the SAME original target.
The physical containment, inner radius, range and gap are exactly the witnesses
of `CorrectedAtoms.exists_common_initialized_history_primary_correction`;
`ProtectedFlow.affineFrameExtension_eqOn` discharges coefficient agreement.
No phase equality is a premise (`app:lem:common-hamilton-phase`,
`app:ch_regular:eq:coefficient-extension`). -/
theorem coordinates_eqOn_projectedStress_extended
    (F : Euclidean n → Euclidean N) (ext : BallExtension.Parameters (Euclidean n))
    {b : ℝ} (hcenter : ext.center = 0) (hradius : ext.radius = b)
    (hBU : ball (0 : Euclidean n) b ⊆ U)
    (hphysical : ∀ z ∈ T.data.localReference.stateDomain,
      z.1 ∈ ball (0 : Euclidean n) b)
    (Q Q' : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hQ : Q.1 = projectedStress F) (hQ' : Q'.1 = extendedProjectedStress ext F)
    {R : ℝ} (hR : R ≤ T.data.localReference.stateRadius)
    (hgap : ∀ z ∈ closedBall (0, T.data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hrange : ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) R)
    (hrange' : ∀ q ∈ (T.family.flow Q').time ×ˢ (T.family.flow Q').parameters,
      ((T.family.flow Q').position q, (T.family.flow Q').momentum q) ∈
        closedBall (0, T.data.center) R) :
    EqOn (T.currentChart Q).coordinates (T.currentChart Q').coordinates T.target := by
  apply T.coordinates_eqOn_of_frame_eqOn Q Q' isOpen_ball hBU hR
    ((closedBall_subset_closedBall hR).trans
      (frameBall_subset_of_stateDomain T.data.localReference hphysical))
    _ hgap hrange hrange'
  rw [hQ, hQ']
  exact projectedStress_extended_eqOn_ball F ext hcenter hradius

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
