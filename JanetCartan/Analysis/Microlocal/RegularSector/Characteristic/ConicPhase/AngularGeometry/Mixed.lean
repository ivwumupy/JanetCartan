module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Cone
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ElapsedGeometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.PhaseBounds.Homogeneity

/-!
# Literal mixed matrix of the conic continuation

Degree one of the actual formula gives degree zero of its mixed matrix.
Joint germ agreement at the section identifies that matrix with the original
inverse-chart matrix. No conic mixed estimate is an input. The consumer is
the spatial half-gap in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral
variable {d : ℕ}

/-- The constructed continuation in the convention of the elapsed graph
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def curriedPhase (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) :
    TwoTimePhase d := fun t s y η ↦ phase ℓ C (t, (s, (y, η)))

/-- Joint smoothness of the actual curried continuation on its domain
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffAt_curriedPhase (ℓ : Euclidean d →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ domain ℓ C.target) :
    ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        curriedPhase ℓ C p.1.1 p.1.2 p.2.1 p.2.2)
      ((q.1, q.2.1), q.2.2) := by
  exact ((contDiffOn_phase ℓ hs).contDiffAt
    ((isOpen_domain ℓ C.open_target).mem_nhds hq)).comp _
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))

/-- At every radial scale, the literal spatial mixed matrix is the original
matrix at the normalized point. All local hypotheses concern the SAME chart
from `exists_buffered_physical_pencil_kernel`.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem mixedPhaseMatrix_phase_eq_normalize (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {B : Set (ℝ × (ℝ × Euclidean d))} {η₀ : Euclidean d} {ρ : ℝ}
    (hB : IsOpen B) (hsub : localPatch B (ball η₀ ρ) ⊆ C.target)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ domain ℓ (localPatch B (ball η₀ ρ))) :
    mixedPhaseMatrix (curriedPhase ℓ C q.1 q.2.1) q.2.2.1 q.2.2.2 =
      twoTimePhaseMixed C (normalize ℓ q) := by
  let X : Set (Euclidean d) := {y | (q.1, (q.2.1, y)) ∈ B}
  let D := angularCone ℓ η₀ ρ
  have hX : IsOpen X := hB.preimage (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))
  have hx : q.2.2.1 ∈ X := hq.2.1
  have hη : q.2.2.2 ∈ D := ⟨hq.1, hq.2.2⟩
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (curriedPhase ℓ C q.1 q.2.1)) (X ×ˢ D) := by
    intro p hp
    have hm : (q.1, (q.2.1, p)) ∈ domain ℓ C.target :=
      ⟨hp.2.1, hsub ⟨hp.1, hp.2.2⟩⟩
    exact (((contDiffOn_phase ℓ hs).contDiffAt
      ((isOpen_domain ℓ C.open_target).mem_nhds hm)).comp p
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  have he := PrimitiveProfiles.mixedPhaseMatrix_dilation_eq_on hX
    (isOpen_angularCone ℓ η₀ ρ) (fun _ ha _ hη ↦ smul_mem_angularCone hη ha) hS
    (fun _ ha y _ η _ ↦ extend_smul ℓ (twoTimePhase C) (q.1, (q.2.1, (y, η))) ha)
    (inv_pos.mpr hq.1) hx hη
  rw [← he]
  apply SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq
  exact (phase_eventuallyEq_at_normalize ℓ hdiff hB isOpen_ball (convex_ball _ _) hsub hq).comp_tendsto
    ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).tendsto
      (q.2.2.1, (ℓ q.2.2.2)⁻¹ • q.2.2.2))

/-- The fixed open base patch, retaining both times and the physical position.
Its product with the frequency ball lies in the original closed buffer
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def bufferedBase (z : RootState (Euclidean d)) (ε : ℝ) : Set (ℝ × (ℝ × Euclidean d)) :=
  ball (z.1, (z.1, z.2.1)) (2 * ε)

/-- Product membership implies membership in the actual closed two-time
buffer (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem localPatch_bufferedBase_subset (z : RootState (Euclidean d)) (ε : ℝ) :
    localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε)) ⊆ closedBall (z.1, z) (2 * ε) := by
  intro q hq
  have hb : dist q.1 z.1 < 2 * ε ∧ dist q.2.1 z.1 < 2 * ε ∧
      dist q.2.2.1 z.2.1 < 2 * ε := by
    simpa only [bufferedBase, mem_ball, Prod.dist_eq, max_lt_iff] using hq.1
  simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
    ⟨hb.1.le, hb.2.1.le, hb.2.2.le, le_of_lt hq.2⟩

/-- Both times of every elapsed point remain in the fixed open base patch,
including the endpoints of the elapsed interval
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsed_mem_bufferedBase {z : RootState (Euclidean d)} {ε r : ℝ}
    (hε : 0 < ε) (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)}
    (hx : x ∈ elapsedPhysicalBox z ε) :
    (x 0, (x 0 - r, spatialPart x)) ∈ bufferedBase z ε := by
  have ht : dist (x 0) z.1 < ε := hx.1
  have hy : dist (spatialPart x) z.2.1 < ε := hx.2
  have hsource : dist (x 0 - r) z.1 < 2 * ε := by
    calc
      _ ≤ dist (x 0 - r) (x 0) + dist (x 0) z.1 := dist_triangle _ _ _
      _ = r + dist (x 0) z.1 := by simp [Real.dist_eq, abs_of_nonneg hr.1]
      _ < 2 * ε := by linarith [hr.2]
  simpa only [bufferedBase, mem_ball, Prod.dist_eq, max_lt_iff] using
    ⟨(by linarith : dist (x 0) z.1 < 2 * ε), hsource,
      (by linarith : dist (spatialPart x) z.2.1 < 2 * ε)⟩

/-- Every cone point normalizes into the very same local product patch.
Consumer: all conic elapsed geometry in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsed_mem_domain_bufferedBase (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε) (hr : r ∈ Icc 0 ε)
    {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    (x 0, (x 0 - r, (spatialPart x, η))) ∈
      domain ℓ (localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε))) :=
  ⟨hη.1, elapsed_mem_bufferedBase hε hr hx,
    ball_subset_ball (by linarith) hη.2⟩

/-- The original spatial half-gap holds on the entire positive cone, with
no radial loss. Its sole producer is the original closed-buffer estimate in
`exists_buffered_physical_pencil_kernel`.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_mixedPhaseMatrix_phase_sub_one_le (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    ‖mixedPhaseMatrix (curriedPhase ℓ C (x 0) (x 0 - r)) (spatialPart x) η - 1‖ ≤ 1 / 2 := by
  rw [mixedPhaseMatrix_phase_eq_normalize ℓ hs hdiff isOpen_ball
    ((localPatch_bufferedBase_subset z ε).trans hbuffer)
    (elapsed_mem_domain_bufferedBase ℓ hε hr hx hη)]
  exact hnear _ (elapsedPoint_mem_twoTime_buffer hε hr hx hη.2)

end JanetCartan.RegularSector.Characteristic.ConicPhase
