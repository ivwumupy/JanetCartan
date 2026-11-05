module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseBuffers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseHomogeneity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry

/-!
# Elapsed graph geometry on the actual local phase buffer

Instantiate the triangular and averaged-gradient deductions with the same
constructed two-time phase. The physical box is convex, every elapsed point
lies in its closed two-time buffer, and the whole lifted spatial-frequency
chart has an injective averaged gradient and a positive Jacobian gap.
These are local buffered conclusions, not yet conic all-frequency symbol
bounds or estimates uniform over a coefficient family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic
open FourierIntegral EvolutionIntegral NormalComparison WholeImageGeometry
variable {d : ℕ}

/-- The fixed convex physical box used by the elapsed-time phase.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedPhysicalBox (z : RootState (Euclidean d)) (ε : ℝ) : Set (Euclidean (d + 1)) :=
  {x | x 0 ∈ ball z.1 ε ∧ spatialPart x ∈ ball z.2.1 ε}
/-- The elapsed physical box is open.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem isOpen_elapsedPhysicalBox (z : RootState (Euclidean d)) (ε : ℝ) : IsOpen (elapsedPhysicalBox z ε) :=
  (isOpen_ball.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous).inter
    (isOpen_ball.preimage spatialPartCLM.continuous)
/-- Full physical segments stay in the elapsed box.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem convex_elapsedPhysicalBox (z : RootState (Euclidean d)) (ε : ℝ) : Convex ℝ (elapsedPhysicalBox z ε) :=
  ((convex_ball z.1 ε).linear_preimage
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).toLinearMap).inter
      ((convex_ball z.2.1 ε).linear_preimage spatialPartCLM.toLinearMap)
/-- One closed two-time buffer contains the whole elapsed slab, including
both endpoints. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedPoint_mem_twoTime_buffer {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ ball z.2.2 ε) :
    (x 0, (x 0 - r, (spatialPart x, η))) ∈ closedBall (z.1, z) (2 * ε) := by
  have ht : dist (x 0) z.1 < ε := hx.1
  have hy : dist (spatialPart x) z.2.1 < ε := hx.2
  have hη' : dist η z.2.2 < ε := hη
  have hs : dist (x 0 - r) z.1 ≤ 2 * ε := by
    calc
      _ ≤ dist (x 0 - r) (x 0) + dist (x 0) z.1 := dist_triangle _ _ _
      _ = r + dist (x 0) z.1 := by simp [Real.dist_eq, abs_of_nonneg hr.1]
      _ ≤ 2 * ε := by linarith [hr.2]
  simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
    And.intro (by linarith : dist (x 0) z.1 ≤ 2 * ε)
      (And.intro hs (And.intro (by linarith : dist (spatialPart x) z.2.1 ≤ 2 * ε)
        (by linarith : dist η z.2.2 ≤ 2 * ε)))

/-- The actual chart's smoothness supplies the exact joint smoothness input
of the elapsed graph theorem at every elapsed time in the fixed slab.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem contDiffAt_curriedTwoTimePhase_elapsed
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ ball z.2.2 ε) :
    ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        curriedTwoTimePhase C p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)) := by
  have hq := hbuffer (elapsedPoint_mem_twoTime_buffer hε hr hx hη)
  exact (hs.contDiffAt (C.open_target.mem_nhds hq)).comp
    (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ (p.1.1, (p.1.2, p.2)))
    ((x 0, x 0 - r), (spatialPart x, η))
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))

/-- Whole-image averaged-gradient injectivity and a positive determinant gap
for the actual elapsed phase follow from its constructed spatial buffer. The
constant depends only on the spatial dimension and precedes the chart and
slab. No inverse-map domain or limiting normal bound is assumed.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_twoTimePhase_elapsed_averaged_geometry (d : ℕ) :
    ∃ κ > 0, ∀ (C : OpenPartialHomeomorph
      (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
      (z : RootState (Euclidean d)) (ε : ℝ), 0 < ε →
      closedBall (z.1, z) (2 * ε) ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
      ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε, ∀ y ∈ elapsedPhysicalBox z ε,
        InjOn (averagedGradient (elapsedPhase (curriedTwoTimePhase C) r) x y)
          (spatialPart ⁻¹' ball z.2.2 ε) ∧
        ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ ball z.2.2 ε →
          κ ≤ |(averagedJacobian (elapsedPhase (curriedTwoTimePhase C) r) x y ξ).det| := by
  obtain ⟨κ, hκ, hg⟩ := exists_elapsedPhase_averaged_geometry d
  refine ⟨κ, hκ, ?_⟩
  intro C z ε hε hbuffer hs hnear
  apply hg (curriedTwoTimePhase C) ε (elapsedPhysicalBox z ε) (ball z.2.2 ε)
    (isOpen_elapsedPhysicalBox z ε) isOpen_ball (convex_elapsedPhysicalBox z ε) (convex_ball _ _)
  · intro r hr x hx η hη
    exact contDiffAt_curriedTwoTimePhase_elapsed C hε hbuffer hs hr hx hη
  · intro r hr x hx η hη
    exact hnear (x 0, (x 0 - r, (spatialPart x, η)))
      (elapsedPoint_mem_twoTime_buffer hε hr hx hη)

/-- The same closed buffer supplies the exact supported mixed-invertibility
premise of integer forward and literal-adjoint graph bounds. Source:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem curriedTwoTimePhase_elapsed_supportedMixedInvertibility
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2)
    (hr : r ∈ Icc 0 ε) (Y : Set (Euclidean (d + 1))) :
    SupportedMixedInvertibility (elapsedPhase (curriedTwoTimePhase C) r)
      ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' ball z.2.2 ε)) := by
  apply elapsedPhase_supportedMixedInvertibility _ r isOpen_ball
  · intro x hx η hη
    exact contDiffAt_curriedTwoTimePhase_elapsed C hε hbuffer hs hr hx hη
  · intro x hx η hη
    exact hnear (x 0, (x 0 - r, (spatialPart x, η)))
      (elapsedPoint_mem_twoTime_buffer hε hr hx hη)

/-- The local radial germ is produced by the full Hamilton phase differential,
then transferred to the exact supported homogeneity input of the existing
integer graph calculus. Neither global conic homogeneity nor a phase extension
is assumed. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem curriedTwoTimePhase_elapsed_supportedPhaseHomogeneity
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hr : r ∈ Icc 0 ε) (Y : Set (Euclidean (d + 1))) :
    SupportedPhaseHomogeneity (elapsedPhase (curriedTwoTimePhase C) r)
      ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' ball z.2.2 ε)) := by
  intro p hp _
  have hq := hbuffer (elapsedPoint_mem_twoTime_buffer hε hr hp.1.1 hp.2)
  have hc : Continuous (fun x : Euclidean (d + 1) ↦
      (x 0, (x 0 - r, (spatialPart x, spatialPart p.2)))) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.prodMk
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.sub
        continuous_const).prodMk (spatialPartCLM.continuous.prodMk continuous_const))
  filter_upwards [twoTimePhase_radial_germ hdiff hq] with a ha
  filter_upwards [ha.comp_tendsto (hc.tendsto p.1.1)] with x hx
  have hsp : spatialPart (a • p.2) = a • spatialPart p.2 := spatialPartCLM.map_smul a p.2
  dsimp only [Function.comp_apply] at hx
  simp only [elapsedPhase, curriedTwoTimePhase, hsp, PiLp.smul_apply, smul_eq_mul, hx]
  ring

end JanetCartan.RegularSector.Characteristic
