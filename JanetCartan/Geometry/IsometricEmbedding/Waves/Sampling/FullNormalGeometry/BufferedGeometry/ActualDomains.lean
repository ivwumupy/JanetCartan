module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.Jacobian
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.Domains

/-!
# Actual full radial domains and their determinant gap

Construct the physical and input domains, their support buffers, original
phase-extension containment, and the actual Jacobian gap before the current
frame. These are inputs to the remaining common-image and injectivity
construction for `app:ch_waves:setup:oscillatory`; this module does not claim
to construct `UniformNormalData`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison ContinuumRow.CanonicalConic
open MeanNormalBound.CanonicalGap RawKernel

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual open convex domains around the complete positive radial support,
with compact closures, positive physical/input buffers, and a determinant gap
for the literal full phase. The closure product lies in the ORIGINAL phase
extension, uniformly for every retained spectator. The physical core fits the
prescribed support ball; the radius and epsilon caps remain arbitrary.

Consumer: the domain, `spatial_subset` and `jacobian_gap` obligations of the
full sampling construction (`app:ch_seed:prop:seed-phase-charts`,
`app:ch_waves:setup:oscillatory`). Global injectivity and common image buffers
are not conclusions of this theorem. -/
theorem exists_radial_literalFullPhase_domains_and_jacobian_gap
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax xmax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hxmax : 0 < xmax) (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ), ∃ M > (0 : ℝ),
    ∃ D : Set (Euclidean (m + 1)), IsOpen D ∧ Convex ℝ D ∧ IsCompact (closure D) ∧
      closure D ⊆ radialSamplingSupport T z₀ ηb (2 * r) amin amax ∧
      (∃ b > (0 : ℝ), cthickening b (radialSamplingSupport T z₀ ηb r amin amax) ⊆ D) ∧
      (∃ b > (0 : ℝ), cthickening b (closedBall (0 : Euclidean (m + 1)) (s / 4)) ⊆
        ball 0 (s / 2)) ∧
      closedBall (0 : Euclidean (m + 1)) (s / 4) ⊆ ball 0 xmax ∧
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        closure (ball (0 : Euclidean (m + 1)) (s / 2)) ×ˢ closure D ⊆
          fullPhaseExtensionDomain T v M) ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (m + 1)) < δ →
      ∀ ε ∈ Icc 0 e, ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        ∀ x ∈ closure (ball 0 (s / 2)), ∀ y ∈ closure (ball 0 (s / 2)),
        ∀ u ∈ closure D,
          γ ≤ |(fderiv ℝ (averagedGradient
            (fun x w ↦ normalizedFullPhase T Q v ε x
              (canonicalInputCoordinates T w)) x y) u).det| := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  obtain ⟨r, hr, hrcap, s, hs, hsr, hphys, hcarrier, e, he, hecap, δ, hδ, γ, hγ, hgap⟩ :=
    exists_radial_literalFullPhase_jacobian_gap T hP hz₀ hk hinc hd
      (lt_min hrmax hxmax) hemax hamin ha
  obtain ⟨D, hDopen, hDconv, hDcomp, hDsub, hDbuffer⟩ :=
    exists_radialSamplingDomain T z₀ ηb hr hamin
  let M := amax * (‖ηb‖ + 2 * r) + 1
  have hM : 0 < M := by
    have hamax : 0 < amax := hamin.trans_le ha
    have : 0 ≤ amax * (‖ηb‖ + 2 * r) := mul_nonneg hamax.le (by positivity)
    dsimp only [M]
    linarith
  have hcl : closure (ball (0 : Euclidean (m + 1)) (s / 2)) = closedBall 0 (s / 2) :=
    closure_ball 0 (ne_of_gt (half_pos hs))
  refine ⟨r, hr, hrcap.trans (min_le_left _ _), s, hs, hsr,
    e, he, hecap, δ, hδ, γ, hγ, M, hM, D, hDopen, hDconv, hDcomp, hDsub, hDbuffer,
    (isCompact_closedBall _ _).exists_cthickening_subset_open isOpen_ball
      (closedBall_subset_ball (by linarith : s / 4 < s / 2)),
    closedBall_subset_ball (by linarith [hrcap.trans (min_le_right rmax xmax)]), ?_, ?_⟩
  · intro v hv
    rw [hcl]
    apply Subset.trans (prod_mono
      (closedBall_subset_ball (by linarith : s / 2 < T.family.radius)) hDsub)
    apply radialSamplingSupport_subset_fullPhaseExtensionDomain T hamin.le
      (by dsimp only [M]; linarith)
    intro t ht
    exact hcarrier ⟨closedBall_subset_closedBall (by linarith) hv,
      closedBall_subset_closedBall (by linarith) ht⟩
  · intro Q hQ ε hε v hv x hx y hy u hu
    rw [hcl] at hx hy
    exact hgap Q hQ ε hε v hv x hx y hy u (hDsub hu)

end JanetCartan.Sampling.FullNormalGeometry
