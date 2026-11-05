module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.ActualDomains
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.CoordinateBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.RadialFrozen
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.RadialComparison

/-!
# Actual buffered geometry for the entire radial sampling input

Construct `UniformNormalGeometry` before the current frame and every spectator,
epsilon and sampling label. The input core is exactly `radialSamplingSupport`
for the complete prescribed positive compact radial interval. The actual full
phase has global injectivity, common image buffers and a positive absolute
Jacobian gap, including at epsilon zero. The compact closure product stays in
the original phase-extension domain. Finite phase jets and zero-amplitude
`UniformNormalData` assembly are separate consumers of this construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison ContinuumRow.CanonicalConic
open MeanNormalBound.CanonicalGap RawKernel
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual full sampling geometry from primitive C⁶ closeness and frozen
incidence/transversality, for the SAME retained Hamilton family and phase.
The complete prescribed radial support is `G.D₀`, with no radial subdivision
or alteration of the kernel. Arbitrary data-radius, epsilon and physical-support
caps can be imposed before the current frame. The four final conclusions are
precisely the geometric fields of `UniformNormalData`; the extension containment
supplies its `spatial_subset` field. Finite jets and amplitude assembly remain
with the full normal-data consumer (`app:ch_seed:prop:seed-phase-charts`,
`app:ch_waves:setup:oscillatory`). -/
theorem exists_radial_uniformNormalGeometry
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax xmax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hxmax : 0 < xmax) (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ δ > (0 : ℝ), ∃ M > (0 : ℝ), ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.X = ball 0 (s / 2) ∧ G.X₀ = closedBall 0 (s / 4) ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
      closure G.D ⊆ radialSamplingSupport T z₀ ηb (2 * r) amin amax ∧
      G.X₀ ⊆ ball 0 xmax ∧
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        closure G.X ×ˢ closure G.D ⊆ fullPhaseExtensionDomain T v M) ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (m + 1)) < δ →
      ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2), ∀ ε ∈ Icc 0 G.ε₀,
        ∀ x ∈ G.X, ∀ y ∈ G.X,
          let f := averagedGradient
            (fun x w ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T w)) x y
          InjOn f G.D ∧ cthickening G.inverseBuffer (f '' G.D₀) ⊆ G.V ∧
            cthickening G.inverseBuffer (closure G.V) ⊆ f '' G.D ∧
            ∀ u ∈ G.D, G.gap ≤ |(fderiv ℝ f u).det| := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  obtain ⟨rf, hrf, A, q, hq, hfrozen⟩ :=
    exists_radial_frozen_derivative_gap T hP hz₀ hk hinc hd hamin ha
  obtain ⟨rc, hrc, hcomparison⟩ :=
    exists_actual_radial_chart_comparison T hP hz₀ ηb hamin ha
  obtain ⟨r, hr, hrcap, s₁, hs₁, hs₁r, e₁, he₁, he₁cap, δ₁, hδ₁,
    γ, hγ, M, hM, D, hD, hconv, hcompact, hDsub, ⟨bD, hbD, hDbuf⟩,
    _, hsupport, hext, hgap⟩ :=
    exists_radial_literalFullPhase_domains_and_jacobian_gap T hP hz₀ hk hinc hd
      (lt_min hrmax (lt_min hrf hrc)) hemax hxmax hamin ha
  have hrf' : r ≤ rf := hrcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrc' : r ≤ rc := hrcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  let K := radialSamplingSupport T z₀ ηb r amin amax
  have hKD : K ⊆ D := (self_subset_cthickening _).trans hDbuf
  have hcoord (u : Euclidean (m + 1))
      (hu : u ∈ radialSamplingSupport T z₀ ηb (2 * r) amin amax) :
      (adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u) ∈
        (fun a : ℝ × (ℝ × Euclidean m) ↦ radialScale a.1 a.2) ''
          (Icc amin amax ×ˢ dataBox (n := m + 1) z₀ ηb (2 * r)) := by
    rwa [radialSamplingSupport_eq_preimage] at hu
  have hDcoord (u : Euclidean (m + 1)) (hu : u ∈ D) :=
    hcoord u (hDsub (subset_closure hu))
  obtain ⟨τ, hτ, b, hb, V, hV, hVcompact, hinverse⟩ :=
    common_buffered_inverse_domains_in_literal_coordinates T
      (radialSamplingSupport_compact T z₀ ηb r amin amax) hD hKD hconv A hq
      (fun u hu ↦ (hfrozen r hr hrf' _ (hDcoord u hu)).1)
      (fun u hu ↦ (hfrozen r hr hrf' _ (hDcoord u hu)).2)
  obtain ⟨s₂, hs₂, hs₂r, e, he, hecap, δ₂, hδ₂, hcomp⟩ :=
    hcomparison r hr hrc' τ hτ e₁ he₁
  let s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  have hss₁ : s ≤ s₁ := min_le_left _ _
  have hss₂ : s ≤ s₂ := min_le_right _ _
  have hcl : closure (ball (0 : Euclidean (m + 1)) (s / 2)) = closedBall 0 (s / 2) :=
    closure_ball 0 (ne_of_gt (half_pos hs))
  have hcl₁ : closure (ball (0 : Euclidean (m + 1)) (s₁ / 2)) = closedBall 0 (s₁ / 2) :=
    closure_ball 0 (ne_of_gt (half_pos hs₁))
  obtain ⟨bX, hbX, hXbuf⟩ :=
    (isCompact_closedBall (0 : Euclidean (m + 1)) (s / 4)).exists_cthickening_subset_open isOpen_ball
      (closedBall_subset_ball (by linarith : s / 4 < s / 2))
  let G : UniformNormalGeometry (m + 1) (m + 1) := {
    dimension_pos := Nat.succ_pos _
    rank_pos := Nat.le_add_left 1 m
    X := ball 0 (s / 2)
    D := D
    X₀ := closedBall 0 (s / 4)
    D₀ := K
    V := V
    isOpen_X := isOpen_ball
    isOpen_D := hD
    convex_X := convex_ball _ _
    convex_D := hconv
    bounded_X := isBounded_ball
    bounded_D := hcompact.isBounded.subset subset_closure
    compact_X₀ := isCompact_closedBall _ _
    compact_D₀ := radialSamplingSupport_compact T z₀ ηb r amin amax
    isOpen_V := hV
    compact_closure_V := hVcompact
    ε₀ := e
    spatialBuffer := bX
    inputBuffer := bD
    inverseBuffer := b
    gap := γ
    ε₀_pos := he
    spatialBuffer_pos := hbX
    inputBuffer_pos := hbD
    inverseBuffer_pos := hb
    gap_pos := hγ
    spatial_buffer := hXbuf
    input_buffer := hDbuf }
  refine ⟨r, hr, hrcap.trans (min_le_left _ _), s, hs, hss₁.trans hs₁r,
    min δ₁ δ₂, lt_min hδ₁ hδ₂, M, hM, G, hecap.trans he₁cap,
    rfl, rfl, rfl, hDsub, ?_, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith : s / 4 ≤ s₁ / 4)).trans hsupport
  · intro v hv
    apply Subset.trans (prod_mono (t₂ := closure D) ?_ (Subset.refl _))
      (hext v (closedBall_subset_closedBall (by linarith : s / 2 ≤ s₁ / 2) hv))
    change closure (ball (0 : Euclidean (m + 1)) (s / 2)) ⊆
      closure (ball 0 (s₁ / 2))
    rw [hcl, hcl₁]
    exact closedBall_subset_closedBall (by linarith)
  intro Q hQ v hv ε hε x hx y hy
  let f := fullChartFamily (current T Q) (spatialCarrier T) (fullPhaseParameters T ε v x y)
  have hp := fullPhaseParameters_mem T hs₂ he hε
    (closedBall_subset_closedBall (by linarith : s / 2 ≤ s₂ / 2) hv)
    (closedBall_subset_closedBall (by linarith : s / 2 ≤ s₂ / 2)
      (ball_subset_closedBall hx))
    (closedBall_subset_closedBall (by linarith : s / 2 ≤ s₂ / 2)
      (ball_subset_closedBall hy))
  have hc u hu := hcomp Q (hQ.trans_le (min_le_right _ _))
    _ hp _ (hDcoord u hu)
  obtain ⟨hinj, himage, hchart⟩ := hinverse f
    (fun u hu ↦ (hc u hu).1) (fun u hu ↦ (hc u hu).2.2)
    (fun u hu ↦ (hc u (hKD hu)).2.1)
  have heq : averagedGradient
      (fun x w ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T w)) x y =
      fun u ↦ (adaptedSliceCoordinates T).equiv.symm
        (f ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))) := by
    funext u
    apply (adaptedSliceCoordinates T).equiv.injective
    exact (averagedGradient_normalizedFullPhase T Q v ε x y
      (canonicalInputCoordinates T u)).trans
        ((adaptedSliceCoordinates T).equiv.apply_symm_apply _).symm
  refine ⟨heq.symm ▸ hinj, heq.symm ▸ himage, heq.symm ▸ hchart, ?_⟩
  intro u hu
  apply hgap Q (hQ.trans_le (min_le_left _ _)) ε ⟨hε.1, hε.2.trans hecap⟩
    v (closedBall_subset_closedBall (by linarith : s / 2 ≤ s₁ / 2) hv)
    x _ y _ u (subset_closure hu)
  · rw [hcl₁]
    exact closedBall_subset_closedBall (by linarith : s / 2 ≤ s₁ / 2)
      (ball_subset_closedBall hx)
  · rw [hcl₁]
    exact closedBall_subset_closedBall (by linarith : s / 2 ≤ s₁ / 2)
      (ball_subset_closedBall hy)

end JanetCartan.Sampling.FullNormalGeometry
