module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets

/-!
# Full sampling phase geometry

The actual buffered geometry and finite phase jets for the SAME retained
Hamilton family, in the original sampling coordinates. The compact input is
the entire prescribed radial interval times the normalized core. All geometry,
buffers, thresholds and jet constants precede the immersion and all sampling
labels. The zero reference amplitude is for subsequent insertion of the actual
measured polynomial by the sampling parent; no amplitude or sampling bound is
asserted here.

The fixed immersion order is `20*(n+1)+5`. Its producer is
`HistoryGeometry.exists_initialScale_for_fixed_immersion_bound` at that order,
on the SAME compact coefficient domain, with baseline condition
`displacementLoss n + bandExponent * (r + (n : ℝ)/2) + 2 < kMin`.
It supplies `cNorm KF r G + 1` for the finite histories. The geometric gaps and
projected-frame neighborhood are supplied by
`HistoryGeometry.exists_geometric_neighborhood`, using
`CurrentGeometricNeighborhood.exists_geometric_neighborhood`. The parent must
instantiate these primitive inputs for its retained family; C14 alone does not
supply the required full input jets.

Sources: `app:ch_seed:prop:seed-phase-charts`,
`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase ActualComparison
open NormalComparison MeanNormalBound.CanonicalGap RawKernel ProjectedStressFrame

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Fix the literal full sampling geometry and its frame tolerance before
all immersion budgets and geometric gaps. The source cap may therefore be
chosen for this exact tolerance before selecting the reference. Only the
phase-jet constants depend on the later map bounds; the original radial input,
phase, extension and derivative reserve are retained
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_uniform_literalFullPhaseNormalData_before_immersion_bounds
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax xmax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hxmax : 0 < xmax) (hamin : 0 < amin) (ha : amin ≤ amax)
    :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ M > (0 : ℝ),
    ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.X = ball 0 (s / 2) ∧ G.X₀ = closedBall 0 (s / 4) ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
      canonicalInputCoordinates T '' G.D₀ =
        (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
          (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r) ∧
      closure G.D ⊆ radialSamplingSupport T z₀ ηb (2 * r) amin amax ∧
      G.X₀ ⊆ ball 0 xmax ∧
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        closure G.X ×ˢ closure G.D ⊆ fullPhaseExtensionDomain T v M) ∧
    ∀ {KF : Set (Euclidean (m + 1))}, IsCompact KF → KF ⊆ U →
      (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF) →
    ∀ (B : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
          ∃ N : UniformNormalData G A,
            N.phase = (fun ε x u ↦
              normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u)) ∧
            N.amplitude = 0 ∧
            N.parameterDomain = Ioo (-2 * G.ε₀) (2 * G.ε₀) ∧
            N.extensionDomain = fullPhaseExtensionDomain T v M := by
  intro ηb
  obtain ⟨r, hr, hrcap, s, hs, hsr, δ₀, hδ₀, M, hM, G₀,
    hecap, hX, hX₀, hD₀, hD, hsupport, hext, hgeometry⟩ :=
    exists_radial_uniformNormalGeometry T hP hz₀ hk hinc hd hrmax hemax hxmax hamin ha
  let H := closedBall (spectatorCenter z₀) (s / 2) ×ˢ (closure G₀.X ×ˢ closure G₀.D)
  have hH : IsCompact H := (isCompact_closedBall _ _).prod
    (G₀.bounded_X.isCompact_closure.prod G₀.bounded_D.isCompact_closure)
  obtain ⟨ej, hej, hbudgets⟩ := exists_literalFullPhase_input_budgets_before_immersion_bounds
    T hP hM hH (fun q hq ↦ hext q.1 hq.1 hq.2)
  let G : UniformNormalGeometry (m + 1) (m + 1) :=
    { G₀ with ε₀ := min G₀.ε₀ ej, ε₀_pos := lt_min G₀.ε₀_pos hej }
  have he₀ : G.ε₀ ≤ G₀.ε₀ := min_le_left _ _
  have hej' : G.ε₀ ≤ ej := min_le_right _ _
  let δ := min δ₀ T.family.threshold
  have hδ : 0 < δ := lt_min hδ₀ T.family.threshold_pos
  refine ⟨r, hr, hrcap, s, hs, hsr, δ, hδ, min_le_right _ _, M, hM,
    G, he₀.trans hecap, hX, hX₀, hD₀, ?_, hD, hsupport, hext, ?_⟩
  · change canonicalInputCoordinates T '' G₀.D₀ = _
    rw [hD₀]
    exact canonicalInputCoordinates_image_radialSamplingSupport T _ _ _ _ _
  intro KF hKF hKU hball B γ κ hγ hκ
  obtain ⟨A, hA, hbudget⟩ := hbudgets hKF hKU hball B hγ hκ
  refine ⟨A, hA, ?_⟩
  intro F hF hi hrank hFB hmet hnormal hsmall
  have hlow := hsmall.trans_le (min_le_right δ₀ T.family.threshold)
  refine ⟨hlow, ?_⟩
  intro Q v hv
  obtain ⟨hsmooth, hjets⟩ := hbudget F hF hi hrank hFB hmet hnormal hlow
  have hsmall₀ := hsmall.trans_le (min_le_left δ₀ T.family.threshold)
  have hgeom ε (hε : ε ∈ Icc 0 G.ε₀) :=
    hgeometry Q hsmall₀ v hv ε ⟨hε.1, hε.2.trans he₀⟩
  let N : UniformNormalData G A := {
    phase := fun ε x u ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u)
    amplitude := 0
    parameterDomain := Ioo (-2 * G.ε₀) (2 * G.ε₀)
    extensionDomain := fullPhaseExtensionDomain T v M
    isOpen_parameterDomain := isOpen_Ioo
    isOpen_extensionDomain := isOpen_fullPhaseExtensionDomain T v M
    parameter_subset := by
      intro ε hε
      exact ⟨by linarith [G.ε₀_pos, hε.1], by linarith [G.ε₀_pos, hε.2]⟩
    spatial_subset := hext v hv
    phase_smooth := (hsmooth v).mono (by
      intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩)
    amplitude_smooth := contDiffOn_const
    amplitude_support := by simp
    input_jets := by
      intro ε hε w hw j hj
      simpa only [Pi.zero_apply, Function.uncurry_def, iteratedFDeriv_fun_zero,
        norm_zero, add_zero, deriv_const] using
        hjets G.ε₀ ⟨G.ε₀_pos.le, hej'⟩ ε hε v w
          ⟨hv, subset_closure hw.1, subset_closure hw.2⟩ j hj
    gradient_injective := fun ε hε x hx y hy ↦ (hgeom ε hε x hx y hy).1
    image_buffer := fun ε hε x hx y hy ↦ (hgeom ε hε x hx y hy).2.1
    chart_buffer := fun ε hε x hx y hy ↦ (hgeom ε hε x hx y hy).2.2.1
    jacobian_gap := fun ε hε x hx y hy ↦ (hgeom ε hε x hx y hy).2.2.2 }
  exact ⟨N, rfl, rfl, rfl, rfl⟩

/-- Full-dimensional normal geometry and phase-only normal data for the
literal sampling phase, including the common epsilon-zero endpoint. The
geometry covers the complete prescribed radial support, and its canonical
coordinate image is exactly the support required by
`LiteralMeanBound.exists_source_mean_bound`. The actual averaged gradient has
proved injectivity, image and chart buffers, and a determinant gap.

The finite immersion order `20*(n+1)+5` suffices for every phase input jet
through `20*(n+1)` and its epsilon derivative. Only primitive smoothness,
metric/normal gaps, this fixed immersion budget and C6 projected-frame
closeness are inputs. Constants and domains precede the immersion, spectators,
frequencies, colors and radial labels. The original coefficient extension is
retained. The zero amplitude is only a reference for the sampling parent's
actual measured amplitude insertion (`app:ch_waves:setup:oscillatory`,
`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_uniform_literalFullPhaseNormalData
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax xmax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hxmax : 0 < xmax) (hamin : 0 < amin) (ha : amin ≤ amax)
    {KF : Set (Euclidean (m + 1))} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF)
    (B : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ M > (0 : ℝ),
    ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.X = ball 0 (s / 2) ∧ G.X₀ = closedBall 0 (s / 4) ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
      canonicalInputCoordinates T '' G.D₀ =
        (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
          (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r) ∧
      closure G.D ⊆ radialSamplingSupport T z₀ ηb (2 * r) amin amax ∧
      G.X₀ ⊆ ball 0 xmax ∧
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        closure G.X ×ˢ closure G.D ⊆ fullPhaseExtensionDomain T v M) ∧
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
          ∃ N : UniformNormalData G A,
            N.phase = (fun ε x u ↦
              normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u)) ∧
            N.amplitude = 0 ∧
            N.parameterDomain = Ioo (-2 * G.ε₀) (2 * G.ε₀) ∧
            N.extensionDomain = fullPhaseExtensionDomain T v M := by
  obtain ⟨r, hr, hrcap, s, hs, hsr, δ, hδ, hδcap, M, hM, G,
    he, hX, hX₀, hD₀, hcoordinates, hD, hsupport, hext, hbudgets⟩ :=
    exists_uniform_literalFullPhaseNormalData_before_immersion_bounds T hP hz₀ hk hinc hd
      hrmax hemax hxmax hamin ha
  obtain ⟨A, hA, hnormal⟩ := hbudgets hKF hKU hball B hγ hκ
  exact ⟨r, hr, hrcap, s, hs, hsr, δ, hδ, hδcap, M, hM, G,
    he, hX, hX₀, hD₀, hcoordinates, hD, hsupport, hext, A, hA, hnormal⟩

end JanetCartan.Sampling.FullNormalGeometry
