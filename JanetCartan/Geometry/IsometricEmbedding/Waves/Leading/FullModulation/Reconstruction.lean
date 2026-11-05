module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.CanonicalReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ComplexModulation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness

/-!
# Reconstruction for the actual full modulation phase

The physical slice argument for `app:ch_waves:eq:exact-half-strain` and
`app:ch_waves:eq:exact-W-amplitude` keeps the independent carrier label and
full covector. The actual local constructor supplies the smooth amplitude on
its open flow tube. Both complex quadratures use the canonical zero-source
completion, with no global extension of the amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase AmbientResponse ResponseTransfer

/-- The canonical half-strain and exact complex modulation identities on an
open full modulation tube. The local constructor supplies the joint smooth
amplitude and the tube containment; physical slices are derived here. Both
complex quadratures use the same zero-source completion
(`app:ch_waves:eq:exact-half-strain`, `app:ch_waves:eq:exact-W-amplitude`). -/
theorem reconstruction_identities {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hΩ : IsOpen Ω)
    (hΩU : Ω ⊆ U ×ˢ univ)
    (hΩphase : Ω ⊆ domain T)
    {b : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean n} (hb : ContDiffOn ℝ ∞ b Ω) :
    let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ w ∈ Ω,
      determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
      (1 / 2 : ℝ) • linearizedMetric F
          (reconstruction F (canonicalNormalCompletion F) (fun x ↦ b (x, w.2))) w.1 =
        ProjectedStressFrame.stressProjection F w.1
          (symmCovariantDeriv F (fun x ↦ b (x, w.2)) w.1) ∧
      ∀ τ : ℝ, τ ≠ 0 →
        completedVariationComplex F
          (fun x ↦ (τ : ℂ) ^ 2 •
            Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ : ℂ)) •
              euclideanComplexInclusion (b (x, w.2))) 0 w.1 =
          Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
            ((Complex.I * (τ : ℂ)) • euclideanComplexInclusion
              (principalNormal (canonicalNormalCompletion F w.1)
                (phaseGradient T Q w.1 w.2.2) (b w)) +
            (τ : ℂ) ^ 2 • euclideanComplexInclusion
              (reconstruction F (canonicalNormalCompletion F) (fun x ↦ b (x, w.2)) w.1)) := by
  let Q := (⟨ProjectedStressFrame.projectedStress F,
    contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  dsimp only
  intro w hw
  let s := (fun x : Euclidean n ↦ (x, w.2)) ⁻¹' Ω
  have hs : IsOpen s := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hsU : s ⊆ U := fun x hx ↦ (hΩU hx).1
  have hbs : ContDiffOn ℝ ∞ (fun x ↦ b (x, w.2)) s :=
    hb.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx ↦ hx)
  have hbx : DifferentiableAt ℝ (fun x ↦ b (x, w.2)) w.1 :=
    (hbs.contDiffAt (hs.mem_nhds hw)).differentiableAt (by simp)
  have hphase0 : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Euclidean (n - 1) ↦ phase T Q w.1 w.2)
      (phaseDomain T) :=
    (phase_smooth T Q).mono (ball_subset_ball
      (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius))
  have hphase : ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phase T Q w.1 w.2.2)
      (domain T) :=
    hphase0.comp
        physicalCovectorProjection.contDiff.contDiffOn (fun _ hw ↦ hw)
  have hSjoint : ContDiffAt ℝ ∞
      (fun v : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phase T Q v.1 v.2.2) w :=
    hphase.contDiffAt ((isOpen_domain T).mem_nhds (hΩphase hw))
  have hpair : ContDiffAt ℝ ∞ (fun x : Euclidean n ↦ (x, w.2)) w.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hSslice : ContDiffAt ℝ ∞ (fun x ↦ phase T Q x w.2.2) w.1 :=
    ContDiffAt.comp (g := fun v : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      phase T Q v.1 v.2.2) (f := fun x : Euclidean n ↦ (x, w.2)) w.1 hSjoint hpair
  have hSx : DifferentiableAt ℝ (fun x ↦ phase T Q x w.2.2) w.1 :=
    hSslice.differentiableAt (by simp)
  refine ⟨phase_characteristic T Q (w := (w.1, w.2.2)) (hΩphase hw),
    reconstruction_canonical_half_strain hs (hF.mono hsU) hbs
      (fun x hx ↦ hi x (hsU hx)) (fun x hx ↦ hrank x (hsU hx)) hw, ?_⟩
  intro τ hτ
  simpa only [scalarDifferential_eq_gradient, phaseGradient, Q] using
    completedVariationComplex_zero_exact_amplitude F hτ hSx hbx

end JanetCartan.LeadingWave.FullModulation
