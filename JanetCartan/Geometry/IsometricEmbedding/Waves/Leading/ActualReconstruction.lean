module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.CanonicalReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ComplexModulation
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness

/-!
# Physical reconstruction on the actual carrier tube

The carrier's Hilbert-space gradient agrees with the coordinate differential
used by the exact modulation formula. Joint smoothness on an open transport
tube suffices for the physical slice identities, without a global extension.
The local amplitude constructor instantiates these facts with its literal
positive scalar and null column (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave
open ActualCarriers FrozenMenu CurrentFullPhase AmbientResponse ResponseTransfer

/-- Identify the coordinate differential in `app:ch_waves:eq:exact-W-amplitude`
with the gradient used by the actual characteristic construction. -/
theorem scalarDifferential_eq_gradient {n : ℕ} (f : Euclidean n → ℝ) (x : Euclidean n) :
    scalarDifferential f x = gradient f x := by
  ext i
  have h := congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
    (toDual_gradient (𝕜 := ℝ) (f := f) (x := x))
  change ⟪gradient f x, EuclideanSpace.single i 1⟫_ℝ = _ at h
  change (fderiv ℝ f x) (EuclideanSpace.single i 1) = _
  simpa only [EuclideanSpace.inner_single_right, conj_trivial, mul_one, one_mul] using h.symm

/-- The retained carrier has the prescribed affine initial value on its
original adapted section (`app:ch_waves:thm:leading`). This is the initial
value of the same full chart used by transport. -/
theorem actual_carrier_initial_value {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {y : Euclidean (n - 1)}
    (hy : T.data.adapted.embedding y ∈ ball (0 : Euclidean n) T.physicalRadius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    T.carrier Q (T.data.adapted.embedding y) z = ⟪y, T.reference.spatialPatch z⟫_ℝ := by
  simpa only [PatchQuantitativeFamily.carrier, carrierPhase, T.family.section_eq,
    LinearIsometry.coe_toContinuousLinearMap] using
      (T.currentChart Q).initial_value (T.current_section_source Q hy hz)

/-- The canonical half-strain and exact complex modulation identities on an
open actual carrier tube. The local constructor supplies the joint smooth
amplitude and the tube containment; physical slices are derived here. Both
complex quadratures use the same zero-source completion
(`app:ch_waves:eq:exact-half-strain`, `app:ch_waves:eq:exact-W-amplitude`). -/
theorem actual_carrier_reconstruction_identities {n N : ℕ} {P : Patch n}
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hΩU : Ω ⊆ U ×ˢ univ)
    (hΩphase : Ω ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {b : Euclidean n × Euclidean 3 → Euclidean n} (hb : ContDiffOn ℝ ∞ b Ω) :
    let Q := ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ w ∈ Ω,
      determinant (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      (1 / 2 : ℝ) • linearizedMetric F
          (reconstruction F (canonicalNormalCompletion F) (fun x ↦ b (x, w.2))) w.1 =
        ProjectedStressFrame.stressProjection F w.1
          (symmCovariantDeriv F (fun x ↦ b (x, w.2)) w.1) ∧
      ∀ τ : ℝ, τ ≠ 0 →
        completedVariationComplex F
          (fun x ↦ (τ : ℂ) ^ 2 •
            Complex.exp (Complex.I * (T.carrier Q x w.2 : ℂ) / (τ : ℂ)) •
              euclideanComplexInclusion (b (x, w.2))) 0 w.1 =
          Complex.exp (Complex.I * (T.carrier Q w.1 w.2 : ℂ) / (τ : ℂ)) •
            ((Complex.I * (τ : ℂ)) • euclideanComplexInclusion
              (principalNormal (canonicalNormalCompletion F w.1)
                (T.carrierGradient Q w.1 w.2) (b w)) +
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
  have hSjoint := (T.carrier_smooth hP Q).contDiffAt
    ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds (hΩphase hw))
  have hpair : ContDiffAt ℝ ∞ (fun x : Euclidean n ↦ (x, w.2)) w.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hSslice := hSjoint.comp w.1 hpair
  have hSx : DifferentiableAt ℝ (fun x ↦ T.carrier Q x w.2) w.1 :=
    hSslice.differentiableAt (by simp)
  refine ⟨T.carrier_characteristic Q (hΩphase hw).1 (hΩphase hw).2,
    reconstruction_canonical_half_strain hs (hF.mono hsU) hbs
      (fun x hx ↦ hi x (hsU hx)) (fun x hx ↦ hrank x (hsU hx)) hw, ?_⟩
  intro τ hτ
  simpa only [scalarDifferential_eq_gradient, PatchQuantitativeFamily.carrierGradient, Q] using
    completedVariationComplex_zero_exact_amplitude F hτ hSx hbx

end JanetCartan.LeadingWave
