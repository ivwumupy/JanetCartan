module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.SupportedChart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportBuffers

/-!
# Compact radial labels for the full sampling phase

Radial dilation changes epsilon to `ε a`; it does not turn the full phase into
transport. The positive gap survives every label in a fixed positive compact
radial interval, with the same incidence and spectator coordinates. This is the
normalized-band input to `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound.CanonicalGap
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison
open ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Dilate only the covector in the original input, retaining the distinguished
incidence coordinate (`app:ch_waves:eq:phase-quotient`). -/
def radialInput (a : ℝ) (u : Euclidean n) : Euclidean n :=
  (adaptedSliceCoordinates T).equiv.symm
    (radialScale a ((adaptedSliceCoordinates T).equiv u))

/-- The existing compact angular support fits the SAME covector-centered
data core at the frozen magnitude. This is the support producer used before
applying radial dilation, with incidence unchanged
(`app:ch_seed:eq:seed-normal-annulus`). -/
theorem closedDirections_mem_normalizedInputCore {z₀ : Euclidean 3}
    {ηb θ : Euclidean (n - 1)} (hηb : ηb ≠ 0) {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : t ∈ closedBall (z₀ 0) r)
    (hθ : θ ∈ closedDirections ηb r) :
    (adaptedSliceCoordinates T).equiv.symm (t, ‖ηb‖ • θ) ∈
      normalizedInputCore T z₀ ηb r := by
  change (adaptedSliceCoordinates T).equiv
    ((adaptedSliceCoordinates T).equiv.symm (t, ‖ηb‖ • θ)) ∈ dataBox z₀ ηb r
  rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨ht, ?_⟩
  rw [mem_closedBall]
  conv_lhs => arg 2; rw [← NormedSpace.norm_smul_normalize ηb]
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hdist := mem_closedBall.mp hθ.2
  have hw := (angularWidth_spec hηb hr).2.2.1
  have hn := norm_pos_iff.mpr hηb
  have hmul := mul_le_mul_of_nonneg_left hdist hn.le
  nlinarith

/-- The full compact radial/input support is constructed as the image of the
original compact core and a closed radial interval, not an unrestricted shell
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem radialInput_image_compact (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) (r amin amax : ℝ) :
    IsCompact ((fun q : ℝ × Euclidean n ↦ radialInput T q.1 q.2) ''
      (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r)) := by
  apply (isCompact_Icc.prod (normalizedInputCore_compact T z₀ ηb r)).image
  unfold radialInput radialScale
  fun_prop

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Exact radial rescaling of the SAME full integral quotient, also at zero
epsilon. The shifted parameter is `ε a`, with unchanged spectators
(`app:ch_waves:eq:phase-quotient`). -/
theorem normalizedFullPhase_radialInput (v : Euclidean 2) (ε a : ℝ)
    (x u : Euclidean n) :
    normalizedFullPhase T Q v ε x (radialInput T a u) =
      a * normalizedFullPhase T Q v (ε * a) x u := by
  simp only [normalizedFullPhase, radialInput, ContinuousLinearEquiv.apply_symm_apply,
    radialScale, modulation, phaseShiftQuotient, smul_smul, mul_assoc, inner_smul_right]
  rw [intervalIntegral.integral_const_mul]

/-- The averaged gradient has the same exact radial law. Consequently a
compact positive radial interval preserves the annular lower bound; no
homogeneity of the nonlinear Hamilton phase is assumed
(`app:ch_seed:eq:seed-normal-annulus`). -/
theorem averagedGradient_radialInput (v : Euclidean 2) (ε a : ℝ)
    (x y u : Euclidean n) :
    averagedGradient (normalizedFullPhase T Q v ε) x y (radialInput T a u) =
      a • averagedGradient (normalizedFullPhase T Q v (ε * a)) x y u := by
  have hphase : (fun z ↦ normalizedFullPhase T Q v ε z (radialInput T a u)) =
      a • (fun z ↦ normalizedFullPhase T Q v (ε * a) z u) := by
    funext z
    exact normalizedFullPhase_radialInput T Q v ε a z u
  unfold averagedGradient averagedPhaseDifferential
  rw [hphase, fderiv_const_smul_field]
  simp only [Pi.smul_apply, intervalIntegral.integral_smul, map_smul]

omit Q in
/-- The actual canonical gap covers every admissible positive radial label
in a fixed compact interval. The constants precede the current frame, radial
label and both physical positions; epsilon is capped by `e / amax` so the SAME
buffered chart is used at the actual shifted value `ε a`
(`app:ch_seed:eq:seed-normal-annulus`). -/
theorem exists_radial_normalizedFullPhase_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
    ∀ ε ∈ Icc 0 e, ∀ a ∈ Icc amin amax,
      ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
      ∀ x ∈ closedBall 0 (s / 2), ∀ y ∈ closedBall 0 (s / 2),
      ∀ u ∈ normalizedInputCore T z₀ ηb (2 * r),
        γ ≤ ‖averagedGradient (normalizedFullPhase T Q v ε) x y (radialInput T a u)‖ := by
  have hamax : 0 < amax := hamin.trans_le ha
  obtain ⟨r, hr, hrcap, s, hs, hsr, _, _, e, he, hecap, δ, hδ, γ, hγ,
    cF, _, bF, _, V, L, _, _, _, _, hall⟩ :=
    exists_buffered_normalizedFullPhase_gap T hP hz₀ hk hinc hd hrmax
      (mul_pos hemax hamax)
  refine ⟨r, hr, hrcap, s, hs, hsr, e / amax, div_pos he hamax,
    (div_le_iff₀ hamax).mpr hecap, δ, hδ, amin * γ, mul_pos hamin hγ, ?_⟩
  intro Q hQ ε hε a ha' v hv x hx y hy u hu
  have hapos : 0 < a := hamin.trans_le ha'.1
  have hεa : ε * a ∈ Icc 0 e :=
    ⟨mul_nonneg hε.1 hapos.le,
      (mul_le_mul_of_nonneg_left ha'.2 hε.1).trans
        ((le_div_iff₀ hamax).mp hε.2)⟩
  rw [averagedGradient_radialInput, norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
  exact mul_le_mul ha'.1 ((hall Q hQ).2 _ hεa v hv x hx y hy u hu) hγ.le hapos.le

end JanetCartan.Sampling.MeanNormalBound.CanonicalGap
