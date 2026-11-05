module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets.JointBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets.Restriction

/-!
# Uniform jets of the literal full sampling phase

The endpoint supplies the phase terms of `UniformNormalData.input_jets` for
`n = m+1`, on any fixed compact set of spectator/physical/input triples in the
published full extension domain. All constants precede the immersion, spectator,
frequency and colors. The retained `PatchQuantitativeFamily T` is unchanged.

The fixed immersion order is `20*(n+1)+5`, not C14. Its finite-history producer
is `HistoryGeometry.exists_initialScale_for_fixed_immersion_bound` at exactly
`r = 20*(n+1)+5`, with the SAME compact coefficient domain and baseline condition
`displacementLoss n + bandExponent * (r + (n : ℝ)/2) + 2 < kMin`.
It supplies the budget `cNorm KF r G + 1`. The parent retains the construction
of `H`, the geometric gaps and the final zero-amplitude normal data.

Sources: `app:ch_waves:setup:oscillatory`,
`app:ch_seed:prop:seed-phase-charts`, `app:ch_seed:eq:seed-phase-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawKernel MeanNormalBound.CanonicalGap ProjectedStressFrame

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Choose the full-input epsilon cap before the immersion budget and
geometric gaps, retaining all literal input jets and the ordinary epsilon
derivative. This order allows `exists_uniform_literalFullPhaseNormalData` to
fix its geometry before the source scale (`app:ch_seed:eq:seed-phase-tame`,
`app:ch_waves:setup:oscillatory`). -/
theorem exists_literalFullPhase_input_budgets_before_immersion_bounds {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H)
    (hHM : ∀ q ∈ H, q.2 ∈ fullPhaseExtensionDomain T q.1 M)
    : ∃ e > (0 : ℝ),
    ∀ {KF : Set (Euclidean (m + 1))}, IsCompact KF → KF ⊆ U →
      (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF) →
    ∀ (B : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (∀ v : Euclidean 2, ContDiffOn ℝ ∞
          (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
            normalizedFullPhase T Q v q.1 q.2.1 (canonicalInputCoordinates T q.2.2))
          (Ioo (-2 * e) (2 * e) ×ˢ fullPhaseExtensionDomain T v M)) ∧
        ∀ e' ∈ Icc (0 : ℝ) e, ∀ ε ∈ Icc (0 : ℝ) e',
          ∀ v : Euclidean 2, ∀ w : Euclidean (m + 1) × Euclidean (m + 1),
          (v, w) ∈ H → ∀ k ≤ 20 * ((m + 1) + 1),
            ‖iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
                normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) w‖ +
              ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
                normalizedFullPhase T Q v t x (canonicalInputCoordinates T u))) w) ε‖ ≤ A k := by
  obtain ⟨e, he, hbudgets⟩ := PhaseJets.exists_literalJoint_budgets_before_immersion_bounds
    T hP hM hH (fun q hq ↦ hHM q hq)
  refine ⟨e, he, ?_⟩
  intro KF hKF hKU hball B γ κ hγ hκ
  obtain ⟨A, hA, hb⟩ := hbudgets hKF hKU hball B hγ hκ
  refine ⟨fun k ↦ A k + A (k + 1),
    fun k ↦ add_pos (hA k) (hA (k + 1)), ?_⟩
  intro F hF hi hrank hFB hmet hnormal hlow Q
  obtain ⟨hs, hj⟩ := hb F hF hi hrank hFB hmet hnormal hlow
  refine ⟨fun v ↦ hs.comp
    (f := fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦ (q.1, v, q.2))
    (by fun_prop) (fun q hq ↦ hq), ?_⟩
  intro e' he' ε hε v w hw k hk
  have hεe : ε ∈ Icc (-e) e := ⟨by linarith [hε.1], hε.2.trans he'.2⟩
  have hεo : ε ∈ Ioo (-(2 * e)) (2 * e) :=
    ⟨by linarith [hεe.1], by linarith [hεe.2]⟩
  have hs' : ContDiffOn ℝ ∞ (PhaseJets.literalJoint T Q)
      (Ioo (-(2 * e)) (2 * e) ×ˢ PhaseJets.tripleDomain T M) := by
    simpa only [neg_mul] using hs
  exact (PhaseJets.inputJets_le_joint T Q hs' hεo (hHM (v, w) hw) k).trans
    (add_le_add (hj (ε, v, w) ⟨hεe, hw⟩ k (by omega))
      (hj (ε, v, w) ⟨hεe, hw⟩ (k + 1) (by omega)))

/-- Uniform finite jets of the SAME literal full phase for the actual
projected stress. The constants and epsilon cap precede `F` and all spectators.
The bound includes the ordinary epsilon derivative at zero and the upper
endpoint, and survives every further cap restriction. The only high input is
the fixed immersion norm at `20*(n+1)+5`; no phase jets or normal data are
assumed. Consumer: `UniformNormalData.input_jets` in
`app:ch_waves:setup:oscillatory`; source `app:ch_seed:eq:seed-phase-tame`. -/
theorem exists_literalFullPhase_input_budgets {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H)
    (hHM : ∀ q ∈ H, q.2 ∈ fullPhaseExtensionDomain T q.1 M)
    {KF : Set (Euclidean (m + 1))} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF)
    (B : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ e > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (∀ v : Euclidean 2, ContDiffOn ℝ ∞
          (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
            normalizedFullPhase T Q v q.1 q.2.1 (canonicalInputCoordinates T q.2.2))
          (Ioo (-2 * e) (2 * e) ×ˢ fullPhaseExtensionDomain T v M)) ∧
        ∀ e' ∈ Icc (0 : ℝ) e, ∀ ε ∈ Icc (0 : ℝ) e',
          ∀ v : Euclidean 2, ∀ w : Euclidean (m + 1) × Euclidean (m + 1),
          (v, w) ∈ H → ∀ k ≤ 20 * ((m + 1) + 1),
            ‖iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
                normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) w‖ +
              ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (fun x u ↦
                normalizedFullPhase T Q v t x (canonicalInputCoordinates T u))) w) ε‖ ≤ A k := by
  obtain ⟨e, he, hbudgets⟩ :=
    exists_literalFullPhase_input_budgets_before_immersion_bounds T hP hM hH hHM
  obtain ⟨A, hA, hbound⟩ := hbudgets hKF hKU hball B hγ hκ
  exact ⟨e, he, A, hA, hbound⟩

end JanetCartan.Sampling.FullNormalGeometry
