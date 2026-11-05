module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain

/-!
# Cubic strain constants before retained geometry

The retained-cell producer supplies its fixed physical containment only after
its immersion argument. This preserves that quantifier order while reusing the
actual ambient reconstruction estimate. The finite raw-family assembly supplies
the containment, transport equation and reserve-fourteen correction budget.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary
open NullTransport ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation ProjectedStressFrame

/-- Choose cubic strain constants before the retained geometric conclusions.
Consumer: `exists_finite_retained_raw_primary_family`; source:
`app:ch_waves:eq:WKB-strain`. No strain estimate is assumed. -/
theorem exists_fullPrimaryStrain_grade_on_retained_workingBall
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (M : ℝ)
    {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j k, 0 < C j k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Kr : Set (Euclidean (n - 1) × Euclidean 3))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        MapsTo Prod.fst (closedBall a ρ) K →
        Q.1 = projectedStress F → IsOpen Ω → closedBall a ρ ⊆ Ω →
        MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
            nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ m, cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r)) →
        ∀ (RF Rr rpar : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
          ∀ j k, k ≤ rpar → ∀ w ∈ closedBall a ρ, ∀ τ : ℝ, 0 < τ →
            ‖iteratedFDeriv ℝ (j + k)
              (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) w‖ ≤
              C j k * τ^3 * L^j := by
  classical
  by_cases hx : MapsTo Prod.fst (closedBall a ρ) K
  · obtain ⟨C, hC, hbound⟩ := exists_fullPrimaryStrain_joint_grade hn T a hρ hK hKU hx M
      hκmet hκnormal AF Ar Γ hAF hAr hΓ
    exact ⟨C, hC, fun F Q row col Φ Y r Kr Ω _ ↦ hbound F Q row col Φ Y r Kr Ω⟩
  · refine ⟨fun _ _ ↦ 1, fun _ _ ↦ zero_lt_one, ?_⟩
    intro F Q row col Φ Y r Kr Ω hgeometry
    exact (hx hgeometry).elim

end JanetCartan.RawPrimary
