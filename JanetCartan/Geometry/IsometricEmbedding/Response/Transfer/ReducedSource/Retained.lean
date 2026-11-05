module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.MixedL2
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Retained

/-!
# Mixed L² profiles of the original retained reduced source

Apply the literal cubic strain and projected-stress producers to the same
retained geometry and full independent source parameters. The original
source cutoff, reduced cutoff and strain extension are kept in the formula.
This constructs the datum profile for both characteristic and elliptic
response envelopes (`app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.ReducedSource
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame ResponsePrimarySources
open ResponseSourceExtension Sampling.BackgroundModulation

/-- Apply the actual cubic strain and projected-stress producers on the SAME
retained cell. The resulting full mixed L² jets retain the original source
cutoff, reduced cutoff, full strain extension and factor one half. All
constants precede the immersion, scalar, frequency and histories; the single
reserve is sixteen (`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_retained_reducedSource_mixedL2_profiles
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (center : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : MapsTo Prod.fst (closedBall center ρ) K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    (χsrc η : Euclidean n → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc) (hη : ContDiff ℝ ∞ η)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall center ρ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
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
        Q.1 = projectedStress F → IsOpen Ω → closedBall center ρ ⊆ Ω →
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
        (∀ m, cNorm (closedBall center ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr → ∀ τ : ℝ, 0 < τ →
          let b := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q.1 w.1)
              (fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1)))
          ContDiffOn ℝ ∞ b (univ ×ˢ V) ∧
            ∀ c ∈ V, ∀ j, ∃ hm : MemLp (fun x : Euclidean n ↦ iteratedFDeriv ℝ j b (x,c)) 2 volume,
              ‖hm.toLp (fun x : Euclidean n ↦ iteratedFDeriv ℝ j b (x,c))‖ ≤ C j * τ^3 * L^j := by
  classical
  have hphysical : closedBall center.1 ρ ⊆ K := by
    intro x hx
    apply hball (x := (x,center.2))
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx
  obtain ⟨B, hB, hraw⟩ := exists_fullPrimaryStrain_grade_on_retained_workingBall
    hn T center hρ hK hKU M hκmet hκnormal AF Ar Γ hAF hAr hΓ
  obtain ⟨AQ, hAQ, hstress⟩ := exists_projectedStress_jet_budgets (N := embeddingDimension n)
    hU center.1 hρ hK hKU hphysical hκmet hκnormal AF hAF
  obtain ⟨C, hC, hsource⟩ := exists_cutoff_reducedSource_mixedL2_constants (d := n-1)
    χ hchart (χsrc * η) (hχsrc.mul hη) AQ (fun j ↦ B j 0) (fun j ↦ (hAQ j).le)
    (fun j ↦ (hB j 0).le)
  refine ⟨C, hC, ?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hα hn' ht hcorr RF Rr L hpF hpr hL hRF hRr τ hτ b
  by_cases hVne : V.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hVne
    have hchartK : chart ⊆ K := fun x hx ↦ hball (x := (x,c₀)) (hproduct ⟨hx,hc₀⟩)
    have hsub : chart ×ˢ V ⊆ Ω := hproduct.trans hballΩ
    have hrawSmooth := contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
      hΩ (fun w hw ↦ hKU (hΩK hw)) hphase hF hi hrank hα hn'
    have hqj (x) (hx : x ∈ tsupport χ.toFun) (j) :
        ‖iteratedFDeriv ℝ j Q.1 x‖ ≤ AQ j * L^j := by
      rw [hQ]
      have hxball : x ∈ closedBall center.1 ρ := by
        have h := hproduct (a := (x,c₀)) ⟨χ.support_chart hx,hc₀⟩
        change max (dist x center.1) (dist c₀ center.2) ≤ ρ at h
        exact le_trans (le_max_left _ _) h
      simpa only [Nat.sub_zero] using
        hstress F hF hi hrank hmet hnormal RF 0 L hL (by omega) (by omega) hpF x hxball j
    have haj (w) (hw : w ∈ chart ×ˢ V) (j) :
        ‖iteratedFDeriv ℝ j (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) w‖ ≤ B j 0 * τ^3 * L^j := by
      simpa only [Nat.add_zero] using hraw F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ
        hΩK hphase hF hi hrank hFM hmet hnormal hframe hα hn' ht hcorr RF Rr 0 L
        hpF hpr hL hRF hRr j 0 le_rfl w (hproduct hw) τ hτ
    have hs := hsource V hV Q.1 (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) (τ^3) L
      (by positivity) hL (Q.property.1.mono (hchartK.trans hKU)) (hrawSmooth.mono hsub) hqj haj
    have he : (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ χ.toFun w.1 •
        ((χsrc * η) w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q.1 w.1)
          (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w)))) = b := by
      funext w
      dsimp only [b]
      rw [fullStrainEnvelope_eq, LinearMapClass.map_smul_of_tower]
      simp only [Pi.mul_apply, smul_smul]
      congr 1
      ring
    simpa only [he] using hs
  · have he : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hVne
    simp [he]

end JanetCartan.ResponseTransfer.ReducedSource
