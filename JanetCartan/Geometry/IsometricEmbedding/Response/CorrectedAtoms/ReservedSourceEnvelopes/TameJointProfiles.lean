module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.HomogeneousJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.JointJets

/-!
# Homogeneous one-high matrix Fourier source bounds

The literal full-strain WKB bound on the original scalar span is passed through
the finite cutoff/Fourier conversion. This retains one high scalar seminorm
and multiplies high geometry only by the fixed low scalar seminorm.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open ReservedSourceEnvelopes PrimarySourceAdmission RawPrimary NullTransport
  ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation ProjectedStressFrame
  ResponseSourceExtension ResponsePrimarySources Pseudodifferential

/-- The same joint cutoff source has homogeneous one-high scalar bounds
with fixed loss sixteen, before Fourier conversion. The original primitive
correction, scalar span and full strain are unchanged. Consumer: the source
factor in classical reconstruction of the same original response
(`app:ch_response:eq:response-graded-source`). -/
theorem exists_retained_fullStrain_homogeneous_joint_envelope_bounds
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hx : MapsTo Prod.fst (closedBall a ρ) K)
    (M : ℝ)
    (z₀ : Euclidean 3) {R Mᵣ m : ℝ} (hR : 0 < R) (hm : 0 ≤ m) (hgap : m < Mᵣ)
    {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (Γ : ℕ → ℝ) (hΓ : ∀ j, 0 < Γ j)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall a ρ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        Q.1 = projectedStress F → IsOpen Ω → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 15 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ w ∈ Ω,
          conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
              nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m, ∀ j,
          cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ j * (1 + cNorm K (j + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) →
        ∀ τ : ℝ, 0 < τ → ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
        let Kr := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
        let f := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1
        ContDiffOn ℝ ∞ f (univ ×ˢ V) ∧
          ∀ j w, w.2 ∈ V → ‖iteratedFDeriv ℝ j f w‖ ≤ C j * τ ^ 3 *
            (cNorm Kr (j + 16) (r : _ → ℝ) +
              (1 + cNorm K (j + 16) F) * cNorm Kr 16 (r : _ → ℝ)) := by
  obtain ⟨B, hB, hjets⟩ := exists_retained_fullStrain_homogeneous_joint_bounds
    hn T a hρ hK hKU hx M z₀ hR hm hgap hκmet hκnormal Γ hΓ
  obtain ⟨C, hC, hfourier⟩ := exists_fullStrain_cutoff_joint_bounds
    (N := embeddingDimension n) χ hchart hV B (fun j ↦ (hB j).le)
  refine ⟨C, hC, ?_⟩
  intro F Q row col Φ Y Ω hQ hΩ hball hΩK hphase hF hi hrank hFM hmet hnormal hframe
    hnonzero hα htransport hcorrection τ hτ r Kr f
  have hspace : ∀ w ∈ Ω, w.1 ∈ U := fun w hw ↦ hKU (hΩK hw)
  have hαr := contDiffOn_scalarAmplitude_of_mem_initialScalarSpan
    T Q F row col Φ Y hα r.property
  have hsub : chart ×ˢ V ⊆ Ω := hproduct.trans hball
  have hrawSmooth := contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs
    T Q F row col Φ Y r τ hΩ hspace hphase hF hi hrank hαr hnonzero
  let A := fun j ↦ τ ^ 3 * (cNorm Kr (j + 16) (r : _ → ℝ) +
    (1 + cNorm K (j + 16) F) * cNorm Kr 16 (r : _ → ℝ))
  have hA (j : ℕ) : 0 ≤ A j := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg hτ.le _)
      (add_nonneg (cNorm_nonneg _ _ _) (mul_nonneg
        (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)))
  have hmono : Monotone A := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ.le _)
    exact add_le_add (cNorm_mono_order (Nat.add_le_add_right hij 16))
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl
        (cNorm_mono_order (Nat.add_le_add_right hij 16))) (cNorm_nonneg _ _ _))
  have hjet (w) (hw : w ∈ chart ×ˢ V) (j : ℕ) :
      ‖iteratedFDeriv ℝ j (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) w‖ ≤ B j * A j := by
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hrawSmooth.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
      (hproduct hw) le_rfl).trans
    simpa only [A, mul_assoc] using hjets F Q row col Φ Y Ω hQ hΩ hball hΩK hphase
      hF hi hrank hFM hmet hnormal hframe hnonzero hα htransport hcorrection τ hτ j r
  obtain ⟨hregular, hbound⟩ := hfourier T Q F row col Φ Y r τ
    (fun w hw ↦ hspace w (hsub hw)) (fun w hw ↦ hphase w (hsub hw))
    hF hi hrank (hαr.mono hsub) (fun w hw ↦ hnonzero w (hsub hw)) A hA hmono hjet
  exact ⟨hregular, fun j w hw ↦ by simpa only [A, mul_assoc] using hbound j w hw⟩

end JanetCartan.CorrectedAtoms
