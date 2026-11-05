module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.TameJointProfiles

/-!
# The actual raw primary's cubic source on a physical history

Paper-v2 `app:ch_response:eq:response-graded-source`: instantiate the proved
homogeneous WKB full-strain formula on the SAME real Schwartz prefix. The
original scalar, full/carrier transports, frame, and source cutoff are unchanged.
The literal source envelope has its cubic `τ³` factor, and an arbitrary fixed
natural derivative reserve is preserved. All geometric inputs are produced
from actual revised physical admissibility; no current-frame or output-source
size estimate is assumed.

The scalar's primitive transport equation and correction tame estimate are
precisely outputs of the original generic leading callback retained by
`PhysicalSeed` and its fullCorrection construction. They remain explicit here
until that SAME callback is instantiated; no new row or flow is selected.
Consumer: the normalized same-source inverse and
`CanonicalAtomRealization.fullPrimaryResponse_fixedSolver_joint_graded`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary

open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open RawPrimary NullTransport HamiltonPhase ResponsePrimarySources CorrectedAtoms
open ResponseSourceExtension LeadingWave.FullModulation PrimarySourceAdmission
open ResponseTransfer

/-- The original raw full-strain envelope is constructed and estimated on the
literal physical history, preserving `τ³` and the chosen reserve. Only the
original scalar/transport equations and their lower-level correction profile
are supplied by the same generic leading producer; no full-strain or response
profile is a premise (`main:prop:current-waves`). -/
theorem exists_history_fullStrain_reserved_profiles
    {n : ℕ} (hn : 5 ≤ n) (G : FlatReference n) {rGeom RGeom : ℝ}
    (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom) (hRGeom : RGeom < G.domain.chartRadius)
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) rGeom) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ambientStrainFrameThreshold hn / 2)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball (0 : Euclidean n) RGeom) isOpen_ball)
    (center : Euclidean n × (Euclidean 3 × Euclidean (n-1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hphysical : MapsTo Prod.fst (closedBall center ρ) (closedBall (0 : Euclidean n) rGeom))
    (z₀ : Euclidean 3) {Rscalar Mscalar mscalar : ℝ}
    (hRscalar : 0 < Rscalar) (hmscalar : 0 ≤ mscalar) (hgap : mscalar < Mscalar)
    (Γ Ar : ℕ → ℝ) (hΓ : ∀ k, 0 < Γ k) (hAr : ∀ k, 0 ≤ Ar k)
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n-1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar reserve kMin : ℕ}
    (hreserve : 16 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ)/2) + 2 < kMin) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Csource : ℕ → ℝ, (∀ k, 0 ≤ Csource k) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ K : ℝ, currentCoefficientScale R₀ j ≤ K →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) RGeom) ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
        Q.1 = projectedStress F →
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
          Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))),
        IsOpen Ω → closedBall center ρ ⊆ Ω →
        MapsTo Prod.fst Ω (closedBall (0 : Euclidean n) rGeom) →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar,
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar, ∀ w ∈ Ω,
          conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
              nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar, ∀ k,
          cNorm (closedBall center ρ) k (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ k * (1 + cNorm (closedBall (0 : Euclidean n) rGeom) (k+14) F +
              cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (Rscalar/8)) (k+14) r)) →
        ∀ τ : ℝ, 0 < τ →
        ∀ scalar : initialScalarSpan (n := n) z₀ Rscalar Mscalar mscalar,
        ∀ size : ℝ, 0 ≤ size →
          (∀ k, cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (Rscalar/8))
            (k+16) (scalar : _ → ℝ) ≤ Ar k * size * K^(k-reserve)) →
        let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          fullStrainEnvelope T Q F row col Φ Y scalar χenv τ w.2 w.1
        ContDiffOn ℝ ∞ a (univ ×ˢ V) ∧
          ∀ k w, w.2 ∈ V →
            ‖iteratedFDeriv ℝ k a w‖ ≤ Csource k * (τ^3*size) * K^(k-reserve) := by
  obtain ⟨threshold, hthreshold, _C₀, _hC₀, κ, hκ, hgeometry⟩ :=
    PhysicalGeometry.exists_cube_frame_neighborhood G hrGeom hrR hRGeom hBband
      (by omega) horder (ambientStrainFrameThreshold_pos hn) hreference
  obtain ⟨AF, hAF, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) rGeom) (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  obtain ⟨B, hB, hsource⟩ := exists_retained_fullStrain_homogeneous_joint_envelope_bounds
    hn T center hρ (isCompact_closedBall (0 : Euclidean n) rGeom)
    (closedBall_subset_ball hrR) hphysical (AF 15) z₀ hRscalar hmscalar hgap
    (κmet := (1/4 : ℝ)) (by norm_num) hκ Γ hΓ χenv hchart hV hproduct
  let Csource := fun k ↦ B k * (Ar k + (1 + AF (k+16)) * Ar 0)
  have hC k : 0 ≤ Csource k := mul_nonneg (hB k)
    (add_nonneg (hAr k) (mul_nonneg (add_nonneg zero_le_one (hAF _)) (hAr 0)))
  refine ⟨threshold, hthreshold, Csource, hC, ?_⟩
  intro R₀ hR₀ j u ell hu K hK F Q hQ row col Φ Y Ω hΩ hball hΩK hphase
    hnonzero hα htransport hcorrection τ hτ scalar size _hsize hscalar a
  obtain ⟨hi, hrank, _hC4, hmetric, hnormal, _hQsmooth, hframe⟩ := hgeometry R₀ hR₀ j u ell hu
  have hpF := hprofile R₀ (hthreshold.trans hR₀) j u ell hu _ Subset.rfl
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hscale : 1 ≤ currentCoefficientScale R₀ j :=
    one_le_currentCoefficientScale (by linarith [hthreshold.trans hR₀]) j
  have hK1 : 1 ≤ K := hscale.trans hK
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hFM : cNorm (closedBall (0 : Euclidean n) rGeom) 15 F ≤ AF 15 := by
    simpa only [show 15-rStar=0 by omega, pow_zero, mul_one] using hpF 15
  have hgeom k : cNorm (closedBall (0 : Euclidean n) rGeom) (k+16) F ≤
      AF (k+16) * K^(k-reserve) :=
    (hpF (k+16)).trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (zero_le_one.trans hscale) hK _).trans
        (pow_le_pow_right₀ hK1 (by omega : k+16-rStar ≤ k-reserve))) (hAF _))
  have hKr : closedBall (0 : Euclidean n) rGeom ⊆ ball (0 : Euclidean n) RGeom :=
    closedBall_subset_ball hrR
  obtain ⟨hregular, hbound⟩ := hsource F Q row col Φ Y Ω hQ hΩ hball hΩK hphase
    hF.contDiffOn hi hrank hFM (fun x hx ↦ hmetric x (hKr hx))
    (fun x hx ↦ hnormal x (hKr hx)) hframe hnonzero hα htransport hcorrection τ hτ scalar
  refine ⟨hregular, ?_⟩
  intro k w hw
  have hscalarLow : cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (Rscalar/8))
      16 (scalar : _ → ℝ) ≤ Ar 0 * size := by
    simpa only [zero_add, Nat.zero_sub, pow_zero, mul_one] using hscalar 0
  have hhigh : 1 + cNorm (closedBall (0 : Euclidean n) rGeom) (k+16) F ≤
      (1 + AF (k+16)) * K^(k-reserve) := by
    calc
      _ ≤ K^(k-reserve) + AF (k+16) * K^(k-reserve) :=
        add_le_add (one_le_pow₀ hK1) (hgeom k)
      _ = _ := by ring
  apply (hbound k w hw).trans
  calc
    _ ≤ B k * τ^3 * (Ar k * size * K^(k-reserve) +
        ((1+AF (k+16))*K^(k-reserve)) * (Ar 0*size)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hscalar k) (mul_le_mul hhigh hscalarLow (cNorm_nonneg _ _ _)
          (mul_nonneg (add_nonneg zero_le_one (hAF _)) (pow_nonneg hK0 _))))
        (mul_nonneg (hB k) (pow_nonneg hτ.le _))
    _ = _ := by dsimp only [Csource]; ring

end JanetCartan.PhysicalPrimary
