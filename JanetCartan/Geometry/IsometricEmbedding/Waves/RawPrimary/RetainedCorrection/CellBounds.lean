module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LeadingInputs

/-!
# Correction on the original retained working balls

The primitive inputs below are conclusions of
`CurrentCoefficientProfiles.exists_finite_retained_leading_family_before_geometry_with_carrier_data_and_working_balls`
and its history variant. In particular, the doubled covering ball lies in the
original scalar-estimate cylinder image. No new cell, index or flow is chosen.
The geometric facts that the producer exports after the immersion are independent
of that immersion; a case split on those facts keeps the constants before it.

Consumer: the same-family finite assembly and the common initialized-history
application of `app:ch_waves:thm:individual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.RetainedCorrection
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open LeadingWave.FullModulation ProjectedStressFrame

/-- Apply the retained scalar estimate to the original doubled working ball.
Every premise is a primitive retained-leading conclusion or an original
immersion/scalar low budget. The correction, cancellation and reserve-fourteen
estimate are derived for the SAME selected indices and flows. In particular,
the covering radius `σ` is not reduced (`app:ch_waves:eq:primary-algebraic-correction`,
`app:ch_waves:eq:WKB-grading`). -/
theorem exists_retained_cell_correction_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hballK : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (row col : Fin n)
    {ρ R τ σ : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hσ : 0 < σ)
    (M Mᵣ : ℝ) (B : ℕ → ℝ) {κmet κnormal b : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hb : 0 < b)
    (hworking : let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
      closedBall a (2 * σ) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ / 2) (τ / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 64)))
    (hcoeff : let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
      closedBall a (2 * σ) ⊆ closedBall a ρ) :
    ∃ Γ : ℕ → ℝ, (∀ k, 0 < Γ k) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
        let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
        let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
          (adaptedCoordinates T.data.adapted)
        let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
        closedBall a (2 * ρ) ⊆ domain T →
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) →
        ∀ (D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))))
          (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
            Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))),
          IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
          C ⁻¹' D ⊆ ball a (2 * ρ) →
          (∀ w ∈ C ⁻¹' D, b ≤ ‖nullvector T Q col w‖) →
          ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          let Kr := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
          cNorm Kr 14 r ≤ Mᵣ →
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) (C ⁻¹' D) →
          (∀ w ∈ C ⁻¹' D,
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
              nullvector T Q col (x, w.2)) w.1 = 0) →
          (∀ k, cNorm W k (scalarAmplitude T Q F row col Φ Y r) +
              cNorm W k (fun w ↦ scalarAmplitude T Q F row col Φ Y r w •
                nullvector T Q col w) ≤
            B k * (1 + cNorm K (k + 13) F + cNorm Kr (k + 13) r)) →
          ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) (C ⁻¹' D) ∧
          (∀ w ∈ C ⁻¹' D,
            Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
              Complex.ofReal *ᵥ (fun i ↦ fullCorrectionCovector T Q F row col Φ Y r w i)) +
              (fun i ↦ (reducedOperator F Q.1
                (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0) ∧
          ∀ k, cNorm (closedBall a (2 * σ)) k (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ k * (1 + cNorm K (k + 14) F + cNorm Kr (k + 14) r) := by
  classical
  let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
  let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
  by_cases hgeometry : closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K))
  · have hsmall : closedBall a (2 * σ) ⊆ closedBall a (2 * ρ) :=
      hcoeff.trans (closedBall_subset_closedBall (by linarith))
    have hW : IsCompact W :=
      (isCompact_Icc.prod (isCompact_closedBall p₀ (R / 64))).image C.symm.continuous
    obtain ⟨Γ, hΓ, hbound⟩ := exists_fullCorrectionCovector_retained_bounds (N := N)
      T hK hKU hballK a (by positivity : 0 < 2 * σ)
      (fun w hw ↦ mem_closedBall.mpr (mem_ball.mp (hgeometry.2 (hsmall hw)).1).le)
      (hsmall.trans hgeometry.1) hW hworking row col M Mᵣ B hκmet hκnormal hb
    refine ⟨Γ, hΓ, ?_⟩
    intro F hF hi hrank hFM hmet hnormal hlow
    dsimp only
    intro hdom hx D Φ Y hD hcover hphys hcolumn r hrM hα hnonzero htransport hscalar
    let Q := (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
    have hWΩ : W ⊆ C ⁻¹' D := by
      rintro w ⟨q, hq, rfl⟩
      change C (C.symm q) ∈ D
      rw [C.apply_symm_apply]
      apply hcover
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
        (closedBall_subset_ball (by linarith : R / 64 < R / 32)) hq.2⟩
    have hxU : MapsTo Prod.fst (C ⁻¹' D) U :=
      fun w hw ↦ hKU (interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2)
    have hphase : C ⁻¹' D ⊆ domain T :=
      fun w hw ↦ hdom (ball_subset_closedBall (hphys hw))
    refine ⟨contDiffOn_fullCorrectionCovector_of_leading_outputs T Q F row col Φ Y r
      hΩ hxU (fun w hw ↦ (hphase hw)) hF hi hα hnonzero, ?_, ?_⟩
    · intro w hw
      exact fullCorrectionCovector_cancel_of_leading_outputs T Q F row col Φ Y r (w := w)
        (hphase hw) (hnonzero w hw).1 (hnonzero w hw).2 (htransport w hw)
    · exact hbound F hF hi hrank hFM hmet hnormal hlow Φ Y r _ (C ⁻¹' D)
        hΩ hWΩ hxU hphase hα hrM hscalar hcolumn
  · refine ⟨fun _ ↦ 1, fun _ ↦ zero_lt_one, ?_⟩
    intro F hF hi hrank hFM hmet hnormal hlow
    dsimp only
    intro hdom hx
    exact (hgeometry ⟨hdom, hx⟩).elim

end JanetCartan.RawPrimary.RetainedCorrection
