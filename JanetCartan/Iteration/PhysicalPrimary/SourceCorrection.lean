module

public import JanetCartan.Iteration.PhysicalPrimary.LeadingAdmission
public import JanetCartan.Iteration.PhysicalPrimary.LeadingSourceFacts
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.CellBounds

/-!
# Actual retained correction budgets on revised physical histories

The original cell, full transport and scalar bounds are unchanged. The fixed
C14 and geometric gaps are produced from revised physical admissibility. The
retained correction constructor then selects ONE profile before the history,
not a history-dependent reciprocal of a qualitative nonvanishing claim.
Consumer: `exists_history_reducedSource_reserved_fourier_profiles`, through
its original full-strain source (`app:ch_waves:eq:primary-algebraic-correction`,
`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation
open RawPrimary RawPrimary.RetainedCorrection

/-- Produce the full correction's fixed shift-fourteen budget on the original
doubled covering ball. All scalar/transport clauses are literal projections of
`LeadingCell.scalar_source_data`; the correction estimate is a conclusion, not
an input (`app:ch_response:eq:response-graded-source`). -/
theorem exists_history_retained_correction_bounds {n : ℕ} (G : FlatReference n)
    {rGeom RGeom : ℝ} (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom)
    (hRGeom : RGeom < G.domain.chartRadius)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 RGeom) isOpen_ball)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ closedBall 0 rGeom)
    (z₀ : Euclidean 3) (row col : Fin n)
    {ρ R time σ : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (htime : 0 < time) (hσ : 0 < σ)
    (Mscalar : ℝ) (Bscalar : ℕ → ℝ) {columnGap : ℝ} (hcolumnGap : 0 < columnGap)
    (hworking : let a := ((0 : Euclidean n),(z₀,T.reference.spatialPatch z₀))
      closedBall a (2*σ) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-time/2) (time/2) ×ˢ
            closedBall ((0 : Euclidean (n-1)),(z₀,T.reference.spatialPatch z₀)) (R/64)))
    (hcoeff : let a := ((0 : Euclidean n),(z₀,T.reference.spatialPatch z₀))
      closedBall a (2*σ) ⊆ closedBall a ρ)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ)/2) + 2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Γ : ℕ → ℝ, (∀ k, 0 < Γ k) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 RGeom))
        (hi : IsImmersionOn F (ball 0 RGeom)) (hrank : HasFullNormalRankOn F (ball 0 RGeom)),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q (ball 0 RGeom) ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank),hlow⟩
      let a := ((0 : Euclidean n),(z₀,T.reference.spatialPatch z₀))
      let p₀ := ((0 : Euclidean (n-1)),(z₀,T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n-1)) (adaptedCoordinates T.data.adapted)
      let W := C.symm '' (Icc (-time/2) (time/2) ×ˢ closedBall p₀ (R/64))
      closedBall a (2*ρ) ⊆ domain T →
      MapsTo Prod.fst (closedBall a (2*ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball 0 T.physicalRadius ∩ interior (closedBall 0 rGeom))) →
      ∀ (D : Set (ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))))
        (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
          Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))),
      IsOpen D → Ioo (-time) time ×ˢ ball p₀ (R/32) ⊆ D → C ⁻¹' D ⊆ ball a (2*ρ) →
      (∀ w ∈ C ⁻¹' D, columnGap ≤ ‖nullvector T Q col w‖) →
      ∀ initial : Euclidean (n-1) × Euclidean 3 → ℝ,
      let Kr := closedBall ((0 : Euclidean (n-1)),z₀) (R/8)
      cNorm Kr 14 initial ≤ Mscalar →
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y initial) (C ⁻¹' D) →
      (∀ w ∈ C ⁻¹' D, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ scalarAmplitude T Q F row col Φ Y initial (x,w.2) •
          nullvector T Q col (x,w.2)) w.1 = 0) →
      (∀ k, cNorm W k (scalarAmplitude T Q F row col Φ Y initial) +
        cNorm W k (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) ≤
        Bscalar k*(1+cNorm (closedBall 0 rGeom) (k+13) F+cNorm Kr (k+13) initial)) →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y initial) (C ⁻¹' D) ∧
        ∀ k, cNorm (closedBall a (2*σ)) k (fullCorrectionCovector T Q F row col Φ Y initial) ≤
          Γ k*(1+cNorm (closedBall 0 rGeom) (k+14) F+cNorm Kr (k+14) initial) := by
  obtain ⟨SG,hSG,_C₀,_hC₀,κ,hκ,hgeom⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G hrGeom hrR hRGeom hBband (by omega) horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨S14,_hS14,hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := embeddingDimension n) hBband horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Γ,hΓ,hcorrection⟩ := exists_retained_cell_correction_bounds
    (N := embeddingDimension n) T (isCompact_closedBall (0 : Euclidean n) rGeom)
    (closedBall_subset_ball hrR) hball z₀ row col hρ hR htime hσ
    (cNorm (closedBall 0 rGeom) 14 G.map+1) Mscalar Bscalar
    (by norm_num : (0 : ℝ) < 1/4) hκ hcolumnGap hworking hcoeff
  refine ⟨max SG S14,hSG.trans (le_max_left _ _),Γ,hΓ,?_⟩
  intro R₀ hR₀ stage u ell hu F
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi,hrank,_h4,hmet,hnormal,_⟩ := hgeom R₀ ((le_max_left _ _).trans hR₀) stage u ell hu
  have h14 : cNorm (closedBall (0 : Euclidean n) rGeom) 14 F ≤
      cNorm (closedBall 0 rGeom) 14 G.map+1 := by
    have hsmall := (cNorm_mono_order hStar (s := closedBall (0 : Euclidean n) rGeom)
      (f := F-G.map)).trans_lt (hnear R₀ ((le_max_right _ _).trans hR₀)
        (closedBall 0 rGeom) G.map (isCompact_closedBall _ _) stage u ell hu)
    have hadd := cNorm_add_le (isCompact_closedBall (0 : Euclidean n) rGeom)
      (G.contDiff.of_le (by simp : (14 : ℕ∞ω) ≤ ∞))
      ((hF.sub G.contDiff).of_le (by simp : (14 : ℕ∞ω) ≤ ∞))
    have he : G.map+(F-G.map) = F := by abel
    change cNorm (closedBall (0 : Euclidean n) rGeom) 14 (G.map+(F-G.map)) ≤
      cNorm (closedBall 0 rGeom) 14 G.map+cNorm (closedBall 0 rGeom) 14 (F-G.map) at hadd
    rw [he] at hadd
    linarith
  refine ⟨hF.contDiffOn,hi,hrank,?_⟩
  intro hlow Q a p₀ C W hdom hphysical D Φ Y hD hcover hphys hcolumn
    initial Kr hInitial hα hnonzero htransport hscalar
  have hc := hcorrection F hF.contDiffOn hi hrank h14
    (fun x hx ↦ hmet x (closedBall_subset_ball hrR hx))
    (fun x hx ↦ hnormal x (closedBall_subset_ball hrR hx)) hlow hdom hphysical
    D Φ Y hD hcover hphys hcolumn initial hInitial hα hnonzero htransport hscalar
  exact ⟨hc.1,hc.2.2⟩

end JanetCartan.PhysicalPrimary
