module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualLocal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.NormalGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.ActualCompatibility

/-!
# Denominator retained by the actual leading construction

Strengthen `FullModulation.exists_actual_positive_amplitude` without changing its
selected row, column, carrier flow, full flow, footpoint or initial datum. The
positive numerical denominator gap from `exists_uniform_coefficients` is retained
before the current immersion. It supplies the center input to
`RawPrimary.exists_fullPhase_minor_neighborhood` and
`RawPrimary.exists_fullCorrectionCovector_projected_bounds`
(`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-grading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer CarrierCompatibility

/-- Construct actual full-parameter positive leading amplitudes from primitive
geometric hypotheses. Constants precede the immersion and the initial datum;
the numerical denominator gap is retained on the coefficient ball and
both flows use the original selected minor (`app:ch_waves:thm:leading`,
`app:ch_waves:eq:joint-tame`). -/
theorem exists_actual_positive_amplitude_with_denominator {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M₁₂ Mᵣ κmet κnormal m : ℝ} (hM₁₂ : 0 ≤ M₁₂) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm : 0 < m)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g b cν Rc τc Mc rcomp δcomp d : ℝ, ∃ A H B : ℕ → ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ 0 < b ∧ 0 < cν ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ 0 < d ∧
      (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (∀ w ∈ closedBall a (2 * ρ), d ≤ |adaptedDenominator T Q row col w|) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) := by
  obtain ⟨row, col, ρc, Rc, ηc, τc, gc, Ac, Hc, _hρc, hRc, hηc, hτc, hgc,
    _hAc, hHc, _hbufferC, _hτRc, hcarrier⟩ :=
    exists_projected_local_positive_amplitude (N := embeddingDimension n)
      (by omega : 2 ≤ n) hP T hK hKU hball M₁₂ hκmet hκnormal z₀ hz₀
  obtain ⟨ηf, ρ, b, Bd, A, hηf, _hηfT, hρ, hb, _hBd, hA,
    hΩ, hsmallΩ, hdom, hx, hcoeff⟩ :=
    exists_uniform_coefficients (N := embeddingDimension n) (by omega : 2 ≤ n)
      hP T hK hKU hball M₁₂ hκmet hκnormal row col z₀ hz₀ hgc
  obtain ⟨R, τ, g, H, B, hR, hτ, hg, hH, hB, hτR, _hgFormula, hbuffer, hfull⟩ :=
    exists_positive_amplitude (N := embeddingDimension n) T K z₀ hρ hΩ hsmallΩ
      A hA hM₁₂ hMᵣ hm
  obtain ⟨δ, cν, hδ, hcν, hnormalGap⟩ :=
    exists_normal_gap_threshold hn hU hK hKU M₁₂ hb (mul_pos hg hb)
  let Mc := Hc 1 * (1 + M₁₂)
  let Mf := H 1 * (1 + M₁₂)
  let Mv := Mc + Mf
  have hMc : 0 ≤ Mc := mul_nonneg (hHc 1).le (by linarith)
  have hMf : 0 ≤ Mf := mul_nonneg (hH 1).le (by linarith)
  have hMv : 0 ≤ Mv := add_nonneg hMc hMf
  obtain ⟨Rg, Lg, hRg, hLg, hgraph⟩ := exists_local_carrierLabel_lipschitz
    T hP ((0 : Euclidean (n - 1)), z₀) hz₀
  obtain ⟨rcomp, δcomp, hrcomp, hδcomp, hδc, hδf, hrc, hrf, hMδ, hrg⟩ :=
    exists_comparison_radii hRc hR hRg hτc hτ hMv hLg
  refine ⟨row, col, ρ, R, min ηc (min ηf δ), τ, g, b, cν, Rc, τc,
    Mc, rcomp, δcomp, gc / 2, A, H, B, hρ, hR, lt_min hηc (lt_min hηf hδ),
    hτ, hg, hb, hcν, hRc, hτc, mul_pos (hHc 1) (by linarith),
    hrcomp, hδcomp, half_pos hgc, hA, hH, hB, hτR, hdom, hx, hbuffer, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hF4 : cNorm K 4 F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFM
  obtain ⟨hlow, Dc, φ, y, hDc, hcoverc, hbigc, _hphysc, _hφ, _hy, hφDc, hyL,
    hφ₀, hyφ, hφy, _hcz, _hyz, hvelocityc, _hnullc, _hcoeffc, hflowc,
    _hregc, hφbuffer, _hybuffer, _hbufc, _hτcR, hgapc, _hsolc⟩ :=
    hcarrier F hF hi hrank hF4 hmet hnormal (hclose.trans_le (min_le_left _ _))
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let Cc := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hcenter : Cc ((0 : Euclidean n), z₀) ∈ Dc := by
    apply hcoverc
    have he : Cc ((0 : Euclidean n), z₀) = (0, 0, z₀) := by simp [Cc]
    rw [he]
    exact ⟨⟨by linarith, hτc⟩, mem_ball_self (by positivity)⟩
  have hcenterGap : gc ≤ |carrierAdaptedDenominator T Q row col (0, z₀)| :=
    (hgapc _ hcenter).1
  obtain ⟨hlowf, hcoefff⟩ := hcoeff F hF hi hrank hF4 hmet hnormal
    (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hk, _hl, _hd, _hinv, hdir, hpot, hgap, _hdirLow, hhigh⟩ := hcoefff hcenterGap
  let Ω := ball ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * ρ)
  have hΩU : ∀ w ∈ Ω, w.1 ∈ U :=
    fun w hw ↦ hKU (interior_subset (hx (ball_subset_closedBall hw)).2.2)
  have hsym : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm := fun w hw i ↦
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds (hΩU w hw))).of_le (by simp)) (hrank w.1 (hΩU w hw)) i).1
  obtain ⟨D, Φ, Y, hD, hcover, hbig, hphys, hΦ, hY, hΦD, hYL,
    hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity, hΦbuffer, hYbuffer, hflow, hsolution⟩ :=
    hfull Q F row col hk hdir hpot
      (fun w hw ↦ (hgap w (ball_subset_closedBall hw)).2.1) hsym
      (fun w hw ↦ hdom (ball_subset_closedBall hw)) hhigh hFM
  have hflowcLow : cNorm (Icc (-τc) τc ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 φ ≤ Hc 1 * (1 + M₁₂) := by
    have hh := hflowc 1
    have hf6 : cNorm K (1 + 5) F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFM
    have hm6 := mul_le_mul_of_nonneg_left (add_le_add_right hf6 1) (hHc 1).le
    linarith [cNorm_nonneg (Icc (-τc) τc ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 y]
  have hF6 : cNorm K (1 + 5) F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFM
  have hflowfLow : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 8)) 1 Φ ≤ Mf := by
    have hh := hflow 1
    have hh' := mul_le_mul_of_nonneg_left (add_le_add_right hF6 1) (hH 1).le
    dsimp only [Mf]
    linarith [cNorm_nonneg (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 8)) 1 Y]
  let Md := A 1 * (1 + M₁₂)
  have hMd : 0 ≤ Md := mul_nonneg (hA 1).le (by linarith)
  have hdirLow : cNorm (closedBall ((0 : Euclidean n),
      (z₀, T.reference.spatialPatch z₀)) ρ) 1 (transportDirection T Q row col) ≤ Md := by
    have hh := hhigh 1
    have hh' := mul_le_mul_of_nonneg_left (add_le_add_right hF6 1) (hA 1).le
    dsimp only [Md]
    linarith [cNorm_nonneg (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ)
        1 (nullvector T Q col),
      cNorm_nonneg (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ)
        1 (conullvector T Q row),
      cNorm_nonneg (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ)
        1 (adaptedDenominator T Q row col),
      cNorm_nonneg (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ)
        1 (fun w ↦ (adaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ)
        1 (transportPotential T Q F row col)]
  have hspeedc p hp t ht : ‖carrierVelocity T Q row col t (φ (t, p))‖ ≤ Mv :=
    (flow_speed_le_cNorm hRc hτc hφbuffer hflowcLow hp ht (hvelocityc p hp t ht)).trans
      (le_add_of_nonneg_right hMf)
  have hspeedf p hp t ht : ‖fullVelocity T Q row col t (Φ (t, p))‖ ≤ Mv :=
    (flow_speed_le_cNorm hR hτ hΦbuffer hflowfLow hp ht (hvelocity p hp t ht)).trans
      (le_add_of_nonneg_left hMc)
  have hlip t (ht : t ∈ Ioo (-δcomp) δcomp) :
      LipschitzOnWith ⟨liftedLowBound T Md, liftedLowBound_nonneg T hMd⟩
        (fullVelocity T Q row col t)
        (closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 2)) :=
    fullVelocity_lipschitz_of_direction_bound T Q row col hΩ
      (isCompact_closedBall _ _) hsmallΩ hdir hMd hR hτR hdirLow hbuffer
      (show t ∈ Ioo (-τ) τ from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcompat := compatibility_on_common_buffer T Q F row col
    hRc hR hrcomp hδcomp hMv hLg hδc hδf hrc hrf hMδ hrg hgraph
    hcoverc hcover (fun q hq ↦ (hyL hq).2) hφy hYΦ hφ₀ hΦ₀
    hvelocityc hvelocity hspeedc hspeedf hlip
  refine ⟨hlow, (fun w hw ↦ (hgap w hw).1), Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, ?_, hhigh, hcompat, ?_⟩
  · intro w hw
    have hh := hgap w (ball_subset_closedBall (hphys hw))
    exact ⟨hh.2.2.2.1, hh.2.2.2.2.2.1,
      nullvector_relations T Q row col (hdom (ball_subset_closedBall (hphys hw)))⟩
  · intro r hr hrLow hrmin
    obtain ⟨hα, hαk, hinitial, hpos, hpde, hsymbol, hreduce, htame⟩ :=
      hsolution r hr hrLow hrmin
    refine ⟨hα, hαk, hinitial, hpos, hpde, hsymbol, hreduce, htame, ?_⟩
    let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
      (adaptedCoordinates T.data.adapted)
    have hident := reconstruction_identities T hF hi hrank hlow
      (hD.preimage C.continuous) (fun w hw ↦ ⟨hΩU w (hphys hw), mem_univ _⟩)
      (fun w hw ↦ hdom (ball_subset_closedBall (hphys hw))) hαk
    intro w hw
    have hwK : w.1 ∈ K := interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2
    have hgaps := hgap w (ball_subset_closedBall (hphys hw))
    have hαpos := (hpos w hw).2.1
    have hamp : g * b ≤ ‖scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
      exact mul_le_mul (hpos w hw).1 hgaps.2.2.2.1 hb.le hαpos.le
    refine ⟨hnormalGap F hF hi hrank hF4
      (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))) w.1 hwK
      _ _ (hsymbol w hw) hgaps.2.2.2.2.2.1 hamp,
      (hident w hw).1, (hident w hw).2.1, (hident w hw).2.2,
      principalNormal_hermitianTensor F w.1 _ _⟩

end JanetCartan.LeadingWave.FullModulation
