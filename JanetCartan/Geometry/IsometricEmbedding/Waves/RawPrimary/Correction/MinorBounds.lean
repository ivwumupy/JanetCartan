module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds.FiniteJet
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Neighborhood

/-!
# Quantitative selected-minor bounds from the transport producer

The actual coefficient constructor retains a positive adapted denominator
gap and a low bound on `(Q, phaseGradient)`. On their fixed compact range,
characteristicity forces the SAME selected adjugate entry to stay away from
zero. This supplies the reciprocal-minor input of
`CorrectionBounds.exists_fullCorrectionCovector_bounds`, for
`app:ch_waves:eq:primary-algebraic-correction` and
`app:ch_waves:eq:WKB-grading`. Constants precede all current fields and labels.
The final actual-family assembly must retain the denominator gap from
`UniformCoefficients.exists_uniform_denominator_neighborhood`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport NullTransport.CoefficientBounds
open LeadingWave.FullModulation LeadingWave.FullModulation.UniformCoefficients

variable {n : ℕ}

private theorem selectedMinor_ne_zero {H : MetricTensor n} {row col : Fin n}
    (hH : H.det = 0) (hk : rightNullvector H col ≠ 0)
    (hl : leftNullvector H row ≠ 0) : H.adjugate row col ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, H.adjugate row j ≠ 0 := by
    by_contra! h
    apply hl
    funext j
    exact h j
  intro hm
  apply hk
  have hh := kernel_eq_smul_rightNullvector hH hj (mulVec_rightNullvector hH col)
  simpa only [rightNullvector, hm, zero_div, zero_smul] using hh

private theorem continuous_input_symbol :
    Continuous (fun p : Input n ↦ reducedSymbol p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : Input n ↦ CorrectionBounds.symbolValue (p, (0 : ℝ))) :=
    CorrectionBounds.contDiff_symbolValue.comp (contDiff_id.prodMk contDiff_const)
  exact h.continuous

/-- A fixed primitive denominator gap gives a uniform gap for the SAME
selected minor on the characteristic set. No correction or inverse estimate
is a hypothesis (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem exists_selected_minor_gap_of_denominator (ν : Euclidean n) (row col : Fin n)
    (L : ℝ) {g : ℝ} (hg : 0 < g) :
    ∃ δ > (0 : ℝ), ∀ p : Input n, ‖p‖ ≤ L →
      (reducedSymbol p.1 p.2).det = 0 → g ≤ |denominator ν row col p| →
        δ ≤ |(reducedSymbol p.1 p.2).adjugate row col| ∧
        |((reducedSymbol p.1 p.2).adjugate row col)⁻¹| ≤ δ⁻¹ := by
  let s := admissibleInputs ν row col L g ∩
    {p : Input n | (reducedSymbol p.1 p.2).det = 0}
  have hs : IsCompact s := (compact_admissibleInputs ν row col L g).inter_right
    (isClosed_eq continuous_input_symbol.matrix_det continuous_const)
  have hc : Continuous (fun p : Input n ↦ |(reducedSymbol p.1 p.2).adjugate row col|) :=
    (((continuous_apply col).comp (continuous_apply row)).comp
      continuous_input_symbol.matrix_adjugate).abs
  have hpos (p) (hp : p ∈ s) : 0 < |(reducedSymbol p.1 p.2).adjugate row col| := by
    have hd := abs_pos.mp (hg.trans_le hp.1.2)
    apply abs_pos.mpr (selectedMinor_ne_zero hp.2 ?_ (left_ne_zero_of_denominator hd))
    intro hk
    apply right_ne_zero_of_denominator hd
    ext i
    exact congrFun hk i
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > (0 : ℝ),
      ∀ p ∈ s, δ ≤ |(reducedSymbol p.1 p.2).adjugate row col| := by
    by_cases hne : s.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hs.exists_isMinOn hne hc.continuousOn
      exact ⟨_, hpos p hp, hmin⟩
    · exact ⟨1, zero_lt_one, fun p hp ↦ (hne ⟨p, hp⟩).elim⟩
  refine ⟨δ, hδ, ?_⟩
  intro p hp hchar hd
  have hb := hbound p ⟨⟨mem_closedBall_zero_iff.mpr hp, hd⟩, hchar⟩
  exact ⟨hb, by rw [abs_inv]; exact (inv_le_inv₀ (hδ.trans_le hb) hδ).mpr hb⟩

/-- One common reciprocal-minor budget works for every carrier's selected
row and column. The constants depend only on the primitive low range and
denominator gap (`app:ch_waves:eq:WKB-grading`). -/
theorem exists_uniform_selected_minor_gap_of_denominator (hn : 0 < n)
    (ν : Euclidean n) (L : ℝ) {g : ℝ} (hg : 0 < g) :
    ∃ δ > (0 : ℝ), ∀ (row col : Fin n) (p : Input n), ‖p‖ ≤ L →
      (reducedSymbol p.1 p.2).det = 0 → g ≤ |denominator ν row col p| →
        δ ≤ |(reducedSymbol p.1 p.2).adjugate row col| ∧
        |((reducedSymbol p.1 p.2).adjugate row col)⁻¹| ≤ δ⁻¹ := by
  classical
  choose δ hδ hb using fun rc : Fin n × Fin n ↦
    exists_selected_minor_gap_of_denominator ν rc.1 rc.2 L hg
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  let δ₀ := Finset.univ.inf' hne δ
  have hδ₀ : 0 < δ₀ := Finset.lt_inf'_iff hne |>.mpr (fun rc _ ↦ hδ rc)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro row col p hp hchar hd
  have hle : δ₀ ≤ δ (row, col) := Finset.inf'_le δ (Finset.mem_univ _)
  have hh := hb (row, col) p hp hchar hd
  exact ⟨hle.trans hh.1, hh.2.trans ((inv_le_inv₀ (hδ (row, col)) hδ₀).mpr hle)⟩

open ActualCarriers FrozenMenu CurrentFullPhase

/-- The denominator neighborhood producer also supplies a selected-minor
gap, uniformly before the actual frame is chosen. The frame/phase input
bound and neighborhood denominator bound are both proved by that producer;
only its original carrier-center gap is required
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:WKB-grading`). -/
theorem exists_fullPhase_minor_neighborhood
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (hn : 2 ≤ n)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {R : ℝ} (hR : 0 < R)
    (hx : MapsTo Prod.fst (closedBall a R)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hdom : closedBall a R ⊆ domain T) (row col : Fin n) {g : ℝ} (hg : 0 < g) :
    ∃ η ρ L δ : ℝ, 0 < η ∧ 0 < ρ ∧ 0 < L ∧ 0 < δ ∧ 2 * ρ ≤ R ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < η →
        g ≤ |adaptedDenominator T Q row col a| →
        cNorm (closedBall a (2 * ρ)) 1 (fullInput T Q) ≤ L ∧
        ∀ w ∈ closedBall a (2 * ρ),
          δ ≤ |(reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col| ∧
          |((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col)⁻¹| ≤ δ⁻¹ := by
  obtain ⟨η, ρ, L, b, hη, hρ, hL, _hb, hρR, hneigh⟩ :=
    exists_uniform_denominator_neighborhood T hn a hR hx hballU hdom row col hg
  obtain ⟨δ, hδ, hminor⟩ :=
    exists_selected_minor_gap_of_denominator T.data.adapted.normal row col L (half_pos hg)
  refine ⟨η, ρ, L, δ, hη, hρ, hL, hδ, hρR, ?_⟩
  intro Q hclose hcenter
  obtain ⟨hlow, hgap⟩ := hneigh Q hclose hcenter
  have hsub : closedBall a (2 * ρ) ⊆ closedBall a R := closedBall_subset_closedBall hρR
  have hinput : closedBall a (2 * ρ) ⊆ UniformCoefficients.inputDomain T :=
    fun w hw ↦ ⟨hdom (hsub hw), hballU (hx (hsub hw))⟩
  refine ⟨hlow, ?_⟩
  intro w hw
  have hnorm := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a (2 * ρ))
    (fun y hy ↦ ((smooth_fullInput T Q).contDiffAt
      ((UniformCoefficients.isOpen_inputDomain T).mem_nhds (hinput hy))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
  rw [norm_iteratedFDeriv_zero] at hnorm
  exact hminor (fullInput T Q w) (hnorm.trans hlow)
    (phase_characteristic T Q (hdom (hsub hw))) (hgap w hw).1

end JanetCartan.RawPrimary
