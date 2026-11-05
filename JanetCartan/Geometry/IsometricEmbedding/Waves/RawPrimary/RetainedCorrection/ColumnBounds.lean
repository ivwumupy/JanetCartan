module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds.JetBounds

/-!
# Quantitative correction from the retained null-column lower bound

The retained leading family already gives `b ≤ ‖nullvector ... col w‖` on
its full flow domain. This is enough for the EXISTING Gram inverse: its
formula depends on the selected column, and needs only some nonzero entry
in that column for the previously proved invertibility lemma. The row used
to witness invertibility is local to the proof; no phase, scalar, flow,
selected transport row or selected column is changed.

Use a compact primitive jet range with this literal lower bound to obtain
one-high estimates. This avoids requiring reciprocal regularity outside the
retained flow domain. Consumer: the reserve-fourteen correction estimate in
`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-grading`.
`RetainedCorrection.CellBounds` supplies the geometric containment of the
estimate ball from the retained producer's original working-ball output.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.RetainedCorrection
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile
open CorrectionBounds

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

/-- The same correction jet has a one-high bound from the quantitative
null-column conclusion exported by
`exists_finite_retained_leading_family_before_geometry`. The existing
selected-minor inverse algebra supplies smoothness on a compact range; no
minor gap, inverse bound, or reciprocal bound is an input. The derivative
cost is still one (`app:ch_waves:eq:WKB-grading`). -/
theorem exists_correctionJetValue_tame_of_retained_column
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ) (col : Fin n)
    (M L : ℝ) {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n × Z)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ (v : Euclidean n × Z → Values n) (J : Euclidean n × Z → StressJet n N),
        ContDiffOn ℝ ∞ v Ω → ContDiffOn ℝ ∞ J Ω →
        cNorm (closedBall a ρ) 1 v ≤ L →
        (∀ w ∈ closedBall a ρ, ‖J w‖ ≤ M) →
        (∀ w ∈ closedBall a ρ, ∀ u, κ * ‖u‖ ^ 2 ≤ ‖(J w).1 u‖ ^ 2) →
        (∀ w ∈ closedBall a ρ, (symbolValue (v w)).det = 0) →
        (∀ w ∈ closedBall a ρ, b ≤ ‖right col (v w).1‖) →
        ∀ m, cNorm (closedBall a ρ) m
          (fun w ↦ correctionJetValue col (J w, v w, fderiv ℝ v w)) ≤
            C m * (1 + cNorm (closedBall a ρ) m J +
              cNorm (closedBall a ρ) (m + 1) v) := by
  let s := admissibleJets (N := N) (Z := Z) col col M L κ 0 ∩
    {p : Jet n N Z | b ≤ ‖right col p.2.1.1‖}
  have hs : IsCompact s := (isCompact_admissibleJets col col M L κ 0).inter_right
    (isClosed_le continuous_const (((smooth_right col).continuous.comp
      continuous_snd.fst.fst).norm))
  have hsmooth (p : Jet n N Z) (hp : p ∈ s) :
      ContDiffAt ℝ ∞ (correctionJetValue col) p := by
    have hk : right col p.2.1.1 ≠ 0 := norm_pos_iff.mp (hb.trans_le hp.2)
    obtain ⟨row, hrow⟩ : ∃ row, (symbolValue p.2.1).adjugate row col ≠ 0 := by
      by_contra! hz
      apply hk
      ext i
      exact hz i
    exact contDiffAt_correctionJetValue row col
      (firstJetMetric_isUnit_of_gap hκ hp.1.2.1) hp.1.2.2.2.2.1 hrow
  choose C hC hcomp using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ hs
      (r := m) (k := m) le_rfl (g := correctionJetValue col)
      (fun p hp ↦ (hsmooth p hp).of_le (by simp))
  refine ⟨fun m ↦ C m * (1 + (m + 1) + 2 * (m + 1) ^ 2),
    fun m ↦ mul_pos (hC m) (by positivity), ?_⟩
  intro Ω hΩ hball v J hv hJ hlow hM hmet hchar hcolumn m
  have hd := hv.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  let p : Euclidean n × Z → Jet n N Z := fun w ↦ (J w, v w, fderiv ℝ v w)
  have hp : ContDiffOn ℝ ∞ p Ω := hJ.prodMk (hv.prodMk hd)
  have hmap : MapsTo p (closedBall a ρ) s := by
    intro w hw
    have hv0 : ‖v w‖ ≤ cNorm (closedBall a ρ) 1 v := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hv.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
            (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
    have hd0 : ‖fderiv ℝ v w‖ ≤ cNorm (closedBall a ρ) 0 (fderiv ℝ v) := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hd.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
            (by simp : (0 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 0)
    exact ⟨⟨hM w hw, hmet w hw, hv0.trans hlow,
      hd0.trans ((cNorm_fderiv_le _ 0 v).trans hlow), hchar w hw, abs_nonneg _⟩, hcolumn w hw⟩
  have hout := hcomp m Ω hΩ hball p hp hmap
  have hp₁ := cNorm_pair_le a m hΩ hball hJ (hv.prodMk hd)
  have hp₂ := cNorm_pair_le a m hΩ hball hv hd
  let H := 1 + cNorm (closedBall a ρ) m J + cNorm (closedBall a ρ) (m + 1) v
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall a ρ) m J, cNorm_nonneg (closedBall a ρ) (m + 1) v]
  have hJH : cNorm (closedBall a ρ) m J ≤ H := by
    dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) (m + 1) v]
  have hvH : cNorm (closedBall a ρ) m v ≤ H :=
    (cNorm_mono_order (Nat.le_succ m)).trans (by
      dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) m J])
  have hdH : cNorm (closedBall a ρ) m (fderiv ℝ v) ≤ H :=
    (cNorm_fderiv_le _ m v).trans (by
      dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) m J])
  have hp₂H := hp₂.trans (mul_le_mul_of_nonneg_left (add_le_add hvH hdH)
    (by positivity : (0 : ℝ) ≤ m + 1))
  have hp₁H : cNorm (closedBall a ρ) m p ≤
      ((m + 1 : ℝ) + 2 * (m + 1) ^ 2) * H := by
    exact (hp₁.trans (mul_le_mul_of_nonneg_left (add_le_add hJH hp₂H)
      (by positivity))).trans_eq (by ring)
  have htotal : 1 + cNorm (closedBall a ρ) m p ≤
      (1 + (m + 1 : ℝ) + 2 * (m + 1) ^ 2) * H := by
    nlinarith only [hp₁H, hH]
  exact hout.trans ((mul_le_mul_of_nonneg_left htotal (hC m).le).trans_eq (by ring))

end JanetCartan.RawPrimary.RetainedCorrection
