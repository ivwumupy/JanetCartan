module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds.FiniteJet

/-!
# One-high bounds from primitive correction jets

For `app:ch_waves:eq:WKB-grading`, the compact range depends only on primitive
low budgets, the immersion metric gap and the fixed symbol minor gap.
The consumer is the bound for the literal `fullCorrectionCovector`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.CorrectionBounds
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

/-- The bounded primitive jet range for
`app:ch_waves:eq:primary-algebraic-correction`. The metric gap is imposed
on the first immersion derivative; the minor is that of the original symbol. -/
def admissibleJets (row col : Fin n) (M L κ δ : ℝ) : Set (Jet n N Z) :=
  {p | ‖p.1‖ ≤ M ∧ (∀ v, κ * ‖v‖ ^ 2 ≤ ‖p.1.1 v‖ ^ 2) ∧
    ‖p.2.1‖ ≤ L ∧ ‖p.2.2‖ ≤ L ∧ (symbolValue p.2.1).det = 0 ∧
      δ ≤ |(symbolValue p.2.1).adjugate row col|}

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- Compactness comes from primitive inequalities, without an inverse norm
or correction estimate (`app:ch_waves:eq:WKB-grading`). -/
theorem isCompact_admissibleJets (row col : Fin n) (M L κ δ : ℝ) :
    IsCompact (admissibleJets (N := N) (Z := Z) row col M L κ δ) := by
  let : FiniteDimensional ℝ (StressJet n N) := inferInstance
  let : FiniteDimensional ℝ (Values n) := inferInstance
  let : FiniteDimensional ℝ ((Euclidean n × Z) →L[ℝ] Values n) := inferInstance
  let : ProperSpace (Jet n N Z) := FiniteDimensional.proper ℝ (Jet n N Z)
  have hm : IsClosed {p : Jet n N Z | ∀ v, κ * ‖v‖ ^ 2 ≤ ‖p.1.1 v‖ ^ 2} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_le continuous_const
      ((((continuous_fst : Continuous (Prod.fst : Jet n N Z → StressJet n N)).fst).clm_apply
        continuous_const).norm.pow 2)
  have hS : Continuous (fun p : Jet n N Z ↦ symbolValue p.2.1) :=
    contDiff_symbolValue.continuous.comp continuous_snd.fst
  have ha : Continuous (fun p : Jet n N Z ↦ (symbolValue p.2.1).adjugate row col) :=
    (Matrix.entryLinearMap ℝ ℝ row col).toContinuousLinearMap.continuous.comp hS.matrix_adjugate
  have hc₁ : IsClosed {p : Jet n N Z | ‖p.1‖ ≤ M} := by
    have h : IsClosed ((fun p : Jet n N Z ↦ p.1) ⁻¹' closedBall (0 : StressJet n N) M) :=
      isClosed_closedBall.preimage continuous_fst
    convert h using 1
    ext p
    change (‖p.1‖ ≤ M) ↔ dist p.1 0 ≤ M
    rw [show dist p.1 0 = ‖p.1‖ from dist_zero_right p.1]
  have hc₂ : IsClosed {p : Jet n N Z | ‖p.2.1‖ ≤ L} := by
    have h : IsClosed ((fun p : Jet n N Z ↦ p.2.1) ⁻¹' closedBall (0 : Values n) L) :=
      isClosed_closedBall.preimage continuous_snd.fst
    convert h using 1
    ext p
    change (‖p.2.1‖ ≤ L) ↔ dist p.2.1 0 ≤ L
    rw [show dist p.2.1 0 = ‖p.2.1‖ from dist_zero_right p.2.1]
  have hc₃ : IsClosed {p : Jet n N Z | ‖p.2.2‖ ≤ L} := by
    have h : IsClosed ((fun p : Jet n N Z ↦ p.2.2) ⁻¹'
        closedBall (0 : (Euclidean n × Z) →L[ℝ] Values n) L) :=
      isClosed_closedBall.preimage continuous_snd.snd
    convert h using 1
    ext p
    change (‖p.2.2‖ ≤ L) ↔ dist p.2.2 0 ≤ L
    rw [dist_zero_right]
  have hc₄ : IsClosed {p : Jet n N Z | (symbolValue p.2.1).det = 0} :=
    isClosed_eq hS.matrix_det continuous_const
  have hc₅ : IsClosed {p : Jet n N Z | δ ≤ |(symbolValue p.2.1).adjugate row col|} :=
    isClosed_le continuous_const ha.abs
  have hc : IsClosed (admissibleJets (N := N) (Z := Z) row col M L κ δ) :=
    hc₁.inter (hm.inter (hc₂.inter (hc₃.inter (hc₄.inter hc₅))))
  have hcompact : IsCompact (closedBall (0 : Jet n N Z) (max M L)) :=
    isCompact_closedBall _ _
  apply hcompact.of_isClosed_subset hc
  intro p hp
  rw [Metric.mem_closedBall, show dist p 0 = ‖p‖ from dist_zero_right p,
    Prod.norm_def, Prod.norm_def]
  exact max_le (hp.1.trans (le_max_left _ _))
    (max_le (hp.2.2.1.trans (le_max_right _ _)) (hp.2.2.2.1.trans (le_max_right _ _)))

/-- Uniform one-high composition bound for the actual correction jet formula.
Its constant is chosen before the open chart, primitive fields, frequency,
and carrier labels (`app:ch_waves:eq:WKB-grading`). -/
theorem exists_correctionJetValue_tame
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ) (row col : Fin n)
    (M L : ℝ) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n × Z)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ (v : Euclidean n × Z → Values n) (J : Euclidean n × Z → StressJet n N),
        ContDiffOn ℝ ∞ v Ω → ContDiffOn ℝ ∞ J Ω →
        cNorm (closedBall a ρ) 1 v ≤ L →
        (∀ w ∈ closedBall a ρ, ‖J w‖ ≤ M) →
        (∀ w ∈ closedBall a ρ, ∀ u, κ * ‖u‖ ^ 2 ≤ ‖(J w).1 u‖ ^ 2) →
        (∀ w ∈ closedBall a ρ, (symbolValue (v w)).det = 0) →
        (∀ w ∈ closedBall a ρ, δ ≤ |(symbolValue (v w)).adjugate row col|) →
        ∀ m, cNorm (closedBall a ρ) m
          (fun w ↦ correctionJetValue col (J w, v w, fderiv ℝ v w)) ≤
            C m * (1 + cNorm (closedBall a ρ) m J +
              cNorm (closedBall a ρ) (m + 1) v) := by
  choose C hC hb using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ
      (isCompact_admissibleJets (N := N) (Z := Z) row col M L κ δ)
      (r := m) (k := m) le_rfl (g := correctionJetValue col)
      (fun p hp ↦ (contDiffAt_correctionJetValue row col
        (firstJetMetric_isUnit_of_gap hκ hp.2.1) hp.2.2.2.2.1
        (abs_pos.mp (hδ.trans_le hp.2.2.2.2.2))).of_le (by simp))
  refine ⟨fun m ↦ C m * (1 + (m + 1) + 2 * (m + 1) ^ 2),
    fun m ↦ mul_pos (hC m) (by positivity), ?_⟩
  intro Ω hΩ hball v J hv hJ hlow hM hmet hchar hminor m
  have hd := hv.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  let p : Euclidean n × Z → Jet n N Z := fun w ↦ (J w, v w, fderiv ℝ v w)
  have hp : ContDiffOn ℝ ∞ p Ω := hJ.prodMk (hv.prodMk hd)
  have hmap : MapsTo p (closedBall a ρ) (admissibleJets row col M L κ δ) := by
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
    exact ⟨hM w hw, hmet w hw, hv0.trans hlow,
      hd0.trans ((cNorm_fderiv_le _ 0 v).trans hlow), hchar w hw, hminor w hw⟩
  have hout := hb m Ω hΩ hball p hp hmap
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

end JanetCartan.RawPrimary.CorrectionBounds
