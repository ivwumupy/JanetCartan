module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LeadingInputs

/-!
# Regularity of the same full-modulation primary atom

Instantiate the canonical reconstruction with the published full phase,
leading covector and orthogonal correction. The scalar smoothness and
nonzero nullvectors below are conclusions of the actual finite leading
constructor, not a new successful-wave interface. The raw integral consumer
uses these results on its shifted frequency buffer.

Sources: `app:ch_waves:eq:WKB-W`, `app:ch_waves:thm:individual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

/-- The literal displacement polynomial of the SAME full-modulation atom,
with the original `τ`, `τ²` and `τ³` terms
(`app:ch_waves:eq:exact-W-amplitude`). -/
def fullDisplacementAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin N) :=
  canonicalDisplacementAmplitude F τ (fun p ↦ phase T Q p.1 p.2)
    (fun p ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2))))
    (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2))) (w.1, w.2.2)

/-- Full phase smoothness with the carrier label retained. This is inherited
from the SAME Hamilton chart (`app:ch_waves:eq:joint-tame`). -/
theorem contDiffOn_fullPhase (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (fun w ↦ phase T Q w.1 w.2.2) Ω :=
  ((phase_smooth T Q).mono
    (Metric.ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius))).comp
        (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase

/-- Joint smoothness of the actual full primary atom follows from the
retained leading outputs. No correction or ambient smoothness premise is
added (`app:ch_waves:thm:wkb`, `app:ch_waves:thm:individual`). -/
theorem contDiffOn_fullPrimaryAtom_of_leading_outputs (τ : ℝ)
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) :
    ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2)) Ω := by
  have ha := (euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn
    (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα)
  have hb := contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero
  have ht := contDiffOn_joint_completedVariationComplex_zero_of_isOpen (n := n) (N := N) (Z := Euclidean 3 × Euclidean (n - 1)) (F := F)
    (b := fun w ↦ twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
      (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
      (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1)
    hΩ hspace hF (contDiffOn_joint_twoTermWave
      (S := fun w ↦ phase T Q w.1 w.2.2)
      (b₀ := fun w ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r w))
      (b₁ := fullCorrectionCovector T Q F row col Φ Y r)
      τ⁻¹ (contDiffOn_fullPhase T Q hphase) ha hb) hi hrank
  simpa only [fullPrimaryAtom, canonicalAtom] using ht

/-- The actual ambient atom has its exact three-power displacement
polynomial on the original domain (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem fullPrimaryAtom_eq_of_leading_outputs {τ : ℝ} (hτ : τ ≠ 0)
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2) =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        fullDisplacementAmplitude T Q F row col Φ Y r τ w := by
  have hd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → E}
      (hf : ContDiffOn ℝ ∞ f Ω) : DifferentiableAt ℝ (fun x ↦ f (x, w.2)) w.1 :=
    (((hf.contDiffAt (hΩ.mem_nhds hw)).comp w.1
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  exact canonicalAtom_eq F hτ (hd (contDiffOn_fullPhase T Q hphase))
    (hd ((euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn
      (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα)))
    (hd (contDiffOn_fullCorrectionCovector_of_leading_outputs
      T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero))

/-- The same literal displacement amplitude is jointly smooth, including
the carrier and free covector variables (`app:ch_waves:eq:joint-tame`). -/
theorem contDiffOn_fullDisplacementAmplitude_of_leading_outputs {τ : ℝ} (hτ : τ ≠ 0)
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) :
    ContDiffOn ℝ ∞ (fullDisplacementAmplitude T Q F row col Φ Y r τ) Ω := by
  have hc : ContDiffOn ℝ ∞
      (fun w ↦ Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ))) Ω :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_fullPhase T Q hphase).div_const τ))).cexp
  apply (hc.smul (contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero)).congr
  intro w hw
  change fullDisplacementAmplitude T Q F row col Φ Y r τ w =
    Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
      fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2)
  rw [fullPrimaryAtom_eq_of_leading_outputs T Q F row col Φ Y r hτ
    hΩ hspace hphase hF hi hα hnonzero hw, smul_smul, ← Complex.exp_add]
  simp

end JanetCartan.RawPrimary
