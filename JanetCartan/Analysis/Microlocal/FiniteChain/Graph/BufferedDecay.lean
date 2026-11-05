module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.BufferedJets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Decay

/-!
# Comparable graph decay from the actual chart buffers

This connects the localizer construction to the integration-by-parts estimate
in `app:ch_regular:eq:chain-tail`. Both the gap and an open nonstationary domain
for every differentiated amplitude are derived here. Only primitive phase and
full-symbol grades, low inverse-chart geometry and compact carriers are inputs.
The physical shell decomposition and Sobolev limit assembly are separate steps.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph
open FourierIntegral KernelEstimates JanetCartan.Localization Retarded.HalfSpace
variable {n r : ℕ}

/-- A positive integration-by-parts denominator determined entirely by the
fixed coordinate basis, chart bounds and buffer distance. The factor `1/2`
leaves room for an open domain around every output-jet support
(`app:ch_regular:eq:chain-tail`). -/
def bufferedPhaseGap {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n))) (δ a b : ℝ) : ℝ :=
  ((δ / graphGapConstant a b) / jointDirectionLoss e) ^ 2 / 2

/-- Positivity uses only the low geometric constants and buffer distance
(`app:ch_regular:eq:chain-tail`). -/
theorem bufferedPhaseGap_pos {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < bufferedPhaseGap e δ a b := by
  exact div_pos (sq_pos_of_pos
    (div_pos (div_pos hδ (graphGapConstant_pos ha hb)) (jointDirectionLoss_pos e)))
    (by norm_num)

/-- All actual comparable output derivatives have the paper's graded decay.
The masks may be obtained from `exists_bufferedLocalizers_of_image_envelope`.
Their geometric separation and low chart control produce the gap, including
for the differentiated complement. No kernel bound, transferred-amplitude
bound, or phase-gradient gap is assumed. The losses `s+3*n` and
`m+bo+D.offset` are independent of accuracy; `s` may be negative. Both literal
orientations and the weighted inverse full amplitude are allowed
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_regularizedJointKernel_le_of_buffer
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) (s : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    {I Dφ : Set (Euclidean n × Euclidean n)} {a b δ G : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    (H : if backward then ReverseChartControl φ κ I Dφ a b
      else ForwardChartControl φ κ I Dφ a b)
    {A : FullAmplitude n r} {mi mo : LocalizerSymbol n}
    {χA χo : Euclidean n → ℝ} (x y : Euclidean n)
    (hi : tsupport mi ⊆ I) (ho : ContDiff ℝ ∞ mo)
    (hbuffer : ∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q),
      δ ≤ dist (κ q) q')
    {D : AmplitudeProfiles} {K : Set (JointVariables (Euclidean n))}
    (hgrades : HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K)
    (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y))
    (hK : IsCompact K)
    (hsK : tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K)
    (hDφ : ∀ p ∈ tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y),
      (p.1.1, p.2.1) ∈ Dφ)
    (hupper : ∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G)
    (P : ℕ → ℝ)
    (hp : ∀ p ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bo m q : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hw : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2)‖ ≤ W j)
    (hmo : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ O j * L ^ (j + bo)) :
    ‖iteratedFDeriv ℝ m
        (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v‖ ≤
      (jointNormalization n *
        decayConstant e (bufferedPhaseGap e δ a b) (G + 1) P
          (D.outputJetProfile W O m) q * (jointMeasure n).real K) *
        ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) *
        L ^ ((m + bo) + D.offset) * (L / ρ) ^ q := by
  let F := jointPhase backward φ x y
  have hFx : ContDiff ℝ ∞ F := by
    have he : F = fun p => jointPhase backward φ 0 y p + inner ℝ x p.2.2.2 := by
      funext p
      simpa only [zero_add] using jointPhase_add_output backward φ 0 y x p
    rw [he]
    exact hφ.add (contDiff_const.inner ℝ contDiff_snd.snd.snd)
  have hdf : Continuous (fderiv ℝ F) := hFx.continuous_fderiv (by simp)
  have hsq : Continuous (phaseGradientSquare e F) := by
    unfold phaseGradientSquare
    exact continuous_finsetSum _ fun i _ => (hdf.clm_apply continuous_const).pow 2
  let U := {p | bufferedPhaseGap e δ a b < phaseGradientSquare e F p} ∩
    {p | ‖fderiv ℝ F p‖ < G + 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hsq).inter (isOpen_lt hdf.norm continuous_const)
  have hsU : tsupport (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v) ⊆ U := by
    intro p hp'
    have hs := tsupport_outputJetAmplitude_subset backward ρ φ A mi mo χA χo x y ho m v hp'
    have hg := outputJetAmplitude_jointDerivative_gap backward φ κ ha hb H hi ho hbuffer
      ρ A χA χo x y m v hp' (hDφ p hs)
    have hsqgap := jointDerivative_gap_phaseGradientSquare e F p
      (div_pos hδ (graphGapConstant_pos ha hb)).le hg
    refine ⟨?_, lt_of_le_of_lt (hupper p (hsK hs)) (lt_add_one G)⟩
    have hpos := bufferedPhaseGap_pos e hδ ha hb
    change bufferedPhaseGap e δ a b < phaseGradientSquare e F p
    dsimp only [bufferedPhaseGap] at hpos ⊢
    linarith
  exact norm_iteratedFDeriv_regularizedJointKernel_apply_le backward hρ hL s φ x y
    hgrades ho hφ hU hK hsK e (bufferedPhaseGap_pos e hδ ha hb)
    (fun _ hp' => hp'.1.le) (fun _ hp' => hp'.2.le) P hp hW hO bo m q v hv hw hmo hsU

/-- Comparable kernel constants are chosen before the phase, frequency, scale,
amplitude, and external bases. The fixed smooth output mask and Fourier
character supply their own derivative profiles. Only the full amplitude's
primitive grades and the phase/chart bounds remain as inputs. This is the
comparable piece of `app:ch_regular:eq:chain-tail`, not its Sobolev extension. -/
theorem exists_buffered_comparable_kernel_constants
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ)
    {mi mo : LocalizerSymbol n} {I Ko Oo : Set (Euclidean n × Euclidean n)}
    (hi : tsupport mi ⊆ I) (ho : IsBufferedLocalizer mo Ko Oo)
    (D : AmplitudeProfiles) {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K)
    {a b δ G : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (P : ℕ → ℝ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (φ : Euclidean n → Euclidean n → ℝ)
        (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
        (Dφ : Set (Euclidean n × Euclidean n)),
      (if backward then ReverseChartControl φ κ I Dφ a b
        else ForwardChartControl φ κ I Dφ a b) →
      (∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q), δ ≤ dist (κ q) q') →
      ∀ (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ) (x y : Euclidean n),
      HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K →
      ContDiff ℝ ∞ (jointPhase backward φ 0 y) →
      tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K →
      (∀ p ∈ tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y),
        (p.1.1, p.2.1) ∈ Dφ) →
      (∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
      (∀ p ∈ K, ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j) →
      ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m
          (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v‖ ≤
        C q * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) *
          L ^ (m + D.offset) * (L / ρ) ^ q := by
  obtain ⟨W, hW, hw⟩ := exists_outputJointWave_profile_on_jointCarrier hK
  obtain ⟨O, hO, hmo⟩ := ho.exists_output_mask_profile
  let C := fun q => jointNormalization n *
    decayConstant e (bufferedPhaseGap e δ a b) (G + 1) P (D.outputJetProfile W O m) q *
      (jointMeasure n).real K
  refine ⟨C, fun q => mul_nonneg (mul_nonneg (jointNormalization_nonneg n)
    (decayConstant_nonneg e _ _ P _ (D.outputJetProfile_nonneg hW hO m) q))
      measureReal_nonneg, ?_⟩
  intro ρ L hL hLρ φ κ Dφ H hbuffer A χA χo x y hgrades hφ hsK hDφ hupper hp q v hv
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hm : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ O j * L ^ (j + 0) := by
    intro p _ j
    exact (hmo ρ hρ x (0, p.2.2.2) j).trans
      (le_mul_of_one_le_right (hO j) (one_le_pow₀ hL))
  simpa only [C, Nat.add_zero] using
    norm_iteratedFDeriv_regularizedJointKernel_le_of_buffer e backward
      (zero_lt_one.trans_le hρ) hL s φ κ ha hb hδ H x y hi ho.smooth hbuffer hgrades hφ
      hK hsK hDφ hupper P hp hW hO 0 m q v hv hw hm

end JanetCartan.FiniteChain.Graph
