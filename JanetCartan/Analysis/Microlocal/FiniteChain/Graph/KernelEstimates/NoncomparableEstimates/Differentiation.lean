module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.FrequencyIntegration

/-!
# Actual derivatives of the explicitly regularized shell kernel

Compact frequency carriers and the primitive two-position symbol support
justify differentiation and Fubini for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral JanetCartan.Localization Retarded.KernelDecay
variable {n r : ℕ}

/-- Joint smoothness uses primitive smoothness alone, without imposing any
frequency-derivative estimate on a smaller-shell mask
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_jointIntegrand_of_factors (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (y : Euclidean n)
    (hA : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)))
    (hi : ContDiff ℝ ∞ (fun ξ => mi (y, ξ))) (ho : ContDiff ℝ ∞ mo)
    (hca : ContDiff ℝ ∞ χA) (hco : ContDiff ℝ ∞ χo)
    (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × JointVariables (Euclidean n) =>
      jointIntegrand backward ρ φ A mi mo χA χo p.1 y p.2) := by
  have ha : ContDiff ℝ ∞ (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) := by
    have he : jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y = fun p =>
        (((χA (ρ • p.2.1) * χo (ρ • p.2.2.2) * mi (y, p.2.2.1)) : ℝ) : ℂ) •
          A p.1.1 p.1.2 (ρ • p.2.1) := by
      funext p
      simp [jointAmplitude]
    rw [he]
    exact (Complex.ofRealCLM.contDiff.comp
      (((hca.comp (contDiff_snd.fst.const_smul ρ)).mul
        (hco.comp (contDiff_snd.snd.snd.const_smul ρ))).mul
        (hi.comp contDiff_snd.snd.fst))).smul hA
  have hw : ContDiff ℝ ∞ (fun p : Euclidean n × JointVariables (Euclidean n) =>
      Complex.exp ((inner ℝ p.1 (ρ • p.2.2.2.2) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.inner ℝ (contDiff_snd.snd.snd.snd.const_smul ρ))).mul contDiff_const)
  have hm : ContDiff ℝ ∞ (fun p : Euclidean n × JointVariables (Euclidean n) =>
      (mo (p.1, p.2.2.2.2) : ℂ)) := Complex.ofRealCLM.contDiff.comp
    (ho.comp (contDiff_fst.prodMk contDiff_snd.snd.snd.snd))
  have hp : ContDiff ℝ ∞ (phaseOscillation (ρ • jointPhase backward φ 0 y)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (hφ.const_smul ρ)).mul contDiff_const)
  have he : (fun p : Euclidean n × JointVariables (Euclidean n) =>
      jointIntegrand backward ρ φ A mi mo χA χo p.1 y p.2) = fun p =>
      (Complex.exp ((inner ℝ p.1 (ρ • p.2.2.2.2) : ℂ) * Complex.I) *
        (1 - (mo (p.1, p.2.2.2.2) : ℂ))) •
      (phaseOscillation (ρ • jointPhase backward φ 0 y) p.2 •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p.2) := by
    funext p
    simpa only [zero_add] using
      jointIntegrand_add_output backward ρ φ A mi mo χA χo 0 y p.1 p.2
  rw [he]
  exact (hw.mul (contDiff_const.sub hm)).smul ((hp.smul ha).comp contDiff_snd)

/-- A literal regularized shell kernel. It retains both base positions and
all three frequency measures and regularizers (`app:ch_regular:eq:chain-tail`). -/
def regularizedShellKernel (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (Kb : Set (Euclidean n × Euclidean n)) (Kξ Kη Kζ : Set (Euclidean n))
    (x y : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  (jointNormalization n * ρ ^ (3 * n)) •
    ∫ p in jointCarrier Kb Kξ Kη Kζ, jointIntegrand backward ρ φ A mi mo χA χo x y p ∂jointMeasure n

set_option maxHeartbeats 400000 in
/-- The shell output integral is exactly the actual output derivative of the
regularized kernel. Compact domination and Fubini are proved from primitive
smoothness and support, never assumed as an operator identity
(`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_regularizedShellKernel_eq (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hKξ : IsCompact Kξ) (hKη : IsCompact Kη) (hKζ : IsCompact Kζ)
    (hA : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)))
    (hi : ContDiff ℝ ∞ (fun ξ => mi (y, ξ))) (ho : ContDiff ℝ ∞ mo)
    (hca : ContDiff ℝ ∞ χA) (hco : ContDiff ℝ ∞ χo)
    (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y))
    (hs : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ Kb)
    (m : ℕ) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m
      (fun t => regularizedShellKernel backward ρ φ A mi mo χA χo Kb Kξ Kη Kζ t y) x v =
      shellOutputIntegral backward ρ φ A mi mo χA χo x y Kξ Kη Kζ m v := by
  let K := jointCarrier Kb Kξ Kη Kζ
  have hK : IsCompact K := isCompact_jointCarrier hKb hKξ hKη hKζ
  let : IsFiniteMeasure ((jointMeasure n).restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hf := contDiff_jointIntegrand_of_factors backward ρ φ A mi mo χA χo y hA hi ho hca hco hφ
  have hg : ContDiff ℝ ∞ (fun t =>
      ∫ p in K, jointIntegrand backward ρ φ A mi mo χA χo t y p ∂jointMeasure n) := by
    rw [← contDiffOn_univ]
    exact JanetCartan.contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ hK
      (subset_univ _) hf.contDiffOn
  change (iteratedFDeriv ℝ m ((jointNormalization n * ρ ^ (3 * n)) •
    (fun t => ∫ p in K, jointIntegrand backward ρ φ A mi mo χA χo t y p ∂jointMeasure n)) x) v = _
  rw [iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (by simp)),
    iteratedFDeriv_compactCarrierIntegral hf hK, smul_apply,
    ContinuousMultilinearMap.integral_apply (integrableOn_outputJet hf hK m x)]
  unfold shellOutputIntegral
  congr 1
  let f : JointVariables (Euclidean n) → Matrix (Fin r) (Fin r) ℂ := fun p =>
    iteratedFDeriv ℝ m (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y p) x v
  have hiJet := integrableOn_outputJet (μ := jointMeasure n) hf hK m x
  have hfint := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Euclidean n)
      (Matrix (Fin r) (Fin r) ℂ) v).integrable_comp hiJet
  change ∫ p in K, f p ∂jointMeasure n = _
  have he : (jointMeasure n).restrict K =
      ((baseMeasure n).restrict Kb).prod ((frequencyMeasure n).restrict (Kξ ×ˢ Kη ×ˢ Kζ)) :=
    (Measure.prod_restrict (μ := baseMeasure n) (ν := frequencyMeasure n) Kb (Kξ ×ˢ Kη ×ˢ Kζ)).symm
  rw [he] at hfint ⊢
  rw [integral_prod_symm f hfint]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hKξ.prod (hKη.prod hKζ)).measurableSet] with w hw
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro b hb
  have hz : A b.1 b.2 (ρ • w.1) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun b : Euclidean n × Euclidean n =>
      A b.1 b.2 (ρ • w.1)) (fun hh => hb (hs w hw hh))
  dsimp only [f]
  rw [← oscillation_smul_outputJetAmplitude,
    outputJetAmplitude_eq_frequencyFactor backward ρ φ A mi mo χA χo x y m v ho, hz,
    smul_zero, smul_zero]

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
