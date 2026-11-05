module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputGrades

/-!
# Differentiating the regularized graph integral

Common compact carriers supply domination for actual output derivatives in
`app:ch_regular:eq:chain-tail`. This concerns the explicitly regularized integral;
identification with the operator composition and removal of regularizers belong
to `Graph.KernelLimits`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral Retarded.KernelDecay JanetCartan.Localization
variable {n r : ℕ}

/-- Joint smoothness of the actual integrand, from the primitive phase and
factors. Both literal orientations have the same external Fourier character
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_jointIntegrand_joint (backward : Bool) {ρ S L : ℝ}
    (φ : Euclidean n → Euclidean n → ℝ) {A : FullAmplitude n r}
    {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ} (y : Euclidean n)
    {D : AmplitudeProfiles} {Ka : Set (JointVariables (Euclidean n))}
    (ha : HasAmplitudeGrades D ρ S L A mi (fun _ => 0) χA χo 0 y Ka)
    (ho : ContDiff ℝ ∞ mo) (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × JointVariables (Euclidean n) =>
      jointIntegrand backward ρ φ A mi mo χA χo p.1 y p.2) := by
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
  exact (hw.mul (contDiff_const.sub hm)).smul
    ((hp.smul ha.contDiff_jointAmplitude).comp contDiff_snd)

/-- The same primitive carrier works for every external output base
(`app:ch_regular:eq:chain-tail`). -/
theorem jointIntegrand_eq_zero_off_carrier (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (y : Euclidean n)
    {K : Set (JointVariables (Euclidean n))}
    (hs : tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K)
    (x : Euclidean n) (p : JointVariables (Euclidean n)) (hp : p ∉ K) :
    jointIntegrand backward ρ φ A mi mo χA χo x y p = 0 := by
  have hz := image_eq_zero_of_notMem_tsupport (fun h => hp (hs h))
  have he := jointIntegrand_add_output backward ρ φ A mi mo χA χo 0 y x p
  simpa only [zero_add, hz, smul_zero] using he

/-- Every output derivative passes through all five measures, retaining the
three Fourier normalizations and frequency Jacobians. Domination follows from
primitive smoothness and compact support (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_regularizedJointKernel_apply_eq_integral
    (backward : Bool) {ρ S L : ℝ} (φ : Euclidean n → Euclidean n → ℝ)
    {A : FullAmplitude n r} {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ}
    (x y : Euclidean n) {D : AmplitudeProfiles} {Ka : Set (JointVariables (Euclidean n))}
    (ha : HasAmplitudeGrades D ρ S L A mi (fun _ => 0) χA χo 0 y Ka)
    (ho : ContDiff ℝ ∞ mo) (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y))
    {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K)
    (hs : tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K)
    (m : ℕ) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v =
      (jointNormalization n * ρ ^ (3 * n)) •
        ∫ p, phaseOscillation (ρ • jointPhase backward φ x y) p •
          outputJetAmplitude backward ρ φ A mi mo χA χo x y m v p ∂jointMeasure n := by
  have hf := contDiff_jointIntegrand_joint backward φ y ha ho hφ
  have hz := jointIntegrand_eq_zero_off_carrier backward ρ φ A mi mo χA χo y hs
  have hi := contDiff_integral_commonCarrier (μ := jointMeasure n) hf hK hz
  change (iteratedFDeriv ℝ m ((jointNormalization n * ρ ^ (3 * n)) •
    (fun t => ∫ p, jointIntegrand backward ρ φ A mi mo χA χo t y p ∂jointMeasure n)) x) v = _
  rw [iteratedFDeriv_const_smul_apply (hi.contDiffAt.of_le (by simp)),
    iteratedFDeriv_integral_commonCarrier hf hK hz, smul_apply,
    ContinuousMultilinearMap.integral_apply
      (integrable_outputJet_commonCarrier (μ := jointMeasure n) hf hK hz m x)]
  simp only [oscillation_smul_outputJetAmplitude]

end JanetCartan.FiniteChain.Graph.KernelEstimates
