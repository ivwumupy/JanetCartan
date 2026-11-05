module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Pointwise

/-!
# Actual output derivatives of the graph integrand

Translation in the output factors out its Fourier character for both literal
orientations. The resulting exact all-order jet keeps the output mask's base
derivatives. This is the input to the remaining output-jet grade estimate for
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral JanetCartan.Localization
variable {n r : ℕ}

/-- The output translation identity is identical for the forward and literal
reverse graphs (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointPhase_add_output (backward : Bool) (φ : Euclidean n → Euclidean n → ℝ)
    (x y t : Euclidean n) (p : JointVariables (Euclidean n)) :
    jointPhase backward φ (x + t) y p =
      jointPhase backward φ x y p + inner ℝ t p.2.2.2 := by
  cases backward <;>
    simp only [jointPhase, forwardPhase, reversePhase, Bool.false_eq_true,
      ↓reduceIte, inner_sub_left, inner_add_left] <;> ring

/-- The matrix integrand before integration, with every primitive factor
retained (`app:ch_regular:eq:joint-kernel-phase`). -/
def jointIntegrand (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  phaseOscillation (ρ • jointPhase backward φ x y) p •
    jointAmplitude ρ A mi mo χA χo x y p

/-- The actual output jet, demodulated by the original literal phase
(`app:ch_regular:eq:chain-tail`). -/
def outputJetAmplitude (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
    (p : JointVariables (Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  phaseOscillation (-(ρ • jointPhase backward φ x y)) p •
    iteratedFDeriv ℝ m (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y p) x v

/-- Exact recovery of the differentiated integrand. This identity assumes no
output-derivative estimate (`app:ch_regular:eq:chain-tail`). -/
theorem oscillation_smul_outputJetAmplitude (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
    (p : JointVariables (Euclidean n)) :
    phaseOscillation (ρ • jointPhase backward φ x y) p •
      outputJetAmplitude backward ρ φ A mi mo χA χo x y m v p =
    iteratedFDeriv ℝ m (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y p) x v := by
  simp only [outputJetAmplitude, phaseOscillation, Pi.neg_apply, Complex.ofReal_neg,
    neg_mul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

/-- Output dependence consists exactly of a Fourier character and the
complementary output symbol, including the latter's base dependence
(`app:ch_regular:eq:chain-tail`). -/
theorem jointIntegrand_add_output (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y t : Euclidean n) (p : JointVariables (Euclidean n)) :
    jointIntegrand backward ρ φ A mi mo χA χo (x + t) y p =
      (Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I) *
        (1 - (mo (x + t, p.2.2.2) : ℂ))) •
      (phaseOscillation (ρ • jointPhase backward φ x y) p •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) := by
  simp only [jointIntegrand, jointAmplitude, phaseOscillation, jointPhase_add_output,
    Pi.smul_apply, smul_eq_mul, inner_smul_right, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one, sub_zero,
    mul_one, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add, smul_smul]
  congr 1
  ring

/-- Exact all-order output jet as a scalar output-symbol jet acting on the
full two-position amplitude. No amplitude position or output mask derivative
is dropped (`app:ch_regular:eq:chain-tail`). -/
theorem outputJetAmplitude_eq_symbolJet (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
    (hmo : ContDiff ℝ ∞ mo) (p : JointVariables (Euclidean n)) :
    outputJetAmplitude backward ρ φ A mi mo χA χo x y m v p =
      iteratedFDeriv ℝ m (fun t =>
        Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I) *
          (1 - (mo (x + t, p.2.2.2) : ℂ))) 0 v •
      jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p := by
  let g : Euclidean n → ℂ := fun t =>
    Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I) *
      (1 - (mo (x + t, p.2.2.2) : ℂ))
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hm : ContDiff ℝ ∞ (fun t : Euclidean n => mo (x + t, p.2.2.2)) :=
    hmo.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const)
  have hw : ContDiff ℝ ∞ (fun t : Euclidean n =>
      Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((hcoe.comp (contDiff_id.inner ℝ contDiff_const)).mul contDiff_const)
  have hg : ContDiff ℝ ∞ g := hw.mul (contDiff_const.sub (hcoe.comp hm))
  have he : (fun t => jointIntegrand backward ρ φ A mi mo χA χo (x + t) y p) =
      fun t => g t • (phaseOscillation (ρ • jointPhase backward φ x y) p •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) := by
    funext t
    exact jointIntegrand_add_output backward ρ φ A mi mo χA χo x y t p
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun t => jointIntegrand backward ρ φ A mi mo χA χo t y p) m x 0
  rw [add_zero, he, iteratedFDeriv_smul_const_apply (hg.contDiffAt.of_le (by simp))] at ht
  unfold outputJetAmplitude
  rw [← ht]
  change phaseOscillation (-(ρ • jointPhase backward φ x y)) p •
    (iteratedFDeriv ℝ m g 0 v • (phaseOscillation (ρ • jointPhase backward φ x y) p •
      jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p)) = _
  rw [smul_comm _ (iteratedFDeriv ℝ m g 0 v)]
  simp only [phaseOscillation, Pi.neg_apply, Complex.ofReal_neg, neg_mul,
    smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rfl

/-- Rescaling the output increment extracts exactly `ρ^m`; the remaining jet
keeps the inverse-frequency scaling in the output mask's base derivatives.
This supplies the frequency count for the future jet-grade bound
(`app:ch_regular:eq:chain-tail`). -/
theorem outputJetAmplitude_eq_scaled_symbolJet (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
    (hmo : ContDiff ℝ ∞ mo) (p : JointVariables (Euclidean n)) :
    outputJetAmplitude backward ρ φ A mi mo χA χo x y m v p =
      ρ ^ m • (iteratedFDeriv ℝ m (fun t =>
        Complex.exp ((inner ℝ t p.2.2.2 : ℝ) * Complex.I) *
          (1 - (mo (x + ρ⁻¹ • t, p.2.2.2) : ℂ))) 0 v •
      jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) := by
  let g : Euclidean n → ℂ := fun t =>
    Complex.exp ((inner ℝ t p.2.2.2 : ℝ) * Complex.I) *
      (1 - (mo (x + ρ⁻¹ • t, p.2.2.2) : ℂ))
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hm : ContDiff ℝ ∞ (fun t : Euclidean n => mo (x + ρ⁻¹ • t, p.2.2.2)) :=
    hmo.comp ((contDiff_const.add (contDiff_id.const_smul ρ⁻¹)).prodMk contDiff_const)
  have hw : ContDiff ℝ ∞ (fun t : Euclidean n =>
      Complex.exp ((inner ℝ t p.2.2.2 : ℝ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((hcoe.comp (contDiff_id.inner ℝ contDiff_const)).mul contDiff_const)
  have hg : ContDiff ℝ ∞ g := hw.mul (contDiff_const.sub (hcoe.comp hm))
  have he : (fun t => Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I) *
      (1 - (mo (x + t, p.2.2.2) : ℂ))) = fun t => g (ρ • t) := by
    funext t
    simp only [g, inv_smul_smul₀ hρ, inner_smul_right, real_inner_smul_left]
  rw [outputJetAmplitude_eq_symbolJet backward ρ φ A mi mo χA χo x y m v hmo p,
    he, iteratedFDeriv_comp_const_smul ρ (hg.of_le (by simp))]
  simp only [smul_zero, smul_apply]
  exact smul_assoc _ _ _

end JanetCartan.FiniteChain.Graph.KernelEstimates
