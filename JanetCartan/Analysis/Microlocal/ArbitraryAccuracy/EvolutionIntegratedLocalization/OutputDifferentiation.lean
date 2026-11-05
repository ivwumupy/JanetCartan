module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Differentiation

/-!
# Output differentiation of the bounded elapsed integral

For `app:ch_regular:eq:chain-tail`, all output derivatives pass through the
actual bounded elapsed integral and all five graph integration variables.
The common compact carrier supplies domination and measurability. The genuine
boundary is retained as a restricted measure; the lower buffer and physical
output slab remove the artificial upper endpoint via `CompactKernels`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

section Integrand

variable (backward : Bool) (ρ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
  (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
  (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (y : Euclidean (d + 1))

/-- The literal compact-frequency integrand with elapsed extension cutoff,
before imposing the half-space. Consumer: output differentiation in
`app:ch_regular:eq:chain-tail`. -/
def cutElapsedIntegrand (x : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) : Matrix (Fin q) (Fin q) ℂ :=
  θ p.1 • jointIntegrand backward ρ (elapsedPhase Ψ p.1)
    (orientedElapsedAmplitude backward b χout χsource β p.1) mi mo χA χo x y p.2

private theorem cutElapsedIntegrand_factor (x : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) :
    cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y x p =
      (Complex.exp ((inner ℝ x (ρ • p.2.2.2.2) : ℂ) * Complex.I) *
        (1 - (mo (x, p.2.2.2.2) : ℂ))) •
        (phaseOscillation (ρ • jointElapsedPhase backward Ψ 0 y) p •
          (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
            χA χo 0 y p)) := by
  unfold cutElapsedIntegrand
  rw [show x = 0 + x by simp, jointIntegrand_add_output]
  simp only [zero_add]
  rw [smul_comm (θ p.1), smul_comm (θ p.1)]
  rfl

/-- Joint output/integration-variable smoothness follows from primitive
phase, amplitude and output-symbol smoothness. It is enough to control the
phase and masked amplitude at the zero external output base
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_cutElapsedIntegrand_joint
    (ho : ContDiff ℝ ∞ mo)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ 0 y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p)) :
    ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × (ℝ × JointVariables (Euclidean (d + 1))) ↦
      cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y p.1 p.2) := by
  simp_rw [cutElapsedIntegrand_factor]
  have hw : ContDiff ℝ ∞
      (fun p : Euclidean (d + 1) × (ℝ × JointVariables (Euclidean (d + 1))) ↦
        Complex.exp ((inner ℝ p.1 (ρ • p.2.2.2.2.2) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.inner ℝ (contDiff_snd.snd.snd.snd.snd.const_smul ρ))).mul contDiff_const)
  have hm : ContDiff ℝ ∞
      (fun p : Euclidean (d + 1) × (ℝ × JointVariables (Euclidean (d + 1))) ↦
        (mo (p.1, p.2.2.2.2.2) : ℂ)) := Complex.ofRealCLM.contDiff.comp
    (ho.comp (contDiff_fst.prodMk contDiff_snd.snd.snd.snd.snd))
  have hp : ContDiff ℝ ∞ (phaseOscillation (ρ • jointElapsedPhase backward Ψ 0 y)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (hF.const_smul ρ)).mul contDiff_const)
  exact (hw.mul (contDiff_const.sub hm)).smul ((hp.smul ha).comp contDiff_snd)

private theorem cutElapsedIntegrand_eq_zero_off_carrier
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K)
    (x : Euclidean (d + 1)) (p : ℝ × JointVariables (Euclidean (d + 1))) (hp : p ∉ K) :
    cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y x p = 0 := by
  have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hs h))
  simp only [cutElapsedIntegrand_factor, hz, smul_zero]

private theorem cutElapsedIntegrand_outputJet (ho : ContDiff ℝ ∞ mo)
    (x : Euclidean (d + 1)) (m : ℕ) (v : Fin m → Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) :
    iteratedFDeriv ℝ m
        (fun t ↦ cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y t p) x v =
      phaseOscillation (ρ • jointElapsedPhase backward Ψ x y) p •
        cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v p := by
  have hc : ContDiff ℝ ∞ (fun t ↦ jointIntegrand backward ρ (elapsedPhase Ψ p.1)
      (orientedElapsedAmplitude backward b χout χsource β p.1) mi mo χA χo t y p.2) := by
    have he := funext (fun t ↦ jointIntegrand_add_output backward ρ (elapsedPhase Ψ p.1)
      (orientedElapsedAmplitude backward b χout χsource β p.1) mi mo χA χo 0 y t p.2)
    simp only [zero_add] at he
    rw [he]
    apply ContDiff.smul_const
    apply ContDiff.mul
    · exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
        (contDiff_id.inner ℝ contDiff_const)).mul contDiff_const)
    · exact contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (ho.comp (contDiff_id.prodMk contDiff_const)))
  unfold cutElapsedIntegrand
  rw [iteratedFDeriv_const_smul_apply' (a := θ p.1) (hc.contDiffAt.of_le (by simp)), smul_apply]
  rw [← oscillation_smul_outputJetAmplitude backward ρ _ _ mi mo χA χo x y m v p.2]
  exact smul_comm _ _ _

end Integrand

/-- All output derivatives of the actual bounded elapsed integral are the
half-space integral of the actual demodulated output jet. Common compact
support discharges every domination, measurability and differentiation
interchange. The physical lower buffer removes the artificial upper endpoint;
the boundary at zero remains in the measure, for both orientations
(`app:ch_regular_base:eq:fixed-time-representation`, `app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_integral_regularizedElapsedKernel_apply_eq_halfSpace
    (backward : Bool) (ρ Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    {a T : ℝ} (hb : ∀ t s u η, s ≤ a → b t s u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (hF : ∀ t, ContDiff ℝ ∞ (jointElapsedPhase backward Ψ t y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K) (m : ℕ) (v : Fin m → Euclidean (d + 1)) :
    iteratedFDeriv ℝ m (fun t ↦ ∫ r in Icc 0 Δ,
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) x v =
      (jointNormalization (d + 1) * ρ ^ (3 * (d + 1))) •
        ∫ p in Ici (0 : ℝ) ×ˢ (univ : Set (JointVariables (Euclidean (d + 1)))),
          phaseOscillation (ρ • jointElapsedPhase backward Ψ x y) p •
            cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v p
          ∂(volume.prod (jointMeasure (d + 1))) := by
  let f := fun z : Euclidean (d + 1) × (ℝ × JointVariables (Euclidean (d + 1))) ↦
    cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y z.1 z.2
  let μ := (volume.prod (jointMeasure (d + 1))).restrict
    (Ici (0 : ℝ) ×ˢ (univ : Set (JointVariables (Euclidean (d + 1)))))
  have hf : ContDiff ℝ ∞ f := contDiff_cutElapsedIntegrand_joint
    backward ρ Ψ b χout χsource β mi mo χA χo θ y ho (hF 0) ha
  have hz : ∀ t p, p ∉ K → f (t, p) = 0 :=
    cutElapsedIntegrand_eq_zero_off_carrier backward ρ Ψ b χout χsource β mi mo χA χo θ y hs
  have he : (fun t ↦ ∫ r in Icc 0 Δ,
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) =
      (jointNormalization (d + 1) * ρ ^ (3 * (d + 1))) • (fun t ↦ ∫ p, f (t, p) ∂μ) := by
    funext t
    have ham : (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
        θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo t y p) =
        fun p ↦ (1 - (mo (t, p.2.2.2.2) : ℂ)) •
          (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
            χA χo 0 y p) := by
      funext p
      simp only [jointElapsedAmplitude, jointAmplitude, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_one, sub_zero, mul_one,
        smul_smul]
      congr 1
      ring
    have hat : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
        θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo t y p) := by
      rw [ham]
      exact (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (ho.comp (contDiff_const.prodMk contDiff_snd.snd.snd.snd)))).smul ha
    have hst : HasCompactSupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
        θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo t y p) := by
      rw [ham]
      exact hK.of_isClosed_subset (isClosed_tsupport _) ((tsupport_smul_subset_right _ _).trans hs)
    rw [integral_regularizedElapsedKernel_eq_halfSpace backward ρ Δ Ψ b χout χsource β
      mi mo χA χo t y θ hθ hb hout hslab (hF t) hat hst]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun p ↦ (smul_comm _ _ _).symm)
  have hi := contDiff_integral_commonCarrier (μ := μ) hf hK hz
  rw [he, iteratedFDeriv_const_smul_apply (a := (jointNormalization (d + 1) * ρ ^ (3 * (d + 1))))
    (hi.contDiffAt.of_le (by simp)),
    iteratedFDeriv_integral_commonCarrier hf hK hz, smul_apply,
    ContinuousMultilinearMap.integral_apply (integrable_outputJet_commonCarrier hf hK hz m x)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun p ↦
    cutElapsedIntegrand_outputJet backward ρ Ψ b χout χsource β mi mo χA χo θ y ho x m v p)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
