module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Differentiation

/-!
# Pointwise decay of actual graph kernel output derivatives

This proves the comparable-frequency analytic implication for
`app:ch_regular:eq:chain-tail`. The exact gradient gap is an input of the
buffered-localizer producer; no kernel, transferred-amplitude or operator
bound is assumed. Noncomparable-frequency summation remains a separate step.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace
variable {n r : ℕ}

/-- Actual output derivatives of the five-variable joint integral obey the
paper's grade, for both literal graph orientations and any real full-symbol
order `s`. The losses `s+3*n` and `m+bo+D.offset` are fixed independently of
integration order `q`. Compact support and primitive grades produce all
integrability, product, and transposed-field estimates. The remaining geometric
premise is the exact gap on the differentiated amplitude support, supplied by
the parent's buffered-localizer construction (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_regularizedJointKernel_apply_le
    {ι : Type*} [Fintype ι] (backward : Bool) {ρ L : ℝ}
    (hρ : 0 < ρ) (hL : 1 ≤ L) (s : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) {A : FullAmplitude n r}
    {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ} (x y : Euclidean n)
    {D : AmplitudeProfiles} {U K : Set (JointVariables (Euclidean n))}
    (ha : HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K)
    (ho : ContDiff ℝ ∞ mo) (hφ : ContDiff ℝ ∞ (jointPhase backward φ 0 y))
    (hU : IsOpen U) (hK : IsCompact K)
    (hsK : tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K)
    (e : ι → JointVariables (Euclidean n)) {δ G : ℝ} (hδ : 0 < δ)
    (hgap : ∀ p ∈ U, δ ≤ phaseGradientSquare e (jointPhase backward φ x y) p)
    (hupper : ∀ p ∈ U, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G)
    (P : ℕ → ℝ)
    (hp : ∀ p ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bo m q : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hw : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2)‖ ≤ W j)
    (hb : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ O j * L ^ (j + bo))
    (hsU : tsupport (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v) ⊆ U) :
    ‖iteratedFDeriv ℝ m (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v‖ ≤
      (jointNormalization n * decayConstant e δ G P (D.outputJetProfile W O m) q *
        (jointMeasure n).real K) * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) *
          L ^ ((m + bo) + D.offset) * (L / ρ) ^ q := by
  have hs := (tsupport_outputJetAmplitude_subset backward ρ φ A mi mo χA χo x y ho m v).trans hsK
  have hφx : ContDiff ℝ ∞ (jointPhase backward φ x y) := by
    have he : jointPhase backward φ x y = fun p =>
        jointPhase backward φ 0 y p + inner ℝ x p.2.2.2 := by
      funext p
      simpa only [zero_add] using jointPhase_add_output backward φ 0 y x p
    rw [he]
    exact hφ.add (contDiff_const.inner ℝ contDiff_snd.snd.snd)
  have h := norm_scaled_vector_integral_le (μ := jointMeasure n) hU hK e
    (jointPhase backward φ x y) (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v)
    hφx.contDiffOn (contDiff_outputJetAmplitude backward hρ.ne' φ x y ha ho m v).contDiffOn
    hsU hs hδ (mul_nonneg (pow_nonneg hρ.le _) (Real.rpow_pos_of_pos hρ s).le)
    (zero_le_one.trans hL) hρ hgap hupper (D.outputJetProfile_nonneg hW hO m)
    ((m + bo) + D.offset) q
    (fun p hp' j hj => hp p (hs hp') j hj)
    (fun p hp' j => norm_iteratedFDeriv_outputJetAmplitude_le backward hρ hL φ x y
      ha ho hW hO bo m v hv p (hs hp') (hw p (hs hp')) (hb p (hs hp')) j)
  rw [iteratedFDeriv_regularizedJointKernel_apply_eq_integral backward φ x y ha ho hφ hK hsK,
    norm_smul, Real.norm_of_nonneg
      (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))]
  apply (mul_le_mul_of_nonneg_left h
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))).trans_eq
  rw [Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_natCast, Real.rpow_natCast]
  ring

end JanetCartan.FiniteChain.Graph.KernelEstimates
