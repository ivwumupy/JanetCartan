module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Output

/-!
# Three-frequency integration after physical-base decay

The explicit regularized shell output integral in `app:ch_regular:eq:chain-tail`
contains the actual output derivatives of the literal graph integrand. Its
bound is derived only from primitive full-symbol, cutoff and mask grades.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace Retarded.KernelDecay
variable {n r : ℕ}

/-- All three normalized Fourier measures; their physical Jacobian is
`ρ^(3*n)`, even when integration by parts uses `R`
(`app:ch_regular:eq:joint-kernel-phase`). -/
def frequencyMeasure (n : ℕ) : Measure (Euclidean n × Euclidean n × Euclidean n) :=
  (volume : Measure (Euclidean n)).prod (volume.prod volume)

instance frequencyMeasure_isAddHaarMeasure : (frequencyMeasure n).IsAddHaarMeasure := by
  let : ((volume : Measure (Euclidean n)).prod (volume : Measure (Euclidean n))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

instance frequencyMeasure_sFinite : SFinite (frequencyMeasure n) :=
  inferInstanceAs (SFinite ((volume : Measure (Euclidean n)).prod (volume.prod volume)))

/-- Each of the three frequency carriers contributes its measure, including
the source shoulder (`app:ch_regular:eq:chain-tail`). -/
theorem frequencyMeasure_real_prod (Kξ Kη Kζ : Set (Euclidean n)) :
    (frequencyMeasure n).real (Kξ ×ˢ Kη ×ˢ Kζ) =
      volume.real Kξ * volume.real Kη * volume.real Kζ := by
  simp only [frequencyMeasure, measureReal_prod_prod]
  ring

/-- Explicit regularized shell integral of the actual output jet. Sharp
frequency carriers are harmless since only the physical bases are used for
integration by parts. This definition asserts no operator or regularization
limit identity (`app:ch_regular:eq:chain-tail`). -/
def shellOutputIntegral (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (Kξ Kη Kζ : Set (Euclidean n)) (m : ℕ) (v : Fin m → Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  (jointNormalization n * ρ ^ (3 * n)) •
    ∫ w in Kξ ×ˢ Kη ×ˢ Kζ, ∫ b,
      iteratedFDeriv ℝ m (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y (b,w)) x v
      ∂baseMeasure n ∂frequencyMeasure n

/-- Shell estimate with all three Fourier measures and every actual output
jet. The offsets `ba+bc+bi+(m+bo)+bA` are fixed before `q`. Only primitive
symbol derivatives and mask base derivatives occur; none of the three
frequencies is differentiated. Both orientations use the full amplitude,
including the weighted inverse of `Graph.Basic`. The parent must instantiate
the normalized phase gap and phase grades (`app:ch_regular:eq:chain-tail`). -/
theorem norm_shellOutputIntegral_le {ι : Type*} [Fintype ι]
    (backward : Bool) {ρ R L S So I Ca Co δ G : ℝ}
    (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (hL : 1 ≤ L) (hS : 0 ≤ S) (hSo : 1 ≤ So)
    (hI : 0 ≤ I) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co) (hδ : 0 < δ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hKξ : IsCompact Kξ) (hKη : IsCompact Kη) (hKζ : IsCompact Kζ)
    (U : (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n))
    (hU : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, IsOpen (U w))
    (e : ι → Euclidean n × Euclidean n) (P B W O : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (ba bc bi bo bA m q : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ho : ContDiff ℝ ∞ mo)
    (hφ : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      ContDiffOn ℝ ∞ (normalizedBasePhase backward ρ R φ x y w) (U w))
    (hA : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ContDiffOn ℝ ∞
      (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) (U w))
    (hsU : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U w)
    (hsK : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ Kb)
    (hgap : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      δ ≤ phaseGradientSquare e (normalizedBasePhase backward ρ R φ x y w) z)
    (hupper : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ G)
    (hp : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P j * L ^ j)
    (ha : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ j,
      ‖iteratedFDeriv ℝ j (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) z‖ ≤
        S * B j * L ^ (j + bA))
    (hi : ∀ η ∈ Kη, ‖mi (y, η)‖ ≤ I * L ^ bi)
    (hca : ∀ ξ ∈ Kξ, ‖χA (ρ • ξ)‖ ≤ Ca * L ^ ba)
    (hco : ∀ ζ ∈ Kζ, ‖χo (ρ • ζ)‖ ≤ Co * L ^ bc)
    (hw : ∀ ζ ∈ Kζ, ∀ j, ‖iteratedFDeriv ℝ j
      (fun t => outputJointWave (t, (ρ / R) • ζ)) 0‖ ≤ W j)
    (hb : ∀ ζ ∈ Kζ, ∀ j,
      ‖iteratedFDeriv ℝ j (fun t => mo (t, ζ)) x‖ ≤ So * O j * L ^ (j + bo)) :
    ‖shellOutputIntegral backward ρ φ A mi mo χA χo x y Kξ Kη Kζ m v‖ ≤
      (jointNormalization n * decayConstant e δ G P B q * (baseMeasure n).real Kb *
        volume.real Kξ * volume.real Kη * volume.real Kζ *
          (Ca * Co * I * derivativeConvolution W (fun j => 1 + O j) m)) *
      (ρ ^ (3 * n) * R ^ m * S * So) * L ^ (ba + bc + bi + (m + bo) + bA) * (L / R) ^ q := by
  let D := Ca * Co * I * derivativeConvolution W (fun j => 1 + O j) m
  let T := (decayConstant e δ G P B q * (baseMeasure n).real Kb) * S * L ^ bA * (L / R) ^ q
  let F := D * (R ^ m * So) * L ^ (ba + bc + bi + (m + bo))
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (decayConstant_nonneg e δ G P B hB q) measureReal_nonneg) hS)
      (pow_nonneg (zero_le_one.trans hL) _))
      (pow_nonneg (div_nonneg (zero_le_one.trans hL) (zero_le_one.trans hR)) _)
  have hF : 0 ≤ F := by
    dsimp [F, D]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hCo) hI)
      (derivativeConvolution_nonneg hW (fun j => by linarith [hO j]) _))
      (mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (zero_le_one.trans hSo)))
      (pow_nonneg (zero_le_one.trans hL) _)
  have hint : ‖∫ w in Kξ ×ˢ Kη ×ˢ Kζ, ∫ b,
      iteratedFDeriv ℝ m (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y (b,w)) x v
      ∂baseMeasure n ∂frequencyMeasure n‖ ≤
      F * T * (frequencyMeasure n).real (Kξ ×ˢ Kη ×ˢ Kζ) := by
    apply norm_setIntegral_le_of_norm_le_const (hKξ.prod (hKη.prod hKζ)).measure_lt_top
    intro w hw'
    rw [integral_outputJet_eq_frequencyFactor backward ρ φ A mi mo χA χo x y m v ho, norm_smul]
    exact mul_le_mul
      (norm_outputFrequencyFactor_le ρ hR hL hSo hI hCa hCo mi mo χA χo x y ho hW hO
        bi ba bc bo m v hv w (hi _ hw'.2.1) (hca _ hw'.1) (hco _ hw'.2.2)
        (hw _ hw'.2.2) (hb _ hw'.2.2))
      (norm_baseIntegral_le backward ρ (zero_lt_one.trans_le hR) (zero_le_one.trans hL) hS hδ
        φ A x y w (hU w hw') hKb e P B hB bA q (hφ w hw') (hA w hw')
        (hsU w hw') (hsK w hw') (hgap w hw') (hupper w hw') (hp w hw') (ha w hw'))
      (norm_nonneg _) hF
  unfold shellOutputIntegral
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ _))]
  apply (mul_le_mul_of_nonneg_left hint
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ _))).trans_eq
  rw [frequencyMeasure_real_prod]
  dsimp [F, T, D]
  simp only [pow_add]
  ring

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
