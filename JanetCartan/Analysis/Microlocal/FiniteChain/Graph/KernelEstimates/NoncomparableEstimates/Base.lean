module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputGrades

/-!
# Physical-base integration with three frozen graph frequencies

For `app:ch_regular:eq:chain-tail`, the normalization of the input mask is `ρ`,
whereas the integration gain uses the larger physical radius `R`. Only the two
positions of the full symbol are differentiated. The parent supplies the gap
and phase grades from the noncomparable geometry construction.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace
variable {n r : ℕ}

/-- The two physical Lebesgue measures in `app:ch_regular:eq:joint-kernel-phase`. -/
def baseMeasure (n : ℕ) : Measure (Euclidean n × Euclidean n) :=
  (volume : Measure (Euclidean n)).prod volume

instance baseMeasure_isAddHaarMeasure : (baseMeasure n).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

instance baseMeasure_sFinite : SFinite (baseMeasure n) :=
  inferInstanceAs (SFinite ((volume : Measure (Euclidean n)).prod volume))

/-- The literal phase normalized by the larger radius, leaving all three
covectors at the original input normalization (`app:ch_regular:eq:chain-tail`). -/
def normalizedBasePhase (backward : Bool) (ρ R : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (b : Euclidean n × Euclidean n) : ℝ :=
  (ρ / R) * jointPhase backward φ x y (b, w)

/-- Restoring the large parameter gives exactly the original phase, without
any homogeneity assumption (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem scaled_normalizedBasePhase (backward : Bool) (ρ : ℝ) {R : ℝ} (hR : R ≠ 0)
    (φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) :
    R • normalizedBasePhase backward ρ R φ x y w =
      fun b => ρ * jointPhase backward φ x y (b, w) := by
  funext b
  simp only [Pi.smul_apply, smul_eq_mul, normalizedBasePhase]
  field_simp

/-- Freeze the frequencies and integrate the full two-position symbol. This is
an actual oscillatory integral, with the phase and matrix amplitude of the
joint kernel (`app:ch_regular:eq:chain-tail`). -/
def baseIntegral (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y : Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  ∫ b, phaseOscillation (fun b => ρ * jointPhase backward φ x y (b, w)) b •
    A b.1 b.2 (ρ • w.1) ∂baseMeasure n

/-- Physical-base integration gives `L/R` per integration, independently of
all ratios between the three frequencies. The amplitude hypotheses are only
primitive full-symbol derivatives, including both positions. The gap and
higher phase grades are the precise inputs of the larger-gap producer;
`S` may be any fixed real symbol power (`app:ch_regular:eq:chain-tail`). -/
theorem norm_baseIntegral_le {ι : Type*} [Fintype ι]
    (backward : Bool) (ρ : ℝ) {R L S δ G : ℝ}
    (hR : 0 < R) (hL : 0 ≤ L) (hS : 0 ≤ S) (hδ : 0 < δ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y : Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n)
    {U K : Set (Euclidean n × Euclidean n)} (hU : IsOpen U) (hK : IsCompact K)
    (e : ι → Euclidean n × Euclidean n) (P B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (b q : ℕ)
    (hφ : ContDiffOn ℝ ∞ (normalizedBasePhase backward ρ R φ x y w) U)
    (hA : ContDiffOn ℝ ∞ (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) U)
    (hsU : tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U)
    (hsK : tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ K)
    (hgap : ∀ z ∈ U, δ ≤ phaseGradientSquare e (normalizedBasePhase backward ρ R φ x y w) z)
    (hupper : ∀ z ∈ U, ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ G)
    (hp : ∀ z ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P j * L ^ j)
    (ha : ∀ z ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) z‖ ≤
        S * B j * L ^ (j + b)) :
    ‖baseIntegral backward ρ φ A x y w‖ ≤
      (decayConstant e δ G P B q * (baseMeasure n).real K) * S * L ^ b * (L / R) ^ q := by
  have h := norm_scaled_vector_integral_le (μ := baseMeasure n) hU hK e
    (normalizedBasePhase backward ρ R φ x y w)
    (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1))
    hφ hA hsU hsK hδ hS hL hR hgap hupper hB b q
    (fun z hz j hj => hp z (hsK hz) j hj) (fun z hz j => ha z (hsK hz) j)
  simpa only [scaled_normalizedBasePhase backward ρ hR.ne', baseIntegral] using h

/-- The frozen scalar factor of the actual output derivative, keeping the
input mask at `ρ` normalization and both frequency regularizers
(`app:ch_regular:eq:chain-tail`). -/
def outputFrequencyFactor (ρ : ℝ) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (m : ℕ) (v : Fin m → Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n) : ℂ :=
  iteratedFDeriv ℝ m (fun t =>
    Complex.exp ((inner ℝ t (ρ • w.2.2) : ℂ) * Complex.I) *
      (1 - (mo (x + t, w.2.2) : ℂ))) 0 v *
    ((χA (ρ • w.1) : ℂ) * (χo (ρ • w.2.2) : ℂ) * (mi (y, w.2.1) : ℂ))

/-- Exact factorization of every output jet. No frequency differentiation or
bound on a transferred amplitude is used (`app:ch_regular:eq:chain-tail`). -/
theorem outputJetAmplitude_eq_frequencyFactor (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (m : ℕ) (v : Fin m → Euclidean n) (ho : ContDiff ℝ ∞ mo)
    (b : Euclidean n × Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n) :
    outputJetAmplitude backward ρ φ A mi mo χA χo x y m v (b, w) =
      outputFrequencyFactor ρ mi mo χA χo x y m v w • A b.1 b.2 (ρ • w.1) := by
  rw [outputJetAmplitude_eq_symbolJet backward ρ φ A mi mo χA χo x y m v ho]
  simp only [jointAmplitude, sub_zero, mul_one, Complex.ofReal_mul, smul_smul,
    outputFrequencyFactor]

/-- The actual output derivative integrated over the physical bases factors
into a frequency-only scalar and the full-symbol oscillatory integral
(`app:ch_regular:eq:chain-tail`). -/
theorem integral_outputJet_eq_frequencyFactor (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (m : ℕ) (v : Fin m → Euclidean n) (ho : ContDiff ℝ ∞ mo)
    (w : Euclidean n × Euclidean n × Euclidean n) :
    (∫ b, iteratedFDeriv ℝ m
      (fun t => jointIntegrand backward ρ φ A mi mo χA χo t y (b,w)) x v ∂baseMeasure n) =
      outputFrequencyFactor ρ mi mo χA χo x y m v w • baseIntegral backward ρ φ A x y w := by
  simp_rw [← oscillation_smul_outputJetAmplitude,
    outputJetAmplitude_eq_frequencyFactor backward ρ φ A mi mo χA χo x y m v ho,
    smul_comm _ (outputFrequencyFactor ρ mi mo χA χo x y m v w)]
  rw [integral_smul]
  rfl

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
