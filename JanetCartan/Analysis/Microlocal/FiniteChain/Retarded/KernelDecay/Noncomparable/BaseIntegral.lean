module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.BaseIntegral.Phase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.BaseIntegral.Amplitude
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Tangential

/-!
# Uniform common-base decay for noncomparable retarded frequencies

For `app:ch_regular:lem:finite-chain`, the two normalized covectors are parameters
throughout the integration by parts. The phase is exactly the literal lower or
upper phase. Only the normal and common-base variables are integrated, and the
integration-by-parts field is tangential to the half-space boundary.

The constants in `exists_uniform_integral_bound` precede the frequency and grade
scales, both primitive weights, both external bases, and both normalized
covectors. Its consumer is the noncomparable retarded shell construction in
`KernelDecay/Noncomparable`: that construction must still insert the actual
symbol factors and integrate the Fourier measures to obtain
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance : (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)

/-- The constant for common-base integration depends only on the primitive
carriers, primitive profiles and fixed normalized radii
(`app:ch_regular:eq:chain-tail`). -/
def baseDecayConstant (e : OrthonormalBasis ι ℝ E) (Kα Kβ : Set (ℝ × E))
    (c M : ℝ) (A B : ℕ → ℝ) (q : ℕ) : ℝ :=
  HalfSpace.decayConstant (baseDirections e) (c ^ 2 / 4) (5 * M)
    (fun _ => 5 * M) (weightProfile A B) q *
    volume.real (Prod.fst '' weightCarrier Kα Kβ) *
    volume.real (Prod.snd '' weightCarrier Kα Kβ)

/-- Nonnegativity of the uniform constant (`app:ch_regular:eq:chain-tail`). -/
theorem baseDecayConstant_nonneg (e : OrthonormalBasis ι ℝ E) (Kα Kβ : Set (ℝ × E))
    (c M : ℝ) {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (q : ℕ) :
    0 ≤ baseDecayConstant e Kα Kβ c M A B q :=
  mul_nonneg (mul_nonneg
    (HalfSpace.decayConstant_nonneg _ _ _ _ _ (weightProfile_nonneg hA hB) q)
    measureReal_nonneg) measureReal_nonneg

/-- The common-base half-space estimate from primitive weight bounds and
noncomparable normalized frequencies (`app:ch_regular:lem:finite-chain`).
The open integration region is the whole base space: the fixed-covector gap
holds everywhere. Neither covector nor the half-space jump is differentiated.
The external bases have no restriction at all. -/
theorem norm_halfSpaceIntegral_le (e : OrthonormalBasis ι ℝ E)
    {Kα Kβ : Set (ℝ × E)} (hKα : IsCompact Kα) (hKβ : IsCompact Kβ)
    {c M : ℝ} (hc : 0 < c) {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (q : ℕ) (upper : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    {α β : ℝ × E → ℝ} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j * L ^ j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j * L ^ j)
    (xi xo : ℝ × E) (w : (ℝ × E) × (ℝ × E))
    (hlarge : c ≤ max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2))
    (hsmall : max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2) ≤ M)
    (hsep : 2 * frequencySize w.2.1 w.2.2 ≤ frequencySize w.1.1 w.1.2 ∨
      2 * frequencySize w.1.1 w.1.2 ≤ frequencySize w.2.1 w.2.2) :
    ‖HalfSpace.halfSpaceOscillatoryIntegral volume ρ
      (basePhase upper xi xo w) (weightAmplitude upper α β)‖ ≤
      baseDecayConstant e Kα Kβ c M A B q * (L / ρ) ^ q := by
  have hs : tsupport (weightAmplitude upper α β) ⊆ weightCarrier Kα Kβ ∩ univ := by
    simpa using tsupport_weightAmplitude_subset upper α β hKα hKβ hsα hsβ
  have h := HalfSpace.norm_halfSpaceOscillatoryIntegral_le_tangential
    (μ := (volume : Measure (ℝ × E))) (P := fun _ => 5 * M)
    (A := weightProfile A B) (G := 5 * M) (δ := c ^ 2 / 4)
    isOpen_univ (isCompact_weightCarrier hKα hKβ) (baseDirections e)
    (basePhase upper xi xo w) (weightAmplitude upper α β)
    (contDiff_basePhase upper xi xo w) (contDiff_weightAmplitude upper hα hβ) hs
    (show 0 < c ^ 2 / 4 by positivity) hL hρ
    (fun d _ z _ => basePhase_gradient_gap e upper xi xo w hc.le hlarge hsep d z)
    (fun d _ z _ => norm_fderiv_basePhase_le upper xi xo w hsmall (d, z))
    (weightProfile_nonneg hA hB) 0 q
    (fun x _ j => norm_iteratedFDeriv_fderiv_basePhase_le upper xi xo w hL hsmall x j)
    (fun x _ j => by
      simpa only [Nat.add_zero] using
        norm_iteratedFDeriv_weightAmplitude_le upper hα hβ hA hB hL ha hb x j)
  simpa only [baseDecayConstant, pow_zero, mul_one] using h

/-- Uniform literal oscillatory integral bound, with the constant chosen before
both scales, weights, external bases and normalized covectors. This is the
common-base input consumed by the noncomparable shell proof of
`app:ch_regular:eq:chain-tail`; Fourier symbol bounds and integration over the
two Fourier measures remain the consumer's responsibility. -/
theorem exists_uniform_integral_bound (e : OrthonormalBasis ι ℝ E)
    {Kα Kβ : Set (ℝ × E)} (hKα : IsCompact Kα) (hKβ : IsCompact Kβ)
    {c : ℝ} (hc : 0 < c) (M : ℝ) {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (upper : Bool) (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
      ∀ α β : ℝ × E → ℝ, ContDiff ℝ ∞ α → ContDiff ℝ ∞ β →
      tsupport α ⊆ Kα → tsupport β ⊆ Kβ →
      (∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j * L ^ j) →
      (∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j * L ^ j) →
      ∀ (xi xo : ℝ × E) (w : (ℝ × E) × (ℝ × E)),
      c ≤ max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2) →
      max (frequencySize w.2.1 w.2.2) (frequencySize w.1.1 w.1.2) ≤ M →
      (2 * frequencySize w.2.1 w.2.2 ≤ frequencySize w.1.1 w.1.2 ∨
        2 * frequencySize w.1.1 w.1.2 ≤ frequencySize w.2.1 w.2.2) →
      ‖∫ d in Ici (0 : ℝ), ∫ b : ℝ × E,
        Complex.exp (((ρ * literalPhase upper xi xo (d, b, w) : ℝ) : ℂ) * Complex.I) *
          weightAmplitude upper α β (d, b)‖ ≤ C * (L / ρ) ^ q := by
  refine ⟨baseDecayConstant e Kα Kβ c M A B q,
    baseDecayConstant_nonneg e Kα Kβ c M hA hB q, ?_⟩
  intro upper ρ L hρ hL α β hα hβ hsα hsβ ha hb xi xo w hlarge hsmall hsep
  have hs := tsupport_weightAmplitude_subset upper α β hKα hKβ hsα hsβ
  have hcompact : HasCompactSupport (weightAmplitude upper α β) :=
    (isCompact_weightCarrier hKα hKβ).of_isClosed_subset (isClosed_tsupport _) hs
  have h := norm_halfSpaceIntegral_le e hKα hKβ hc hA hB q upper hρ hL
    hα hβ hsα hsβ ha hb xi xo w hlarge hsmall hsep
  rw [HalfSpace.halfSpaceOscillatoryIntegral_eq_integral_slice
    (contDiff_basePhase upper xi xo w) (contDiff_weightAmplitude upper hα hβ) hcompact] at h
  simpa only [Localization.phaseOscillation, Pi.smul_apply, smul_eq_mul, basePhase] using h

end JanetCartan.FiniteChain.Retarded.KernelDecay.BaseIntegral
