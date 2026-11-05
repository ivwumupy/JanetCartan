module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# The original modulated source

Concrete Euclidean hypotheses for the negative source estimate immediately before
`app:ch_response:eq:response-graded-reduced`. All measures are Lebesgue measures.
The envelope hypotheses use the actual L² Fourier transform and the existing
Euclidean Sobolev weight, with the same normalization as `MemFourierSobolev`.
They apply to complete complex Hilbert targets, including tensor fibers.

The geometry and envelope are inputs, to be constructed by the phase, leading
wave and current-mean producers. No estimate on a residual output is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.SourceNegative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The literal original source in `app:ch_response:prop:response-graded`. -/
def modulatedSource (χ : Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (f : Euclidean n → F) (ρ : ℝ) (x : Euclidean n) : F :=
  χ x • (carrier ρ φ x • f x)

/-- Raw smooth geometry for the source estimate preceding
`app:ch_response:eq:response-graded-reduced`. The gradient gap is required on
the entire fixed support set, and the constants are separate from the slow scale. -/
structure SourceGeometry (χ φ : Euclidean n → ℝ) (S : Set (Euclidean n))
    (c G L : ℝ) (P X : ℕ → ℝ) : Prop where
  cutoff_smooth : ContDiff ℝ ∞ χ
  phase_smooth : ContDiff ℝ ∞ φ
  compact : IsCompact S
  support_subset : tsupport χ ⊆ S
  lower_pos : 0 < c
  lower_lt_upper : c < G
  scale_one_le : 1 ≤ L
  phase_constants_nonneg : ∀ j, 0 ≤ P j
  cutoff_constants_nonneg : ∀ j, 0 ≤ X j
  gradient_lower : ∀ x ∈ S, c ≤ ‖fderiv ℝ φ x‖
  gradient_upper : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ G
  phase_derivatives : ∀ x ∈ S, ∀ j : ℕ, 1 ≤ j →
    ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * L ^ j
  cutoff_derivatives : ∀ x, ∀ j : ℕ,
    ‖iteratedFDeriv ℝ j χ x‖ ≤ X j * L ^ j

/-- Hilbert-valued form of the actual Fourier envelope profile
`app:ch_response:eq:response-graded-source`. For scalar targets its weighted
function is definitionally `Pseudodifferential.weightedL2Fourier`.
Membership is retained separately from the numerical `toReal` bound. -/
structure SobolevEnvelopeBounds (f : Euclidean n → F) (hf : MemLp f 2 volume)
    (A K : ℝ) (C : ℕ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  amplitude_nonneg : 0 ≤ A
  scale_one_le : 1 ≤ K
  constants_nonneg : ∀ p, 0 ≤ C p
  fourier_memLp : ∀ p : ℕ, MemLp (fun ξ ↦
    Pseudodifferential.euclideanSobolevWeight (p : ℝ) ξ •
      (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ) 2 volume
  fourier_bound : ∀ p : ℕ, (eLpNorm (fun ξ ↦
    Pseudodifferential.euclideanSobolevWeight (p : ℝ) ξ •
      (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ) 2 volume).toReal ≤
    C p * A * K ^ p

/-- The carrier agrees with the source-shell phase convention, including the
placement of `i` (`app:ch_response:prop:response-graded`). -/
theorem carrier_eq_phaseOscillation (ρ : ℝ) (φ : Euclidean n → ℝ) :
    carrier ρ φ = Localization.phaseOscillation (fun x ↦ ρ * φ x) := by
  funext x
  simp only [carrier, Localization.phaseOscillation, mul_comm Complex.I]

omit [CompleteSpace F] in
/-- Modulation preserves pointwise norms; the cutoff is the sole L² cost
(`app:ch_response:prop:response-graded`). -/
theorem norm_modulatedSource (χ φ : Euclidean n → ℝ) (f : Euclidean n → F)
    (ρ : ℝ) (x : Euclidean n) :
    ‖modulatedSource χ φ f ρ x‖ = |χ x| * ‖f x‖ := by
  simp [modulatedSource, norm_smul, carrier_eq_phaseOscillation,
    Localization.norm_phaseOscillation, Real.norm_eq_abs]

omit [CompleteSpace F] in
/-- Actual L² membership of the original source, without a pointwise bound on
the envelope (`app:ch_response:prop:response-graded`). -/
theorem modulatedSource_memLp {χ φ : Euclidean n → ℝ} {f : Euclidean n → F}
    (hχ : Continuous χ) (hφ : Continuous φ) (hf : MemLp f 2 volume)
    {B : ℝ} (hB : ∀ x, |χ x| ≤ B) (ρ : ℝ) :
    MemLp (modulatedSource χ φ f ρ) 2 volume := by
  have hc : Continuous (carrier ρ φ) := by
    unfold carrier
    fun_prop
  apply hf.of_le_mul (c := B) (hχ.aestronglyMeasurable.smul
    (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖modulatedSource χ φ f ρ x‖ ≤ B * ‖f x‖
    rw [norm_modulatedSource]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- The zeroth actual Sobolev bound gives the envelope's L² bound, with no
power of `K` (`app:ch_response:eq:response-graded-source`). -/
theorem SobolevEnvelopeBounds.norm_toLp_le {f : Euclidean n → F}
    {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) : ‖hf.toLp f‖ ≤ C 0 * A := by
  simpa only [Nat.cast_zero, Pseudodifferential.euclideanSobolevWeight_zero,
    one_smul, ← Lp.norm_def, Lp.norm_fourier_eq, pow_zero, mul_one] using h.fourier_bound 0

omit [CompleteSpace F] in
/-- L² control of the original source from the actual envelope L² class
(`app:ch_response:prop:response-graded`). -/
theorem norm_modulatedSource_toLp_le {χ φ : Euclidean n → ℝ} {f : Euclidean n → F}
    (hf : MemLp f 2 volume) {ρ B : ℝ}
    (hs : MemLp (modulatedSource χ φ f ρ) 2 volume) (hB : ∀ x, |χ x| ≤ B) :
    ‖hs.toLp (modulatedSource χ φ f ρ)‖ ≤ B * ‖hf.toLp f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hs.coeFn_toLp, hf.coeFn_toLp] with x hsx hfx
  rw [hsx, hfx, norm_modulatedSource]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- The stated cutoff jet bound supplies its uniform zeroth-order bound
(`app:ch_response:prop:response-graded`). -/
theorem SourceGeometry.cutoff_bound {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    (x : Euclidean n) : |χ x| ≤ X 0 := by
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using
    g.cutoff_derivatives x 0

omit [CompleteSpace F] in
/-- The raw geometry and actual Sobolev envelope imply L² membership of the
original source (`app:ch_response:prop:response-graded`). -/
theorem source_memLp {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} (hf : MemLp f 2 volume) (ρ : ℝ) :
    MemLp (modulatedSource χ φ f ρ) 2 volume :=
  modulatedSource_memLp g.cutoff_smooth.continuous g.phase_smooth.continuous hf
    g.cutoff_bound ρ

omit [CompleteSpace F] in
/-- The actual original source is integrable because its cutoff is compactly
supported; this does not require the envelope to be L¹
(`app:ch_response:prop:response-graded`). -/
theorem source_integrable {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} (hf : Continuous f) (ρ : ℝ) :
    Integrable (modulatedSource χ φ f ρ) volume := by
  have hχ : HasCompactSupport χ := g.compact.of_isClosed_subset
    (isClosed_tsupport _) g.support_subset
  have hc : Continuous (carrier ρ φ) := by
    have hφ := g.phase_smooth.continuous
    unfold carrier
    fun_prop
  exact (g.cutoff_smooth.continuous.smul (hc.smul hf)).integrable_of_hasCompactSupport
    hχ.smul_right

/-- Sharp L² control without a Sobolev embedding loss, for the annular term in
`source_negative_sobolev_with_l2` (`app:ch_response:prop:response-graded`). -/
theorem source_norm_le {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (ρ : ℝ) :
    ‖(source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)‖ ≤ X 0 * C 0 * A := by
  exact (norm_modulatedSource_toLp_le hf (source_memLp g hf ρ) g.cutoff_bound).trans
    ((mul_le_mul_of_nonneg_left h.norm_toLp_le (g.cutoff_constants_nonneg 0)).trans_eq
      (mul_assoc _ _ _).symm)

omit [CompleteSpace F] in
/-- The Fourier identification for the literal source retains the fixed
physical `2π` frequency dilation (`app:ch_response:prop:response-graded`). -/
theorem source_physicalFourier_eq {χ φ : Euclidean n → ℝ} {f : Euclidean n → F}
    (ρ : ℝ) (ξ : Euclidean n) :
    Localization.physicalFourierIntegral volume (modulatedSource χ φ f ρ)
      (InnerProductSpace.toDual ℝ (Euclidean n) ξ) =
    𝓕 (modulatedSource χ φ f ρ) ((2 * Real.pi)⁻¹ • ξ) :=
  Localization.physicalFourierIntegral_eq_fourier _ _

end JanetCartan.ResponseTransfer.SourceNegative
