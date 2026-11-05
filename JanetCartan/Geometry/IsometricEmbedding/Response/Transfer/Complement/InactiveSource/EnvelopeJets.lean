module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.EnvelopeJets.FourierNorm
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets

/-!
# Inactive-source envelope jets from the actual Sobolev profile

The all-order profile in `app:ch_response:thm:response-literal-transfer`
implies the pointwise amplitude bounds required by
`app:ch_osc:prop:osc-source-shell`, with the single fixed loss `d + 1`.
The consumers are `InactiveSource.norm_masked_carrier_fourier_of_gap` and
`InactiveSource.masked_carrier_spectral_tail`, applied with amplitude
`A * K ^ (d + 1)`.

The finite-order embedding below uses the proved Fourier-moment,
reconstruction and inverse-differentiation lemmas in `SourceNegative`.
`EnvelopeJets.FourierNorm` identifies their weighted L² input with the
existing coordinate-based vector Fourier Sobolev norm, on the same
Euclidean Lebesgue measure. No pointwise or tail bound is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "VL2" => Lp F 2 (volume : Measure E)

/-- Sobolev embedding for the actual vector Fourier norm: the order `j + d + 1`
controls the `j`-th pointwise Fréchet derivative. This proves the analytic
implication used to apply `app:ch_osc:prop:osc-source-shell` in
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_le_vectorFourierSobolevNorm
    {f : E → F} (hcont : Continuous f) (hf : MemLp f 2 volume) (j : ℕ)
    (hs : MemVectorFourierSobolev ((j + (d + 1) : ℕ) : ℝ) (hf.toLp f)) (x : E) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ SourceNegative.envelopeJetConstant d j *
      vectorFourierSobolevNorm ((j + (d + 1) : ℕ) : ℝ) (hf.toLp f) := by
  have hmom (k : ℕ) (hk : k ≤ j) :
      Integrable (fun ξ ↦ ‖ξ‖ ^ k * ‖(𝓕 (hf.toLp f) : VL2) ξ‖) := by
    have hlow : MemVectorFourierSobolev ((k + (d + 1) : ℕ) : ℝ) (hf.toLp f) := by
      intro i
      exact (hs i).mono (by exact_mod_cast Nat.add_le_add_right hk (d + 1))
    exact (SourceNegative.envelope_moment_integrable_and_le
      (Lp.aestronglyMeasurable _) k (memLp_weighted_vectorFourier _ _ hlow)).1
  have hi : Integrable (fun ξ ↦ (𝓕 (hf.toLp f) : VL2) ξ) := by
    apply (integrable_norm_iff (Lp.aestronglyMeasurable _)).mp
    simpa only [pow_zero, one_mul] using hmom 0 (Nat.zero_le j)
  have hjet := SourceNegative.norm_iteratedFDeriv_fourierInv_le_moment
    (fun ξ ↦ (𝓕 (hf.toLp f) : VL2) ξ) j (Lp.aestronglyMeasurable _) hmom x
  rw [← SourceNegative.eq_fourierInv_l2_of_continuous hcont hf hi] at hjet
  have hb := (SourceNegative.envelope_moment_integrable_and_le
    (Lp.aestronglyMeasurable _) j (memLp_weighted_vectorFourier _ _ hs)).2
  rw [eLpNorm_weighted_vectorFourier _ _ hs] at hb
  exact hjet.trans ((mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (2 * Real.pi) ^ j)).trans_eq (by
      dsimp [SourceNegative.envelopeJetConstant]
      ring))

/-- The uniform jet constants for the profile in
`app:ch_response:thm:response-literal-transfer`. They use only the dimension,
derivative order and the single profile constant `C (j + d + 1)`. -/
def envelopeJetProfileConstant (d : ℕ) (C : ℕ → ℝ) (j : ℕ) : ℝ :=
  SourceNegative.envelopeJetConstant d j * max 0 (C (j + (d + 1)))

/-- Nonnegativity needed by the two inactive-source kernel estimates in
`app:ch_osc:prop:osc-source-shell`. -/
theorem envelopeJetProfileConstant_nonneg (d : ℕ) (C : ℕ → ℝ) (j : ℕ) :
    0 ≤ envelopeJetProfileConstant d C j :=
  mul_nonneg (SourceNegative.envelopeJetConstant_nonneg d j) (le_max_left _ _)

/-- The actual all-order vector Sobolev profile produces the pointwise
envelope input to `norm_masked_carrier_fourier_of_gap` and
`masked_carrier_spectral_tail`, with amplitude `A * K ^ (d + 1)`.
The exponent loss is fixed before the requested derivative or tail order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_iteratedFDeriv_le_envelope_profile
    {f : E → F} (hcont : Continuous f) (hf : MemLp f 2 volume)
    {C : ℕ → ℝ} {A K : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K)
    (hmem : ∀ p : ℕ, MemVectorFourierSobolev (p : ℝ) (hf.toLp f))
    (hbound : ∀ p : ℕ, vectorFourierSobolevNorm (p : ℝ) (hf.toLp f) ≤
      C p * A * K ^ p) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j f x‖ ≤
      envelopeJetProfileConstant d C j * ((A * K ^ (d + 1)) * K ^ j) := by
  have hE := SourceNegative.envelopeJetConstant_nonneg d j
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  calc
    _ ≤ SourceNegative.envelopeJetConstant d j *
        vectorFourierSobolevNorm ((j + (d + 1) : ℕ) : ℝ) (hf.toLp f) :=
      norm_iteratedFDeriv_le_vectorFourierSobolevNorm hcont hf j (hmem _) x
    _ ≤ SourceNegative.envelopeJetConstant d j * (C (j + (d + 1)) * A *
        K ^ (j + (d + 1))) := mul_le_mul_of_nonneg_left (hbound _) hE
    _ ≤ SourceNegative.envelopeJetConstant d j * (max 0 (C (j + (d + 1))) * A *
        K ^ (j + (d + 1))) := by
      gcongr
      exact le_max_right _ _
    _ = _ := by
      simp only [envelopeJetProfileConstant, pow_add]
      ring

/-- Uniform all-order jets for smooth compactly supported vector envelopes in
`app:ch_response:thm:response-literal-transfer`. L² membership is derived from
smoothness and compact support. The constants are chosen before `f`, `A`, `K`,
and even before the support; the fixed loss `d + 1` supplies the envelope
hypothesis of `app:ch_osc:prop:osc-source-shell`. -/
theorem exists_envelope_jet_profile (d r : ℕ) (C : ℕ → ℝ) :
    ∃ J : ℕ → ℝ, (∀ j, 0 ≤ J j) ∧
      ∀ (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℂ (Fin r))
        (hsmooth : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
        (A K : ℝ), 0 ≤ A → 1 ≤ K →
        let hf : MemLp f 2 volume := hsmooth.continuous.memLp_of_hasCompactSupport hcompact
        (∀ p : ℕ, MemVectorFourierSobolev (p : ℝ) (hf.toLp f)) →
        (∀ p : ℕ, vectorFourierSobolevNorm (p : ℝ) (hf.toLp f) ≤ C p * A * K ^ p) →
        ∀ j x, ‖iteratedFDeriv ℝ j f x‖ ≤ J j * ((A * K ^ (d + 1)) * K ^ j) := by
  refine ⟨envelopeJetProfileConstant d C, envelopeJetProfileConstant_nonneg d C, ?_⟩
  intro f hsmooth hcompact A K hA hK hf hmem hbound j x
  exact norm_iteratedFDeriv_le_envelope_profile hsmooth.continuous hf hA hK hmem hbound j x

end JanetCartan.ResponseTransfer.Complement.InactiveSource
