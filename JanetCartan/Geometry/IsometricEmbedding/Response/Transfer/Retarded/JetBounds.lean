module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Carrier transfer in the actual completed jet norms

For `app:ch_response:eq:fixed-factor-transfer`, these estimates follow from the
proved integral-energy theorem, including every derivative of both weights.
Parameter differentiation holds the frequency and the actual operators fixed.
The norms here are those of `RetardedSobolev.Spaces.Ambient`. Comparing them
with the local Sobolev scale used by `HasEnvelopeProfile` is still a separate
representation obligation; this module does not assume that comparison.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.RetardedCutoffs

open RetardedSobolev RetardedSobolev.Spaces

variable {d : ℕ} (W : RetardedCutoffs d)

/-- Uniform norm bounds for the literal demodulated factors, obtained directly
from the integral-energy theorem of `app:ch_osc:prop:osc-retarded-tube`.
The constant precedes the frequency, covector and input. -/
theorem exists_demodulated_jet_norm_bounds (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (ζ : Euclidean d) (f : Test d),
      ‖ofTest s volume (W.demodulatedLower ρ ζ f)‖ ≤ C * ‖ofTest s volume f‖ ∧
      ‖ofTest s volume (W.demodulatedUpper ρ ζ f)‖ ≤ C * ‖ofTest s volume f‖ := by
  obtain ⟨D, hD, hb⟩ := retardedTest_energy_bounds W.lowerEndpoint W.upperEndpoint
    W.endpoints_le s W.input W.output W.input_smooth W.output_smooth
    W.input_compact W.output_compact W.input_support_strip W.output_support_strip
  refine ⟨Real.sqrt (D * (Fintype.card (JetIndex d s) : ℝ)), Real.sqrt_nonneg _, ?_⟩
  intro ρ ζ f
  simp only [demodulatedLower_eq, demodulatedUpper_eq]
  exact ⟨jetMap_bound_of_energy_bound volume volume W.lower hD (fun f ↦ (hb f).1) f,
    jetMap_bound_of_energy_bound volume volume W.upper hD (fun f ↦ (hb f).2) f⟩

/-- Envelope profiles in the actual Cartesian jet completion are preserved,
with no loss in the power of `K` (`app:ch_response:eq:fixed-factor-transfer`).
This is a jet-norm statement, not yet a `HasEnvelopeProfile` assertion in the
local restriction scale. -/
theorem demodulated_jet_profile {ι : Type*} (f : ι → Test d)
    (ρ : ι → ℝ) (ζ : ι → Euclidean d) (A K : ι → ℝ)
    (hf : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      ‖ofTest s volume (f i)‖ ≤ C * A i * K i ^ s) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      ‖ofTest s volume (W.demodulatedLower (ρ i) (ζ i) (f i))‖ ≤
          C * A i * K i ^ s ∧
      ‖ofTest s volume (W.demodulatedUpper (ρ i) (ζ i) (f i))‖ ≤
          C * A i * K i ^ s := by
  intro s
  obtain ⟨D, hD, hbound⟩ := W.exists_demodulated_jet_norm_bounds s
  obtain ⟨C, hC, hf⟩ := hf s
  refine ⟨D * C, mul_nonneg hD hC, fun i ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left (hf i) hD
  rw [show D * (C * A i * K i ^ s) = D * C * A i * K i ^ s by ring] at h
  exact ⟨((hbound (ρ i) (ζ i) (f i)).1).trans h,
    ((hbound (ρ i) (ζ i) (f i)).2).trans h⟩

private theorem norm_parameter_derivative_le {p s k : ℕ}
    (T : Ambient d s →L[ℂ] Ambient d s) (f g : Euclidean p → Ambient d s)
    (he : ∀ c, g c = T (f c)) (c : Euclidean p)
    (hf : ContDiffAt ℝ (k : ℕ∞ω) f c) :
    ‖iteratedFDeriv ℝ k g c‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ k f c‖ := by
  have hg : g = T.restrictScalars ℝ ∘ f := funext he
  rw [hg]
  simpa only [ContinuousLinearMap.norm_restrictScalars] using
    (T.restrictScalars ℝ).norm_iteratedFDeriv_comp_left hf le_rfl

/-- Any finite number of parameter derivatives passes through the same fixed
retarded factors in their completed jet norms
(`app:ch_response:thm:response-literal-transfer`). The carrier covector may vary
arbitrarily: it cancels identically before differentiation. The input hypothesis
concerns only differentiability of the given envelope in the indicated norm. -/
theorem exists_demodulated_parameter_norm_bounds (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p k : ℕ) (ρ : ℝ) (ζ : Euclidean p → Euclidean d)
      (f : Euclidean p → Test d) (c : Euclidean p),
      ContDiffAt ℝ (k : ℕ∞ω) (fun c ↦ ofTest s volume (f c)) c →
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedLower ρ (ζ c) (f c))) c‖ ≤
          C * ‖iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f c)) c‖ ∧
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedUpper ρ (ζ c) (f c))) c‖ ≤
          C * ‖iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f c)) c‖ := by
  obtain ⟨C, hC, L, U, hL, hU, heL, heU, _⟩ :=
    exists_retarded_sobolev_extensions W.lowerEndpoint W.upperEndpoint W.endpoints_le
      s W.input W.output W.input_smooth W.output_smooth W.input_compact W.output_compact
      W.input_support_strip W.output_support_strip
  refine ⟨C, hC, ?_⟩
  intro p k ρ ζ f c hf
  constructor
  · apply (norm_parameter_derivative_le L _ _ (fun c ↦ ?_) c hf).trans
      (mul_le_mul_of_nonneg_right hL
        (norm_nonneg (iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f c)) c)))
    simpa only [demodulatedLower_eq, lower] using (heL (f c)).symm
  · apply (norm_parameter_derivative_le U _ _ (fun c ↦ ?_) c hf).trans
      (mul_le_mul_of_nonneg_right hU
        (norm_nonneg (iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f c)) c)))
    simpa only [demodulatedUpper_eq, upper] using (heU (f c)).symm

/-- The finite parameter profile has total grade `s + k`, with constants
independent of the parameter, family index and frequency
(`app:ch_response:thm:response-literal-transfer`). It applies on any fixed compact
parameter box, and in fact on any set where the displayed input bounds hold.
The frequency and cutoffs are fixed during each parameter differentiation. -/
theorem demodulated_parameter_jet_profile {ι : Type*} {p : ℕ}
    (q : ℕ) (B : Set (Euclidean p)) (f : ι → Euclidean p → Test d)
    (ρ : ι → ℝ) (ζ : Euclidean p → Euclidean d) (A K : ι → ℝ)
    (hsmooth : ∀ s i c, c ∈ B →
      ContDiffAt ℝ (q : ℕ∞ω) (fun c ↦ ofTest s volume (f i c)) c)
    (hf : ∀ s k, k ≤ q → ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
      ‖iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f i c)) c‖ ≤
        C * A i * K i ^ (s + k)) :
    ∀ s k, k ≤ q → ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedLower (ρ i) (ζ c) (f i c))) c‖ ≤
          C * A i * K i ^ (s + k) ∧
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedUpper (ρ i) (ζ c) (f i c))) c‖ ≤
          C * A i * K i ^ (s + k) := by
  intro s k hk
  obtain ⟨D, hD, hb⟩ := W.exists_demodulated_parameter_norm_bounds s
  obtain ⟨C, hC, hf⟩ := hf s k hk
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro i c hc
  have h := hb p k (ρ i) ζ (f i) c ((hsmooth s i c hc).of_le (by exact_mod_cast hk))
  have hbound := mul_le_mul_of_nonneg_left (hf i c hc) hD
  rw [show D * (C * A i * K i ^ (s + k)) = D * C * A i * K i ^ (s + k) by ring]
    at hbound
  exact ⟨h.1.trans hbound, h.2.trans hbound⟩

end JanetCartan.ResponseTransfer.RetardedCutoffs
