module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.HighEnvelope.Scaling

/-!
# The complete-complement high envelope

Checked Euclidean Lebesgue L² realization of the low/high split and the
displayed high-envelope estimate in the complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`.

`EnvelopeCutoff.low` is the inverse L² Fourier transform of the given real
smooth cutoff times the actual Fourier transform; `EnvelopeCutoff.high`
is its exact complement. `high_profile_bound` gives the paper's decay
profile from the explicit Euclidean input profile. For cutoffs specified
in physical covectors, use `physicalCovectorCutoff` and
`high_physical_profile_bound`, which retain η = 2πξ.

Conditional inputs: the given bounded smooth cutoff and its support/plateau,
the scale inequalities, and the actual datum's finite Sobolev membership
and quantitative profile. The wave/current-mean producers must supply the
last two analytic inputs to `jc-response-complement`. No torus-to-Euclidean
comparison or unconditional wave construction is claimed here.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement

/-- The concrete decomposition and Sobolev conclusions consumed by the
complete-complement argument of `app:ch_response:thm:response-literal-transfer`.
All numerical norms are accompanied by finite membership proofs. -/
theorem highEnvelope_decomposition {d : ℕ} {Λ B R t p : ℝ}
    (χ : EnvelopeCutoff d Λ B R) (hΛ : 1 ≤ Λ) (_ht : 0 ≤ t) (htp : t ≤ p)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : MemFourierSobolev p f) :
    χ.low f + χ.high f = f ∧
      (∀ s : ℝ, MemFourierSobolev s (χ.low f)) ∧
      MemFourierSobolev p (χ.high f) ∧ MemFourierSobolev t (χ.high f) ∧
      fourierSobolevNorm t (χ.high f) ≤
        (1 + B) * Λ ^ (t - p) * fourierSobolevNorm p f := by
  exact ⟨χ.low_add_high f, fun s ↦ χ.low_mem_all_orders s f,
    (χ.high_sobolev_bound hf).1, χ.high_tail_bound (lt_of_lt_of_le zero_lt_one hΛ) htp hf⟩

end JanetCartan.ResponseTransfer.Complement
