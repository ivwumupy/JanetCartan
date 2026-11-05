module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Fourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Vector envelopes for the complete complement

The literal Euclidean vector L² split in the complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. Scalar cutoff estimates are
transferred through the proved coordinate isometry with no dimension loss.
`EnvelopeCutoff.vectorLow_eq_fourierInv` identifies the split with the actual
vector Fourier multiplier, and `paperL2FourierTransform_vectorLow_zero_outside`
supplies the physical low-support premise of the forward and reverse estimates.

`vectorFourierSobolevScale` is on this same L² space; its levels and member norms
are exactly the existing vector Fourier Sobolev memberships and norms. The
wave/current-mean source profiles and the full graph estimates are still inputs
to the parent complete-complement construction, not conclusions of this module.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.Pseudodifferential
namespace JanetCartan.ResponseTransfer.Complement
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "VL2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)

/-- Exact vector split and high estimate in
`app:ch_response:thm:response-literal-transfer`, with every finite membership. -/
theorem highEnvelope_vector_decomposition {Λ B R t p : ℝ}
    (χ : EnvelopeCutoff d Λ B R) (hΛ : 0 < Λ) (htp : t ≤ p)
    (f : VL2) (hf : MemVectorFourierSobolev p f) :
    χ.vectorLow f + χ.vectorHigh f = f ∧
      (∀ s : ℝ, MemVectorFourierSobolev s (χ.vectorLow f)) ∧
      ‖χ.vectorLow f‖ ≤ B * ‖f‖ ∧
      MemVectorFourierSobolev p (χ.vectorHigh f) ∧
      MemVectorFourierSobolev t (χ.vectorHigh f) ∧
      vectorFourierSobolevNorm t (χ.vectorHigh f) ≤
        (1 + B) * Λ ^ (t - p) * vectorFourierSobolevNorm p f :=
  ⟨χ.vectorLow_add_vectorHigh f, fun s ↦ χ.vectorLow_mem_all_orders s f,
    χ.norm_vectorLow_le f, (χ.vectorHigh_sobolev_bound hf).1,
    χ.vectorHigh_tail_bound hΛ htp hf⟩

/-- The physical-covector split supplies exactly the source-side obligations
of the forward/reverse low estimates and `completeComplement_observations`.
The explicit 2π factor is retained in the high bound
(`app:ch_response:thm:response-literal-transfer`). -/
theorem highEnvelope_vector_physical_decomposition {r : ℕ} {Λ B R t p : ℝ}
    (χ : EnvelopeCutoff d Λ B R) (hΛ : 0 < Λ) (htp : t ≤ p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E))
    (hf : MemVectorFourierSobolev p f) :
    χ.physicalCovectorCutoff.vectorLow f + χ.physicalCovectorCutoff.vectorHigh f = f ∧
      (∀ s : ℝ, MemVectorFourierSobolev s (χ.physicalCovectorCutoff.vectorLow f)) ∧
      ‖χ.physicalCovectorCutoff.vectorLow f‖ ≤ B * ‖f‖ ∧
      (∀ᵐ θ ∂volume, R * Λ < ‖θ‖ →
        LowEnvelope.paperL2FourierTransform (χ.physicalCovectorCutoff.vectorLow f) θ = 0) ∧
      MemVectorFourierSobolev p (χ.physicalCovectorCutoff.vectorHigh f) ∧
      MemVectorFourierSobolev t (χ.physicalCovectorCutoff.vectorHigh f) ∧
      vectorFourierSobolevNorm t (χ.physicalCovectorCutoff.vectorHigh f) ≤
        ((1 + B) * (2 * Real.pi) ^ (p - t)) * Λ ^ (t - p) *
          vectorFourierSobolevNorm p f :=
  ⟨χ.physicalCovectorCutoff.vectorLow_add_vectorHigh f,
    fun s ↦ χ.physicalCovectorCutoff.vectorLow_mem_all_orders s f,
    χ.physicalCovectorCutoff.norm_vectorLow_le f,
    χ.paperL2FourierTransform_vectorLow_zero_outside f,
    (χ.physicalCovectorCutoff.vectorHigh_sobolev_bound hf).1,
    χ.vectorHigh_physical_tail_bound hΛ htp hf⟩

/-- Instantiating the envelope interface requires exactly the original vector
Fourier Sobolev profile, on the same Euclidean L² space. Its producer is the
wave/current-mean construction; its consumer is the complete-complement
assembly in `app:ch_response:thm:response-literal-transfer`. -/
theorem hasEnvelopeProfile_vectorFourier_iff {ι : Type*}
    (f : ι → VL2) (A K : ι → ℝ) :
    HasEnvelopeProfile vectorFourierSobolevScale f A K ↔
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
        MemVectorFourierSobolev s (f i) ∧
          vectorFourierSobolevNorm s (f i) ≤ C * A i * K i ^ s := by
  constructor
  · intro h s
    obtain ⟨C, hC, hb⟩ := h s
    refine ⟨C, hC, fun i ↦ ⟨(hb i).1, ?_⟩⟩
    simpa only [vectorFourierSobolevScale_gradeNorm s (hb i).1] using (hb i).2
  · intro h s
    obtain ⟨C, hC, hb⟩ := h s
    refine ⟨C, hC, fun i ↦ ⟨(hb i).1, ?_⟩⟩
    simpa only [vectorFourierSobolevScale_gradeNorm s (hb i).1] using (hb i).2

end JanetCartan.ResponseTransfer.Complement
