module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Literal retarded transfer in the local Sobolev scale

The norm adapters and the proved integral-energy bound give
`app:ch_response:eq:fixed-factor-transfer` for both signed integrals. All
constants precede the frequency, covector and envelope. These deductions use
the fixed buffered cutoff data; their construction and the actual geometric
zero-energy phase identification remain with the parent producers.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ResponseTransfer.RetardedCutoffs

open RetardedSobolev.Spaces LocalSobolev

variable {d : ℕ} (W : RetardedCutoffs d)

/-- The actual restriction Sobolev estimate for both literal demodulated
integrals, with no loss of derivatives (`app:ch_response:eq:fixed-factor-transfer`).
The estimate is derived from integral energy and both proved norm comparisons;
in particular it is not a field of the cutoff data. -/
theorem exists_demodulated_local_norm_bounds (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (ζ : Euclidean d) (f : Test d),
      let G := restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
        MeasurableSet.univ
      G.gradeNorm s (retardedTestToLocalL2 (W.demodulatedLower ρ ζ f)) ≤
          C * G.gradeNorm s (retardedTestToLocalL2 f) ∧
      G.gradeNorm s (retardedTestToLocalL2 (W.demodulatedUpper ρ ζ f)) ≤
          C * G.gradeNorm s (retardedTestToLocalL2 f) := by
  obtain ⟨D, hD, hb⟩ := W.exists_demodulated_jet_norm_bounds s
  obtain ⟨C, hC, hc⟩ := exists_retardedTestToLocalL2_gradeNorm_le_mul_ofTest_norm d s
  refine ⟨C * D, mul_nonneg hC hD, fun ρ ζ f ↦ ?_⟩
  have hi := ofTest_norm_le_retardedTestToLocalL2_gradeNorm s f
  constructor
  · exact (hc _).trans ((mul_le_mul_of_nonneg_left (hb ρ ζ f).1 hC).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (mul_nonneg hC hD)))
  · exact (hc _).trans ((mul_le_mul_of_nonneg_left (hb ρ ζ f).2 hC).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (mul_nonneg hC hD)))

/-- The buffered signed integrals and their literal adjoints preserve the
actual `HasEnvelopeProfile` (`app:ch_response:eq:fixed-factor-transfer`). The
frequency and physical covector vary with the family index, while the cutoffs
are fixed. Membership in every Sobolev grade is part of the conclusion. -/
theorem demodulated_hasEnvelopeProfile {ι : Type*} (f : ι → Test d)
    (ρ : ι → ℝ) (ζ : ι → Euclidean d) (A K : ι → ℝ)
    (hf : HasEnvelopeProfile
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ MeasurableSet.univ)
      (fun i ↦ retardedTestToLocalL2 (f i)) A K) :
    HasEnvelopeProfile
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ MeasurableSet.univ)
      (fun i ↦ retardedTestToLocalL2 (W.demodulatedLower (ρ i) (ζ i) (f i))) A K ∧
    HasEnvelopeProfile
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ MeasurableSet.univ)
      (fun i ↦ retardedTestToLocalL2 (W.demodulatedUpper (ρ i) (ζ i) (f i))) A K := by
  have hb (s : ℕ) := W.exists_demodulated_local_norm_bounds s
  constructor <;> intro s <;> obtain ⟨D, hD, hbound⟩ := hb s <;>
    obtain ⟨C, hC, hf⟩ := hf s <;> refine ⟨D * C, mul_nonneg hD hC, fun i ↦
      ⟨retardedTestToLocalL2_mem _ s, ?_⟩⟩
  · exact ((hbound (ρ i) (ζ i) (f i)).1).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hf i).2 hD)
  · exact ((hbound (ρ i) (ζ i) (f i)).2).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hf i).2 hD)

end JanetCartan.ResponseTransfer.RetardedCutoffs
