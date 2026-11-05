module

public import JanetCartan.Analysis.Microlocal.Localization.SourceEstimates

/-!
# Absorbing the envelope's pointwise loss only in the Fourier tail

For `app:ch_response:prop:response-graded`, Sobolev embedding costs a fixed
power `K^b`. The existing `source_negative_sobolev` retains that loss even
in its annular term. Here the annular term uses an independent actual L² bound;
only the complementary tail uses amplitude jets. Increasing the integration
order absorbs the latter loss. Construction of these jets from the envelope
is a separate obligation; this module does not assert the full source theorem.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ResponseTransfer.SourceNegative

open JanetCartan.Localization

/-- The fixed Sobolev embedding loss is absorbed by extra integrations by parts
in the source tail (`app:ch_response:prop:response-graded`). -/
theorem tail_factor_with_loss_le {ρ K σ b d M : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hK : 0 ≤ K) (hKρ : K ≤ ρ) (hb : 0 ≤ b)
    (hgap : K ≤ ρ ^ (1 - σ)) (hq : M + (b + d) ≤ σ * q) :
    K ^ b * (ρ ^ d * (K / ρ) ^ q) ≤ ρ ^ (-M) := by
  calc
    _ ≤ ρ ^ b * (ρ ^ d * (K / ρ) ^ q) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hK hKρ hb) (by positivity)
    _ = ρ ^ (b + d) * (K / ρ) ^ q := by
      rw [Real.rpow_add (by positivity : 0 < ρ)]
      ring
    _ ≤ _ := tail_factor_le_negative_power hρ hK hgap hq

variable {D E F ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

/-- The actual shell constant is nonnegative, as needed to absorb its scale loss
in `source_negative_sobolev_with_l2`. -/
theorem sourceTailConstant_nonneg (e : OrthonormalBasis ι ℝ E) (S : Set E)
    (c G W : ℝ) (P C : ℕ → ℝ) (m : ℝ) (q : ℕ)
    (hW : 0 ≤ W) (hC : ∀ r, 0 ≤ C r) :
    0 ≤ sourceTailConstant e S c G W P C m q := by
  have ht := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e ((radialGapConstant c G) ^ 2) (max G 1) P)
    hC q 0
  unfold sourceTailConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg hW ht) measureReal_nonneg)
    (Real.sqrt_nonneg _)

/-- The source-shell deduction with a separate L² input, used for the original
source in `app:ch_response:prop:response-graded`. Unlike the generic shell bound,
the near-annulus term has no amplitude supremum loss. The amplitude jet premise
must still be derived from the actual Sobolev envelope before applying this to
the response; it is not an additional input to the final source theorem. -/
theorem source_negative_sobolev_with_l2
    {φ : D → E → ℝ} {a : D → E → F} {U S : Set E}
    {c G A K b : ℝ} {P C : ℕ → ℝ}
    (s : SourceShellBounds φ a U S c G A K b P C)
    (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (e : OrthonormalBasis ι ℝ E) {ρ W : ℝ} {π : (E →L[ℝ] ℝ) → ℂ}
    (hρ : 1 ≤ ρ) (hπ : SourceShellMask π c G ρ W)
    {σ M B₀ : ℝ} (hM : 0 ≤ M) (hKρ : K ≤ ρ)
    (hgap : K ≤ ρ ^ (1 - σ)) (q : ℕ)
    (hq : (Module.finrank ℝ E : ℝ) / 2 < q)
    (horder : M + (b + (Module.finrank ℝ E : ℝ) / 2) ≤ σ * q)
    (h₀ : fourierWeightedL2Norm volume 0 (fun ξ : E ↦
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)) ≤ B₀) :
    fourierWeightedL2Norm volume (-M) (fun ξ : E ↦
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)) ≤
      ((c / 4) ^ (-M) * B₀ + sourceTailConstant e S c G W P C 0 q *
        A * ν.variation.real Set.univ) * ρ ^ (-M) := by
  let H := fun ξ : E ↦ physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
    (InnerProductSpace.toDual ℝ E ξ)
  let mask := fun ξ : E ↦ π (InnerProductSpace.toDual ℝ E ξ)
  obtain ⟨hti, htail⟩ := source_sobolev_tail s ν e hρ hπ (m := 0) le_rfl q
    (by simpa using hq)
  simp only [Real.rpow_zero, one_mul, zero_add] at hti htail
  have hmask : ∀ ξ : E, ‖ξ‖ < c / 4 * ρ → mask ξ = 0 := by
    intro ξ hξ
    change π (InnerProductSpace.toDual ℝ E ξ) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hl := (hπ.support hs).1
    simp only [LinearIsometryEquiv.norm_map] at hl
    linarith
  have hsplit := fourierWeightedL2Norm_negative_le_annular_split
    (div_pos s.lower_pos (by norm_num : (0 : ℝ) < 4))
    (by positivity : 0 < ρ) hM mask H hmask
    (integrable_norm_sq_physicalFourierIntegral (s.source_integrable ν ρ).1
      (s.source_integrable ν ρ).2) hti
  have habs := tail_factor_with_loss_le hρ (by linarith [s.scale_one_le]) hKρ
    s.loss_nonneg hgap horder
  have hT := sourceTailConstant_nonneg e S c G W P C 0 q
    hπ.bound_nonneg s.amplitude_constants_nonneg
  have hc : 0 < c := s.lower_pos
  have htail' : fourierWeightedL2Norm volume 0 (fun ξ ↦ (1 - mask ξ) • H ξ) ≤
      (sourceTailConstant e S c G W P C 0 q * A * ν.variation.real Set.univ) *
        ρ ^ (-M) := by
    apply htail.trans
    calc
      _ = (sourceTailConstant e S c G W P C 0 q * A * ν.variation.real Set.univ) *
          (K ^ b * (ρ ^ ((Module.finrank ℝ E : ℝ) / 2) * (K / ρ) ^ q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left habs
        (mul_nonneg (mul_nonneg hT s.amplitude_nonneg) measureReal_nonneg)
  apply hsplit.trans
  calc
    _ ≤ (c / 4 * ρ) ^ (-M) * B₀ +
        (sourceTailConstant e S c G W P C 0 q * A * ν.variation.real Set.univ) *
          ρ ^ (-M) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity)) htail'
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ c / 4) (by positivity : 0 ≤ ρ)]
      ring

end JanetCartan.ResponseTransfer.SourceNegative
