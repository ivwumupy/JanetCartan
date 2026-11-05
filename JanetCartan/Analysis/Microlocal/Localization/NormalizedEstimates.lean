module

public import JanetCartan.Analysis.Microlocal.Localization.SourceEstimates

/-!
# Source estimates in the manuscript's Fourier normalization

The two inequalities of `app:ch_osc:prop:osc-source-shell`, including the fixed
amplitude loss and all constants. The weighted norms are spectral Sobolev norms:
the tail is the norm of `(1 - π) ĥ`, with `ĥ(ξ) = (2π)^(-n) ∫ exp(-i x·ξ) h(x)`.
The choice of integration order is uniform over the source scales and masks.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Localization

section Difference
variable {D E F : Type*} [MeasurableSpace D] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- `app:ch_osc:rem:osc-difference-frequency`: the actual source with signed
difference phase is exactly the source at the positive frequency `λ |z-z'|`.
The normalized phase retains the sign for either ordering of `z` and `z'`. -/
theorem oscillatorySource_differenceFrequency (ν : ComplexMeasure D)
    (φ ψ : D → E → ℝ) (a : D → E → F) (lam : ℝ) {z z' : ℝ} (hz : z ≠ z') :
    oscillatorySource ν (fun u ↦ normalizedDifferencePhase (φ u) (ψ u) z z') a
      (differenceFrequency lam z z') =
      oscillatorySource ν (fun u x ↦ φ u x - ψ u x) a lam := by
  funext x
  simp only [oscillatorySource, phaseOscillation,
    differenceFrequency_mul_normalizedDifferencePhase lam hz]
end Difference

section Homogeneity
variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normalization factor in `app:ch_osc:prop:osc-source-shell` acts
homogeneously on every spectral Sobolev norm. -/
theorem fourierWeightedL2Norm_real_smul (μ : Measure E) (m t : ℝ) (H : E → F) :
    fourierWeightedL2Norm μ m (fun x ↦ t • H x) =
      |t| * fourierWeightedL2Norm μ m H := by
  simp only [fourierWeightedL2Norm, norm_smul, Real.norm_eq_abs, mul_pow]
  simp_rw [show ∀ x, (1 + ‖x‖ ^ 2) ^ m * (|t| ^ 2 * ‖H x‖ ^ 2) =
    |t| ^ 2 * ((1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2) from fun _ ↦ by ring]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

/-- `app:ch_osc:prop:osc-source-shell`: normalization preserves weighted
integrability, so the displayed norms are finite Sobolev norms. -/
theorem integrable_sobolevEnergy_real_smul {μ : Measure E} {m : ℝ} {H : E → F}
    (hi : Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2) μ) (t : ℝ) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ m * ‖t • H x‖ ^ 2) μ := by
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, mul_left_comm] using
    hi.const_mul (|t| ^ 2)
end Homogeneity

variable {D E F ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

/-- The physical Fourier transform with the manuscript's `(2π)^(-n)`
normalization (`app:ch_osc:prop:osc-source-shell`). -/
def paperFourierTransform (h : E → F) (ξ : E) : F :=
  ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ •
    physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)

variable {φ : D → E → ℝ} {a : D → E → F} {U K : Set E}
  {c G A L b : ℝ} {P C : ℕ → ℝ}
  (s : SourceShellBounds φ a U K c G A L b P C)
  (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
  (e : OrthonormalBasis ι ℝ E) {ρ W : ℝ} {π : (E →L[ℝ] ℝ) → ℂ}
  (hρ : 1 ≤ ρ) (hπ : SourceShellMask π c G ρ W)

include s in
/-- `app:ch_osc:eq:osc-source-negative`: finiteness of the negative Sobolev
norm in the manuscript's normalization. -/
theorem paper_source_negative_energy_integrable (ρ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-M) *
      ‖paperFourierTransform (oscillatorySource ν φ a ρ) ξ‖ ^ 2) :=
  integrable_sobolevEnergy_real_smul (s.negative_energy_integrable ν ρ hM) _

include s hρ hπ

/-- `app:ch_osc:eq:osc-source-tail`: the radial Fourier-shell estimate for the
actual source, in the exact normalization of the manuscript, with no additional
analytic premises. The formula for the constant displays all derivative losses. -/
theorem paper_source_sobolev_tail {m : ℝ} (hm : 0 ≤ m) (q : ℕ)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) :
    let H := fun ξ : E ↦ (1 - π (InnerProductSpace.toDual ℝ E ξ)) •
      paperFourierTransform (oscillatorySource ν φ a ρ) ξ
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ m * ‖H ξ‖ ^ 2) ∧
      fourierWeightedL2Norm volume m H ≤
        (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ * sourceTailConstant e K c G W P C m q) *
          A * ν.variation.real Set.univ * L ^ b *
          (ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2) * (L / ρ) ^ q) := by
  dsimp only [paperFourierTransform]
  simp_rw [smul_comm (1 - π _) (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹)]
  obtain ⟨hi, hb⟩ := source_sobolev_tail s ν e hρ hπ hm q hq
  refine ⟨integrable_sobolevEnergy_real_smul hi _, ?_⟩
  rw [fourierWeightedL2Norm_real_smul, abs_of_pos (by positivity)]
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
  ring

/-- `app:ch_osc:eq:osc-source-negative`: negative Sobolev gain in the
manuscript's normalization, for any integration order large enough to absorb
the tail. -/
theorem paper_source_negative_sobolev {σ M : ℝ} (hM : 0 ≤ M)
    (hgap : L ≤ ρ ^ (1 - σ)) (q : ℕ)
    (hq : (Module.finrank ℝ E : ℝ) / 2 < q)
    (horder : M + (Module.finrank ℝ E : ℝ) / 2 ≤ σ * q) :
    fourierWeightedL2Norm volume (-M)
      (paperFourierTransform (oscillatorySource ν φ a ρ)) ≤
      (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ * sourceNegativeConstant e K c G W P C M q) *
        A * ν.variation.real Set.univ * L ^ b * ρ ^ (-M) := by
  unfold paperFourierTransform
  rw [fourierWeightedL2Norm_real_smul, abs_of_pos (by positivity)]
  apply (mul_le_mul_of_nonneg_left
    (source_negative_sobolev s ν e hρ hπ hM hgap q hq horder) (by positivity)).trans_eq
  ring

omit s hρ hπ in
/-- `app:ch_osc:eq:osc-source-negative`: for each requested observation order,
a single integration order works for every `A`, `L`, `ρ` and admissible mask.
Thus the constant is independent of the variable scales and the exponent `b`
remains fixed for all observations. -/
theorem exists_uniform_source_negative_order {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) :
    ∃ q : ℕ, (Module.finrank ℝ E : ℝ) / 2 < q ∧
      M + (Module.finrank ℝ E : ℝ) / 2 ≤ σ * q ∧
      ∀ {A L ρ : ℝ}, SourceShellBounds φ a U K c G A L b P C →
        1 ≤ ρ → L ≤ ρ ^ (1 - σ) →
        ∀ {π : (E →L[ℝ] ℝ) → ℂ}, SourceShellMask π c G ρ W →
          fourierWeightedL2Norm volume (-M)
            (paperFourierTransform (oscillatorySource ν φ a ρ)) ≤
            (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ *
              sourceNegativeConstant e K c G W P C M q) *
              A * ν.variation.real Set.univ * L ^ b * ρ ^ (-M) := by
  obtain ⟨q, hq, ho⟩ := exists_tail_order hσ ((Module.finrank ℝ E : ℝ) / 2) M
  refine ⟨q, hq, ho, ?_⟩
  intro A L ρ s hρ hgap π hπ
  exact paper_source_negative_sobolev s ν e hρ hπ hM hgap q hq ho

omit s hρ hπ in
/-- `app:ch_osc:eq:osc-source-negative` and `app:ch_osc:rem:osc-difference-frequency`:
the paper's fixed separated-carrier exponents give the actual source estimate
at every observation order, with one uniform choice of integration order. -/
theorem exists_uniform_source_negative_order_separated_carrier {M : ℝ} (hM : 0 ≤ M) :
    ∃ q : ℕ, (Module.finrank ℝ E : ℝ) / 2 < q ∧
      M + (Module.finrank ℝ E : ℝ) / 2 ≤ separatedCarrierGap * q ∧
      ∀ {T A L ρ : ℝ}, SourceShellBounds φ a U K c G A L b P C →
        0 ≤ T → 1 ≤ ρ → T ^ (carrierExponent - separationExponent) ≤ ρ →
        L ≤ T ^ (1 + meanSlack) →
        ∀ {π : (E →L[ℝ] ℝ) → ℂ}, SourceShellMask π c G ρ W →
          fourierWeightedL2Norm volume (-M)
            (paperFourierTransform (oscillatorySource ν φ a ρ)) ≤
            (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ *
              sourceNegativeConstant e K c G W P C M q) *
              A * ν.variation.real Set.univ * L ^ b * ρ ^ (-M) := by
  obtain ⟨q, hq, ho, hb⟩ := exists_uniform_source_negative_order
    (φ := φ) (a := a) (U := U) (K := K) (c := c) (G := G) (b := b)
    (P := P) (C := C) (W := W) ν e separatedCarrierGap_pos hM
  refine ⟨q, hq, ho, ?_⟩
  intro T A L ρ s hT hρ hf hL π hπ
  exact hb s hρ (scale_gap_of_separated_carrier hT hf hL) hπ

end JanetCartan.Localization
