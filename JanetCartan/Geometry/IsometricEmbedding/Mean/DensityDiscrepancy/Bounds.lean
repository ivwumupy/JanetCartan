module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.PositiveAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Integration

/-!
# Positive-density discrepancy estimates

The conditional deduction in `app:ch_mean_pairs:eq:mean-density-lipschitz`.
The current and transport maps are linear in the actual initial amplitude;
their difference has a finite-jet gain of `Λ⁻¹`. The square-root, polarization,
and color integration steps are proved, not packaged as analytic hypotheses.

`I` realizes initial data in its literal carrier/initial variables and `F`
realizes derivative amplitudes as matrix fields. `L` is the linear measurement
into the chosen output space (for application, the fixed `H^s` realization).
Its finite-jet continuity bound and the actual atom bounds are explicit inputs.
The theorem neither constructs those maps nor identifies the transport square
with the transported density. The latter is a separate exact identity.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.DensityDiscrepancy

variable {X P A V Y α ι m n : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace α] [Fintype ι] [Fintype m] [Fintype n]

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: a frequency-independent
constant for both the positive-density Lipschitz estimate and the discrepancy
at zero. The finite initial shift is the explicit natural number `j`; `k` is
the required physical jet order for the fixed output realization `L`.

The identities involving `I` specify actual amplitudes, not bounds on the
answer. All bounds for the nonlinear square-root map are discharged internally.
`U`, `T`, `Λ`, and the masks are quantified *after* the constant. The literal
measure enters only through its total mass. -/
theorem exists_density_discrepancy_bounds
    (μ : Measure α) [IsFiniteMeasure μ]
    (I : A →ₗ[ℝ] (X → ℝ)) (F : V →ₗ[ℝ] (P → Matrix m n ℂ))
    (L : (P → Matrix n n ℝ) →ₗ[ℝ] Y)
    {s : Set X} (hs : IsCompact s) {t : Set P} (ht : IsCompact t)
    (j k : ℕ) (hF : ∀ v, ContDiff ℝ k (F v))
    (r : X → ℝ) (hr : ContDiff ℝ j r)
    {M R C K : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hrR : cNorm s j r ≤ R)
    (hL : ∀ f, ContDiff ℝ k f → ‖L f‖ ≤ K * cNorm t k f) :
    ∃ Cₛ : ℝ, 0 < Cₛ ∧ ∀ (mask : ι → α → ℝ),
      (∀ i z, 0 ≤ mask i z) → (∀ z, ∑ i, mask i z = 1) →
      ∀ (Λ : ℝ), 0 < Λ →
      ∀ U T : ι → α → A →ₗ[ℝ] V,
      (∀ i z a, cNorm t k (F (U i z a)) ≤ C * cNorm s j (I a)) →
      (∀ i z a, cNorm t k (F (T i z a)) ≤ C * cNorm s j (I a)) →
      (∀ i z a, cNorm t k (F ((U i z - T i z) a)) ≤
        Λ⁻¹ * C * cNorm s j (I a)) →
      (∀ (v w : X → ℝ) (a b : A),
        ContDiff ℝ j v → ContDiff ℝ j w →
        cNorm s j v ≤ M → cNorm s j w ≤ M →
        (∀ x, 0 < 1 + v x) → (∀ x, 0 < 1 + w x) →
        (∀ x ∈ s, 1 + v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
        (∀ x ∈ s, 1 + w x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
        I a = (fun x ↦ positiveDensityAmplitude (r x) (v x)) →
        I b = (fun x ↦ positiveDensityAmplitude (r x) (w x)) →
        Integrable (fun z ↦ ∑ i, mask i z •
          squareDiscrepancy (measuredHermitianBilinear F L) (U i z) (T i z) a) μ →
        Integrable (fun z ↦ ∑ i, mask i z •
          squareDiscrepancy (measuredHermitianBilinear F L) (U i z) (T i z) b) μ →
        ‖integratedHermitianDiscrepancy μ mask F L U T a -
          integratedHermitianDiscrepancy μ mask F L U T b‖ ≤
          Cₛ * Λ⁻¹ * cNorm s j (v - w)) ∧
      (∀ a₀ : A, I a₀ = r →
        ‖integratedHermitianDiscrepancy μ mask F L U T a₀‖ ≤ Cₛ * Λ⁻¹) := by
  obtain ⟨B, hB, hbounds⟩ := exists_positiveAmplitude_cNorm_bounds hs j hM hR
  let mass := μ.real Set.univ
  have hmass : 0 ≤ mass := ENNReal.toReal_nonneg
  let D := 4 * (K * 2 ^ k) * C ^ 2 * (R + B * M) * B * mass
  let D₀ := 2 * (K * 2 ^ k) * C ^ 2 * R ^ 2 * mass
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  refine ⟨1 + D + D₀, by positivity, ?_⟩
  intro mask hm hpartition Λ hΛ U T hU hT hdiff
  have hΛ' : 0 ≤ Λ⁻¹ := inv_nonneg.mpr hΛ.le
  constructor
  · intro v w a b hv hw hvM hwM hvpos hwpos hvi hwi ha hb hai hbi
    have hvw0 := cNorm_nonneg s j (v - w)
    obtain ⟨hva, hwb, hd⟩ := hbounds r v w hr hv hw hrR hvM hwM hvpos hwpos hvi hwi
    rw [← ha] at hva
    rw [← hb] at hwb
    have hid : I (a - b) = (fun x ↦ positiveDensityAmplitude (r x) (v x) -
        positiveDensityAmplitude (r x) (w x)) := by rw [map_sub, ha, hb]; rfl
    rw [← hid] at hd
    have hbase := norm_integratedHermitianDiscrepancy_sub_le μ mask hm hpartition F L U T
      (fun a ↦ cNorm s j (I a)) (fun a ↦ cNorm_nonneg _ _ _)
      ht k hF hC hK hΛ' hL hU hT hdiff a b hai hbi
    calc
      _ ≤ (2 * (K * 2 ^ k) * C ^ 2 * Λ⁻¹ *
          (cNorm s j (I a) + cNorm s j (I b)) * cNorm s j (I (a - b))) * mass := hbase
      _ ≤ (2 * (K * 2 ^ k) * C ^ 2 * Λ⁻¹ *
          ((R + B * M) + (R + B * M)) * (B * cNorm s j (v - w))) * mass := by
        apply mul_le_mul_of_nonneg_right _ hmass
        apply mul_le_mul _ hd (cNorm_nonneg _ _ _) (by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add hva hwb) (by positivity)
      _ = D * Λ⁻¹ * cNorm s j (v - w) := by dsimp [D]; ring
      _ ≤ (1 + D + D₀) * Λ⁻¹ * cNorm s j (v - w) := by
        gcongr
        linarith
  · intro a₀ ha₀
    have hr0 := cNorm_nonneg s j r
    have hbase := norm_integratedHermitianDiscrepancy_le μ mask hm hpartition F L U T
      (fun a ↦ cNorm s j (I a)) (fun a ↦ cNorm_nonneg _ _ _)
      ht k hF hC hK hΛ' hL hU hT hdiff a₀
    rw [ha₀] at hbase
    calc
      _ ≤ (2 * (K * 2 ^ k) * C ^ 2 * Λ⁻¹ * cNorm s j r ^ 2) * mass := hbase
      _ ≤ (2 * (K * 2 ^ k) * C ^ 2 * Λ⁻¹ * R ^ 2) * mass := by
        gcongr
      _ = D₀ * Λ⁻¹ := by dsimp [D₀]; ring
      _ ≤ (1 + D + D₀) * Λ⁻¹ := by gcongr; linarith

end JanetCartan.DensityDiscrepancy
