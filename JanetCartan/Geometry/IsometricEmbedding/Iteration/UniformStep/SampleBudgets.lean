module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.SampledRow
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledEstimates

/-!
# Deterministic budgets for the original canonical samples

Apply the existing finite-patch counting and mass theorems to the literal
canonical `SampleIndex` and `sampleWeight`. Fixed constants precede all stages
and shifts. The original mesh gives exactly the exponent `1 + samplingSlack`.
These estimates apply to every shift, including the eventual common sample;
they make no new probabilistic choice and do not assert a normal comparison.
-/

@[expose] public noncomputable section

open scoped BigOperators
namespace JanetCartan.UniformStep
open SeparatedSampling CanonicalRowComparison
variable {J : Type*} [Fintype J]

/-- `main:eq:sampling`: the literal canonical sample enumeration has the
original count exponent for every shift, by the existing three-parameter
counting theorem. The coefficient depends only on fixed charts, window order
and patch radius. Consumed by the count input of
`exists_normalized_measured_direct_sampled_stage`. -/
theorem sampleIndex_card_le_originalScale (p : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (weights : J → Point → ℝ) (w : ℝ → ℝ) {R : ℝ} (hR : 1 ≤ R)
    (shifts : J → Lattice → Point) :
    (Fintype.card (SampleIndex p B weights w (R ^ (-separationExponent)) shifts) : ℝ) ≤
      ((Fintype.card J : ℝ) * countConstant p B) * R ^ (1 + samplingSlack) := by
  classical
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hh : 0 < R ^ (-separationExponent) := Real.rpow_pos_of_pos hRpos _
  have hh₁ : R ^ (-separationExponent) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [separationExponent])
  have hc : ((R ^ (-separationExponent)) ^ (3 : ℕ))⁻¹ = R ^ (1 + samplingSlack) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le, ← Real.rpow_neg hRpos.le]
    congr 1
    norm_num [separationExponent, samplingSlack]
  change (Fintype.card ((a : J) × samples p B (weights a) w
    (R ^ (-separationExponent)) (shifts a)) : ℝ) ≤ _
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _a : J, countConstant p B * R ^ (1 + samplingSlack) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [Fintype.card_coe, div_eq_mul_inv, hc] using
        (card_samples_le (p := p) (ψ := weights a) (w := w) (U := shifts a) hB hh hh₁)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- `main:eq:sampling`: total mass of the SAME canonical samples is uniformly
bounded at the original mesh, without choosing a sample or normalizing any
weight. The existing patch mass theorem supplies the estimate for every shift.
Consumed by the mass input of the actual sampled-stage construction. -/
theorem sampleWeight_mass_le_originalScale (p : ℕ) {B W : ℝ} {P : J → ℝ}
    {weights : J → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hweights : ∀ a, PatchBounds (weights a) B (P a))
    {R : ℝ} (hR : 1 ≤ R) (shifts : J → Lattice → Point) :
    ∑ i : SampleIndex p B weights w (R ^ (-separationExponent)) shifts,
      sampleWeight B weights w (R ^ (-separationExponent)) shifts i ≤
        countConstant p B * ((∑ a, P a) * W ^ 3) := by
  classical
  have hh : 0 < R ^ (-separationExponent) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) _
  have hh₁ : R ^ (-separationExponent) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [separationExponent])
  simp only [SampleIndex, Fintype.sum_sigma, sampleWeight, Finset.sum_coe_sort]
  calc
    _ ≤ ∑ a : J, countConstant p B * (P a * W ^ 3) := by
      apply Finset.sum_le_sum
      intro a _
      exact totalMass_le hw (hweights a) hh hh₁
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Both synthesis weight budgets for the actual canonical enumeration,
with constants fixed before the stage and shifts (`main:eq:primary-strain`,
`app:ch_pairs:eq:pairs-weighted-U`). This applies the original counting and
mass producers and discharges the corresponding numeric premises of the
primary and pair assemblers; it does not select the common normal event. -/
theorem sampled_weight_budgets_originalScale (p : ℕ) {B W : ℝ} (hB : 0 ≤ B) {P : J → ℝ}
    {weights : J → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hweights : ∀ a, PatchBounds (weights a) B (P a))
    {R : ℝ} (hR : 1 ≤ R) (shifts : J → Lattice → Point) :
    let Ccount := (Fintype.card J : ℝ) * countConstant p B
    let Cmass := countConstant p B * ((∑ a, P a) * W ^ 3)
    let μ := sampleWeight (p := p) B weights w (R ^ (-separationExponent)) shifts
    0 ≤ Ccount ∧ 0 ≤ Cmass ∧ (∀ i, 0 ≤ μ i) ∧
      (Fintype.card (SampleIndex p B weights w (R ^ (-separationExponent)) shifts) : ℝ) ≤
        Ccount * R ^ (1 + samplingSlack) ∧
      (∑ i, μ i) ≤ Cmass ∧
      ProductSum.coefficientMass μ ≤ (Ccount * Cmass) * R ^ (1 + samplingSlack) ∧
      ∑ i, Real.sqrt (μ i) ≤ Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2) := by
  dsimp only
  have hC : 0 ≤ countConstant p B := by
    dsimp [countConstant, blockCountConstant]
    positivity
  have hW : 0 ≤ W := (hw.nonneg 0).trans (hw.le_bound 0)
  have hP : ∀ a, 0 ≤ P a := fun a ↦ ((hweights a).nonneg 0).trans ((hweights a).le_bound 0)
  have hCcount : 0 ≤ (Fintype.card J : ℝ) * countConstant p B := mul_nonneg (Nat.cast_nonneg _) hC
  have hCmass : 0 ≤ countConstant p B * ((∑ a, P a) * W ^ 3) :=
    mul_nonneg hC (mul_nonneg (Finset.sum_nonneg fun a _ ↦ hP a) (pow_nonneg hW _))
  have hμ := sampleWeight_nonneg shifts hw hweights
    (Real.rpow_nonneg (zero_le_one.trans hR) (-separationExponent))
  have hcount := sampleIndex_card_le_originalScale p hB weights w hR shifts
  have hmass := sampleWeight_mass_le_originalScale p hw hweights hR shifts
  exact ⟨hCcount, hCmass, hμ, hcount, hmass,
    sampled_coefficientMass_le _ hμ hCmass hcount hmass,
    sampled_weight_sum_le _ hμ (zero_lt_one.trans_le hR) hCcount hCmass hcount hmass⟩

end JanetCartan.UniformStep
