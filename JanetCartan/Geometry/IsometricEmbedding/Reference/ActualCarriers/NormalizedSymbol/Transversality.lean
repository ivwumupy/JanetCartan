module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Differential

/-!
# The transverse gap after normalization

Step 1 of `app:ch_seed:prop:seed-actual-menu`: an adapted determinant derivative
gap on the characteristic set gives a positive gap for the normalized symbol.
The annulus and determinant gap are inputs, to be supplied by the frozen-patch,
pencil-continuity and characteristic-root constructions. The normalization gap
is a conclusion. The direction can be any fixed adapted coordinate direction.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ActualCarriers

/-- The exact covector differential on the characteristic set; physical frame
regularity is unnecessary for this frozen-physical-point identity
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem fderiv_covector_normalizedSymbol_of_determinant_eq_zero {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (x : Euclidean n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) (hp : determinant (Q x) ξ = 0) :
    fderiv ℝ (fun η ↦ normalizedSymbol Q (x, η)) ξ =
      determinantNormalization ξ • fderiv ℝ (determinant (Q x)) ξ := by
  change fderiv ℝ (determinant (Q x) * determinantNormalization) ξ = _
  rw [fderiv_mul (hasFDerivAt_determinant (Q x) ξ).differentiableAt
    ((contDiffAt_determinantNormalization hξ).differentiableAt (by simp))]
  simp [hp]

/-- A fixed annulus bounds the positive normalization uniformly from below
(`app:ch_seed:prop:seed-actual-menu`, Step 1). This form works in every dimension. -/
theorem determinantNormalization_annular_lower_bound {n : ℕ} {ξ : Euclidean n}
    {r R : ℝ} (hr : 0 < r) (hlower : r ≤ ‖ξ‖) (hupper : ‖ξ‖ ≤ R) :
    r / R ^ n ≤ determinantNormalization ξ := by
  have hξ : 0 < ‖ξ‖ := hr.trans_le hlower
  rw [determinantNormalization, zpow_sub₀ hξ.ne', zpow_one, zpow_natCast]
  exact div_le_div₀ (norm_nonneg ξ) hlower (pow_pos hξ n)
    (pow_le_pow_left₀ (norm_nonneg ξ) hupper n)

/-- A determinant derivative gap transfers to the normalized symbol on a fixed
annulus (`app:ch_seed:prop:seed-actual-menu`, Step 1). No transversality of the
normalized symbol is assumed. -/
theorem normalizedSymbol_transverse_gap {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (x ξ v : Euclidean n)
    {r R c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hlower : r ≤ ‖ξ‖) (hupper : ‖ξ‖ ≤ R) (hp : determinant (Q x) ξ = 0)
    (hgap : c ≤ fderiv ℝ (determinant (Q x)) ξ v) :
    (r / R ^ n) * c ≤ fderiv ℝ (fun η ↦ normalizedSymbol Q (x, η)) ξ v := by
  have hξ : ξ ≠ 0 := norm_pos_iff.mp (hr.trans_le hlower)
  rw [fderiv_covector_normalizedSymbol_of_determinant_eq_zero Q x hξ hp]
  change _ ≤ determinantNormalization ξ * fderiv ℝ (determinant (Q x)) ξ v
  exact mul_le_mul (determinantNormalization_annular_lower_bound hr hlower hupper)
    hgap hc.le (determinantNormalization_pos hξ).le

/-- In particular the adapted derivative is strictly positive on the current
characteristic set (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedSymbol_transverse_pos {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (x ξ v : Euclidean n)
    {r R c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hlower : r ≤ ‖ξ‖) (hupper : ‖ξ‖ ≤ R) (hp : determinant (Q x) ξ = 0)
    (hgap : c ≤ fderiv ℝ (determinant (Q x)) ξ v) :
    0 < fderiv ℝ (fun η ↦ normalizedSymbol Q (x, η)) ξ v := by
  have hR : 0 < R := (hr.trans_le hlower).trans_le hupper
  exact (mul_pos (div_pos hr (pow_pos hR n)) hc).trans_le
    (normalizedSymbol_transverse_gap Q x ξ v hr hc hlower hupper hp hgap)

/-- One constant works on the whole prescribed annular characteristic patch,
providing the common positive buffer of `app:ch_seed:prop:seed-actual-menu`, Step 1.
The parent construction must supply the annulus and determinant gap. -/
theorem exists_uniform_normalizedSymbol_transverse_gap {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n)
    (A : Set (Euclidean n × Euclidean n)) (v : Euclidean n)
    {r R c : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hannulus : ∀ z ∈ A, r ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ R)
    (hgap : ∀ z ∈ A, determinant (Q z.1) z.2 = 0 →
      c ≤ fderiv ℝ (determinant (Q z.1)) z.2 v) :
    ∃ δ > 0, ∀ z ∈ A, determinant (Q z.1) z.2 = 0 →
      δ ≤ fderiv ℝ (fun η ↦ normalizedSymbol Q (z.1, η)) z.2 v := by
  refine ⟨(r / R ^ n) * c, mul_pos (div_pos hr (pow_pos hR n)) hc, ?_⟩
  intro z hz hp
  exact normalizedSymbol_transverse_gap Q z.1 z.2 v hr hc
    (hannulus z hz).1 (hannulus z hz).2 hp (hgap z hz hp)

end JanetCartan.ActualCarriers
