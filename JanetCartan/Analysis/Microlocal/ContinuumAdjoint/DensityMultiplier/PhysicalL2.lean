module
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalCutoff
/-!
# The real physical density as an actual L² class

The final operations in `app:ch_background:eq:bg-density-adjoint` are continuous
real linear maps on the literal physical Lebesgue L² space. Their representatives
are exactly `2 Re u` and `2 Re (χ_y u)`. These maps are to be composed with the
shared partial inverse Fourier construction; they do not introduce a substitute
Fourier transform or identify physical data with the auxiliary torus.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds
variable {n : ℕ}

/-- Twice the real quadrature on physical L² classes, before the cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
def twoReL2 : CarrierL2 n →L[ℝ] Lp ℝ 2 (carrierMeasure n) :=
  ((2 : ℝ) • Complex.reCLM).compLpL 2 (carrierMeasure n)

/-- The uncut real output has the exact factor two
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem twoReL2_coeFn (u : CarrierL2 n) :
    twoReL2 u =ᵐ[carrierMeasure n] fun x ↦ 2 * (u x).re := by
  simpa only [twoReL2, smul_apply, Complex.reCLM_apply, smul_eq_mul]
    using ((2 : ℝ) • Complex.reCLM).coeFn_compLpL (p := 2) u

/-- The uncut real output bound on all physical L² data
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_twoReL2_le (u : CarrierL2 n) : ‖twoReL2 u‖ ≤ 2 * ‖u‖ := by
  change ‖((2 : ℝ) • Complex.reCLM).compLp u‖ ≤ _
  simpa only [norm_smul, Real.norm_ofNat, Complex.reCLM_norm, mul_one] using
    ((2 : ℝ) • Complex.reCLM).norm_compLp_le (p := 2) u

/-- The literal cutoff followed by twice the real part, as a bounded real
linear map on physical L² (`app:ch_background:eq:bg-density-adjoint`). -/
def densityPhysicalCutoffL2 (χ : Lp ℝ ∞ (carrierMeasure n)) :
    CarrierL2 n →L[ℝ] Lp ℝ 2 (carrierMeasure n) :=
  twoReL2.comp (carrierMultiplier χ)

/-- Agreement with the literal physical density on representatives
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityPhysicalCutoffL2_coeFn (χ : Lp ℝ ∞ (carrierMeasure n))
    (u : CarrierL2 n) :
    densityPhysicalCutoffL2 χ u =ᵐ[carrierMeasure n] densityPhysicalCutoff χ u := by
  filter_upwards [twoReL2_coeFn (carrierMultiplier χ u), carrierMultiplier_coeFn χ u]
    with x hr hm
  change twoReL2 (carrierMultiplier χ u) x = _
  rw [hr, hm]
  rfl

/-- A pointwise bound on the fixed mask gives the physical output bound; no
output estimate is assumed (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityPhysicalCutoffL2_le (χ : Lp ℝ ∞ (carrierMeasure n))
    {B : ℝ} (hb : ∀ᵐ x ∂carrierMeasure n, |χ x| ≤ B) (u : CarrierL2 n) :
    ‖densityPhysicalCutoffL2 χ u‖ ≤ (2 * B) * ‖u‖ := by
  have hm : ‖carrierMultiplier χ u‖ ≤ B * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [carrierMultiplier_coeFn χ u, hb] with x hx hxB
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hxB (norm_nonneg _)
  exact (norm_twoReL2_le (carrierMultiplier χ u)).trans
    (by nlinarith)

/-- A continuous compact physical mask produces the actual bounded operator
without a separate L∞ membership hypothesis
(`app:ch_background:eq:bg-density-adjoint`). -/
def compactDensityPhysicalCutoffL2 {χ : CarrierVariable n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    CarrierL2 n →L[ℝ] Lp ℝ 2 (carrierMeasure n) :=
  densityPhysicalCutoffL2 ((hχ.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ)

/-- The constructed compact-mask operator agrees with the original mask,
not only with its chosen L∞ representative
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem compactDensityPhysicalCutoffL2_coeFn {χ : CarrierVariable n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (u : CarrierL2 n) :
    compactDensityPhysicalCutoffL2 hχ hc u =ᵐ[carrierMeasure n] densityPhysicalCutoff χ u := by
  filter_upwards [densityPhysicalCutoffL2_coeFn
    ((hχ.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ) u,
    (hχ.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).coeFn_toLp] with x hx hmask
  exact hx.trans (by simp only [densityPhysicalCutoff, hmask])

/-- Compactness supplies a uniform all-data L² bound for the physical part
of the density adjoint (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_compactDensityPhysicalCutoffL2_bound {χ : CarrierVariable n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CarrierL2 n,
      ‖compactDensityPhysicalCutoffL2 hχ hc u‖ ≤ (2 * B) * ‖u‖ := by
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hc
  refine ⟨max 0 C, le_max_left _ _, fun u ↦ ?_⟩
  apply norm_densityPhysicalCutoffL2_le
  filter_upwards [(hχ.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).coeFn_toLp]
    with x hx
  rw [hx, ← Real.norm_eq_abs]
  exact (hC x).trans (le_max_right _ _)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
