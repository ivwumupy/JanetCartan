module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Pointwise

/-!
# Same-mask carrier kernel bound from the actual retained fields

The finite-jet producer controls transported position, original normal field
and full reduced covector. The literal kernel then has a fixed-frequency bound
with the same angular, high-pass and physical masks. No comparison of uncut
Fourier integral row operator norms is asserted. Consumer: strong raw-adjoint
continuity for `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow
variable {n N : ℕ}

/-- Exact pointwise carrier-kernel variation from the original retained
position, normal and reduced-covector differences. The common masks are not
changed, and the half-derivative factor remains explicit. -/
theorem norm_carrierKernel_sub_le_of_field_differences (d d₀ : CarrierData n N)
    (hchart : d.outputChart = d₀.outputChart) (x : Torus n) (u : CarrierVariable n)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hmask : d.measurementCutoff x * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d.highCutoff ‖u.2‖ =
      d₀.measurementCutoff x * d₀.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d₀.highCutoff ‖u.2‖)
    (hmaskBound : |d.measurementCutoff x * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) *
      d.highCutoff ‖u.2‖| ≤ 1)
    (hpos : ‖d.transportedPosition (d.chartPoint x) u.1 -
      d₀.transportedPosition (d₀.chartPoint x) u.1‖ ≤ δ)
    (hν : ‖d.normalField (d.chartPoint x) u.1‖ ≤ M)
    (hν₀ : ‖d₀.normalField (d₀.chartPoint x) u.1‖ ≤ M)
    (hq : ‖reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1)‖ ≤ M)
    (hdν : ‖d.normalField (d.chartPoint x) u.1 -
      d₀.normalField (d₀.chartPoint x) u.1‖ ≤ δ)
    (hdq : ‖reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1) -
      reducedCovector d₀ (d₀.chartPoint x) (d₀.covector (d₀.chartPoint x) u.1)‖ ≤ δ) :
    ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤
      Real.sqrt ‖u.2‖ * δ * (‖u.2‖ * M ^ 3 + 3 * M ^ 2) := by
  let m := d.measurementCutoff x * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d.highCutoff ‖u.2‖
  let ν := d.normalField (d.chartPoint x) u.1
  let ν₀ := d₀.normalField (d₀.chartPoint x) u.1
  let q := reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1)
  let q₀ := reducedCovector d₀ (d₀.chartPoint x) (d₀.covector (d₀.chartPoint x) u.1)
  have ha : carrierAmplitude d x u = (m * Real.sqrt ‖u.2‖) • (‖ν‖ ^ 2 • q) := by
    change (m * Real.sqrt ‖u.2‖ * ‖ν‖ ^ 2) • q = _
    rw [smul_smul]
  have ha₀ : carrierAmplitude d₀ x u = (m * Real.sqrt ‖u.2‖) • (‖ν₀‖ ^ 2 • q₀) := by
    change ((d₀.measurementCutoff x * d₀.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) *
      d₀.highCutoff ‖u.2‖) * Real.sqrt ‖u.2‖ * ‖ν₀‖ ^ 2) • q₀ = _
    rw [← hmask, smul_smul]
  have hm : |m * Real.sqrt ‖u.2‖| ≤ Real.sqrt ‖u.2‖ := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_right hmaskBound (Real.sqrt_nonneg _)).trans_eq (one_mul _)
  have hamp : ‖carrierAmplitude d x u‖ ≤ Real.sqrt ‖u.2‖ * M ^ 3 := by
    rw [ha, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hm (norm_squaredField_le ν q hν hq) (norm_nonneg _) (Real.sqrt_nonneg _)
  have hampDiff : ‖carrierAmplitude d x u - carrierAmplitude d₀ x u‖ ≤
      Real.sqrt ‖u.2‖ * (3 * M ^ 2 * δ) := by
    rw [ha, ha₀, ← smul_sub, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hm (norm_squaredField_sub_le ν ν₀ q q₀ hM hδ hν hν₀ hq hdν hdq)
      (norm_nonneg _) (Real.sqrt_nonneg _)
  have hphase : ‖carrierPhase d x u - carrierPhase d₀ x u‖ ≤ δ * ‖u.2‖ := by
    unfold carrierPhase
    rw [← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hpos (norm_nonneg _))
  calc
    ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤
        ‖carrierPhase d x u - carrierPhase d₀ x u‖ * ‖carrierAmplitude d x u‖ +
          ‖carrierAmplitude d x u - carrierAmplitude d₀ x u‖ :=
      norm_carrierKernel_sub_le d d₀ hchart x u
    _ ≤ (δ * ‖u.2‖) * (Real.sqrt ‖u.2‖ * M ^ 3) +
        Real.sqrt ‖u.2‖ * (3 * M ^ 2 * δ) :=
      add_le_add (mul_le_mul hphase hamp (norm_nonneg _) (by positivity)) hampDiff
    _ = _ := by ring

end JanetCartan.PhysicalInverseContinuity
