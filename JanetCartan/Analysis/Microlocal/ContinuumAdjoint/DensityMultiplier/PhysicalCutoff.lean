module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.CarrierJets
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Physical cutoff and real part in the density adjoint

The final operations in `app:ch_background:eq:bg-density-adjoint`, on physical
initial variables `(z,y)`. All derivatives below are full derivatives, including
both carrier and transverse initial coordinates. These smooth-data estimates
are inputs to the eventual closure on the shared carrier Sobolev scale.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

open ContinuumRow

variable {n : ℕ}

/-- The literal physical cutoff and two real quadratures applied to a physical
initial field (`app:ch_background:eq:bg-density-adjoint`). Here the second
coordinate is `y`, not Fourier frequency and not the auxiliary torus. -/
def densityPhysicalCutoff (χ : CarrierVariable n → ℝ) (u : CarrierVariable n → ℂ)
    (x : CarrierVariable n) : ℝ := 2 * (χ x • u x).re

private theorem norm_twoRe_jet_le (k : ℕ) {u : CarrierVariable n → ℂ}
    (hu : ContDiff ℝ ∞ u) (x : CarrierVariable n) :
    ‖iteratedFDeriv ℝ k (fun y ↦ 2 * (u y).re) x‖ ≤ 2 * ‖iteratedFDeriv ℝ k u x‖ := by
  have h := ((2 : ℝ) • Complex.reCLM).norm_iteratedFDeriv_comp_left
    (hu.contDiffAt (x := x)) (n := k) (by simp)
  simpa only [Function.comp_def, smul_apply, Complex.reCLM_apply,
    smul_eq_mul, norm_smul, Real.norm_ofNat, Complex.reCLM_norm, mul_one] using h

/-- Full Leibniz bound after the physical cutoff and real part, including
every `z` and `y` derivative of the cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityPhysicalCutoff_jet_le (k : ℕ)
    {χ : CarrierVariable n → ℝ} {u : CarrierVariable n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (M : ℕ → ℝ)
    (hbound : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M i)
    (x : CarrierVariable n) :
    ‖iteratedFDeriv ℝ k (densityPhysicalCutoff χ u) x‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        (2 * (k.choose i : ℝ) * M i) * ‖iteratedFDeriv ℝ (k - i) u x‖ := by
  calc
    _ ≤ 2 * ‖iteratedFDeriv ℝ k (fun y ↦ χ y • u y) x‖ :=
      norm_twoRe_jet_le k (hχ.smul hu) x
    _ ≤ 2 * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (k - i) u x‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hχ hu x (by simp))
        (by norm_num)
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hb := hbound i (by simpa using Finset.mem_range.mp hi) x
      calc
        _ ≤ 2 * ((k.choose i : ℝ) * M i * ‖iteratedFDeriv ℝ (k - i) u x‖) := by
          gcongr
        _ = _ := by ring

/-- Finite physical jet energies are preserved by the cutoff and real part,
with an explicit norm estimate. This is the smooth-data physical half of
`app:ch_background:eq:bg-density-adjoint`; it assumes no output estimate. -/
theorem densityPhysicalCutoff_jet_memLp_and_bound (k : ℕ)
    {χ : CarrierVariable n → ℝ} {u : CarrierVariable n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (M : ℕ → ℝ) (hM : ∀ i ≤ k, 0 ≤ M i)
    (hbound : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M i)
    (hmem : ∀ j ≤ k, MemLp (iteratedFDeriv ℝ j u) 2 (carrierMeasure n)) :
    MemLp (iteratedFDeriv ℝ k (densityPhysicalCutoff χ u)) 2 (carrierMeasure n) ∧
      lpNorm (iteratedFDeriv ℝ k (densityPhysicalCutoff χ u)) 2 (carrierMeasure n) ≤
      ∑ i ∈ Finset.range (k + 1), (2 * (k.choose i : ℝ) * M i) *
        lpNorm (iteratedFDeriv ℝ (k - i) u) 2 (carrierMeasure n) := by
  let c i := 2 * (k.choose i : ℝ) * M i
  let g i := fun x ↦ c i * ‖iteratedFDeriv ℝ (k - i) u x‖
  have hg i : MemLp (g i) 2 (carrierMeasure n) :=
    ((hmem (k - i) (Nat.sub_le _ _)).norm).const_mul (c i)
  have hsum := memLp_finsetSum (Finset.range (k + 1)) (fun i _ ↦ hg i)
  have hpt := norm_densityPhysicalCutoff_jet_le k hχ hu M hbound
  have hsmooth : ContDiff ℝ ∞ (densityPhysicalCutoff χ u) :=
    (((2 : ℝ) • Complex.reCLM).contDiff.comp (hχ.smul hu))
  constructor
  · exact hsum.mono' (hsmooth.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  · calc
      _ ≤ lpNorm (fun x ↦ ∑ i ∈ Finset.range (k + 1), g i x) 2 (carrierMeasure n) :=
        lpNorm_mono_real hsum hpt
      _ ≤ ∑ i ∈ Finset.range (k + 1), lpNorm (g i) 2 (carrierMeasure n) := by
        have he : (fun x ↦ ∑ i ∈ Finset.range (k + 1), g i x) =
            ∑ i ∈ Finset.range (k + 1), g i := by ext x; simp
        rw [he]
        exact lpNorm_sum_le (fun i (_ : i ∈ Finset.range (k + 1)) ↦ hg i)
          (by norm_num : (1 : ENNReal) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hc : 0 ≤ c i := by
          exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (hM i (by simpa using Finset.mem_range.mp hi))
        change lpNorm ((c i) • (fun x ↦ ‖iteratedFDeriv ℝ (k - i) u x‖))
          2 (carrierMeasure n) = _
        rw [lpNorm_const_smul, lpNorm_norm (hmem (k - i) (Nat.sub_le _ _)).aestronglyMeasurable]
        simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc, c]

/-- The same estimate before the physical cutoff, retaining the factor `2`
from the real density (`app:ch_background:eq:bg-density-adjoint`). -/
theorem twoRe_jet_memLp_and_bound (k : ℕ) {u : CarrierVariable n → ℂ}
    (hu : ContDiff ℝ ∞ u) (hmem : MemLp (iteratedFDeriv ℝ k u) 2 (carrierMeasure n)) :
    MemLp (iteratedFDeriv ℝ k (fun x ↦ 2 * (u x).re)) 2 (carrierMeasure n) ∧
      lpNorm (iteratedFDeriv ℝ k (fun x ↦ 2 * (u x).re)) 2 (carrierMeasure n) ≤
        2 * lpNorm (iteratedFDeriv ℝ k u) 2 (carrierMeasure n) := by
  have hg := hmem.norm.const_mul (2 : ℝ)
  have hsmooth : ContDiff ℝ ∞ (fun x ↦ 2 * (u x).re) :=
    (((2 : ℝ) • Complex.reCLM).contDiff.comp hu)
  constructor
  · exact hg.mono' (hsmooth.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_twoRe_jet_le k hu))
  · have h := lpNorm_mono_real hg (norm_twoRe_jet_le k hu)
    have he : lpNorm (fun x ↦ (2 : ℝ) * ‖iteratedFDeriv ℝ k u x‖) 2 (carrierMeasure n) =
        2 * lpNorm (iteratedFDeriv ℝ k u) 2 (carrierMeasure n) := by
      change lpNorm ((2 : ℝ) • (fun x ↦ ‖iteratedFDeriv ℝ k u x‖)) 2 (carrierMeasure n) = _
      rw [lpNorm_const_smul, lpNorm_norm hmem.aestronglyMeasurable]
      norm_num
    exact h.trans_eq he

end JanetCartan.ContinuumAdjoint.DensityMultiplier
