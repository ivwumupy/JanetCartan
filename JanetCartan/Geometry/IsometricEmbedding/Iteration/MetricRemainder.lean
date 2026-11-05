module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder.TensorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Scales
public import JanetCartan.Analysis.ContDiff.Norm.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cubic metric remainders and cutoff stability

The last two terms of `main:eq:metric-ledger` are bounded in the Frobenius norm
using the actual finite-dimensional differentials. Derivative bounds with amplitudes
δ and δ² imply the cubic estimate with the fixed `cubicLoss` exponent B₃.

The estimates are conditional on the stated derivative profiles. In particular, this
module does not derive C¹ bounds from `main:eq:joint-physical-profile`, construct the
fields, or establish a Fourier cutoff tail. It proves the tensor estimates and the
C¹ metric stability needed once those analytic inputs are available.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

/-- The last two terms in `main:eq:metric-ledger`: the symmetrized mixed tensor
`(dP)ᵀ dW + (dW)ᵀ dP` and the quadratic secondary tensor `(dW)ᵀ dW`. -/
def metricRemainder {n N : ℕ} (P W : Euclidean n → Euclidean N) :
    MetricField n := linearizedMetric P W + inducedMetric W

variable {n N : ℕ} {P W F E : Euclidean n → Euclidean N} {x : Euclidean n}
  {s : Set (Euclidean n)}

/-- `main:eq:metric-ledger`: the remainder is controlled by bounds for the actual
differentials of the two fields. -/
theorem norm_metricRemainder_le_of_fderiv_bounds {p w : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hP : ‖fderiv ℝ P x‖ ≤ p) (hW : ‖fderiv ℝ W x‖ ≤ w) :
    ‖metricRemainder P W x‖ ≤ n * (2 * p * w + w ^ 2) := by
  calc
    _ ≤ ‖linearizedMetric P W x‖ + ‖inducedMetric W x‖ := norm_add_le _ _
    _ ≤ 2 * n * ‖fderiv ℝ P x‖ * ‖fderiv ℝ W x‖ + n * ‖fderiv ℝ W x‖ ^ 2 :=
      add_le_add (norm_linearizedMetric_le P W x) (norm_inducedMetric_le W x)
    _ ≤ 2 * n * p * w + n * w ^ 2 := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hW
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hw).2 hW)
          (Nat.cast_nonneg n)
    _ = _ := by ring

/-- `main:eq:metric-ledger`: one primary factor of δ and one secondary factor of δ²
produce cubic smallness; the secondary square is absorbed using δ ≤ 1. -/
theorem norm_metricRemainder_le_cubic {C δ L : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hL : 0 ≤ L)
    (hP : ‖fderiv ℝ P x‖ ≤ C * δ * L)
    (hW : ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * L) :
    ‖metricRemainder P W x‖ ≤ 3 * n * C ^ 2 * δ ^ 3 * L ^ 2 := by
  have hpow : δ ^ 4 ≤ δ ^ 3 := by
    calc
      δ ^ 4 = δ ^ 3 * δ := by ring
      _ ≤ δ ^ 3 * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = δ ^ 3 := mul_one _
  calc
    _ ≤ n * (2 * (C * δ * L) * (C * δ ^ 2 * L) + (C * δ ^ 2 * L) ^ 2) :=
      norm_metricRemainder_le_of_fderiv_bounds (by positivity) (by positivity) hP hW
    _ = (n * C ^ 2 * L ^ 2) * (2 * δ ^ 3 + δ ^ 4) := by ring
    _ ≤ (n * C ^ 2 * L ^ 2) * (2 * δ ^ 3 + δ ^ 3) := by gcongr
    _ = _ := by ring

/-- `main:eq:joint-physical-profile`: a common derivative loss `Rᵃ` gives the squared
loss `R^(2a)` in the cubic remainder. -/
theorem norm_metricRemainder_le_rpow {C δ R a : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hP : ‖fderiv ℝ P x‖ ≤ C * δ * R ^ a)
    (hW : ‖fderiv ℝ W x‖ ≤ C * δ ^ 2 * R ^ a) :
    ‖metricRemainder P W x‖ ≤ 3 * n * C ^ 2 * δ ^ 3 * R ^ (2 * a) := by
  have h := norm_metricRemainder_le_cubic hC hδ.le hδ1 (Real.rpow_nonneg hR a) hP hW
  simpa only [mul_comm 2 a, Real.rpow_mul hR, Real.rpow_two] using h

/-- `main:eq:step-error`: a uniform Frobenius bound gives the domain C⁰ bound,
including for the empty domain. -/
theorem cNorm_zero_le_of_norm_bound {G : Euclidean n → MetricTensor n} {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ x ∈ s, ‖G x‖ ≤ B) : cNorm s 0 G ≤ B := by
  rw [cNorm_order_zero]
  exact Real.sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hG x hx) hB

/-- `main:eq:metric-ledger`, `main:eq:joint-physical-profile`: the cubic C⁰ estimate
with the manuscript's fixed exponent B₃. The hypotheses are the C¹ derivative bounds obtained
from the physical profiles by Fourier estimates. That analytic input is not proved here. -/
theorem cNorm_metricRemainder_le_cubicLoss {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hP : ∀ x ∈ s, ‖fderiv ℝ P x‖ ≤
      C * δ * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hW : ∀ x ∈ s, ‖fderiv ℝ W x‖ ≤
      C * δ ^ 2 * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2))) :
    cNorm s 0 (metricRemainder P W) ≤ 3 * n * C ^ 2 * δ ^ 3 * R ^ cubicLoss n := by
  apply cNorm_zero_le_of_norm_bound (by positivity)
  intro x hx
  have he : cubicLoss n =
      2 * (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) := by
    unfold cubicLoss
    ring
  rw [he]
  exact norm_metricRemainder_le_rpow hC hδ hδ1 hR (hP x hx) (hW x hx)

/-- `main:eq:metric-expansion`: the exact metric change caused by an added field.
Applied at `F + P + W₂`, this is the cutoff contribution following `main:eq:joint-physical-profile`. -/
theorem inducedMetric_add_sub_eq_metricRemainder
    (hF : DifferentiableAt ℝ F x) (hE : DifferentiableAt ℝ E x) :
    inducedMetric (F + E) x - inducedMetric F x = metricRemainder F E x := by
  rw [inducedMetric_add hF hE]
  change _ = linearizedMetric F E x + inducedMetric E x
  abel

/-- `main:eq:step-error`: pointwise metric stability under a C¹ perturbation,
with the quadratic term retained. -/
theorem norm_inducedMetric_add_sub_le {M ε : ℝ}
    (hF : DifferentiableAt ℝ F x) (hE : DifferentiableAt ℝ E x)
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hFM : ‖fderiv ℝ F x‖ ≤ M) (hEε : ‖fderiv ℝ E x‖ ≤ ε) :
    ‖inducedMetric (F + E) x - inducedMetric F x‖ ≤ n * (2 * M * ε + ε ^ 2) := by
  rw [inducedMetric_add_sub_eq_metricRemainder hF hE]
  exact norm_metricRemainder_le_of_fderiv_bounds hM hε hFM hEε

/-- `main:eq:step-error`: uniform differential bounds control the C⁰ metric change.
The differentiability assumptions concern the ambient derivatives used in the definitions. -/
theorem cNorm_inducedMetric_add_sub_le_of_fderiv_bounds {M ε : ℝ}
    (hF : ∀ x ∈ s, DifferentiableAt ℝ F x) (hE : ∀ x ∈ s, DifferentiableAt ℝ E x)
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hFM : ∀ x ∈ s, ‖fderiv ℝ F x‖ ≤ M) (hEε : ∀ x ∈ s, ‖fderiv ℝ E x‖ ≤ ε) :
    cNorm s 0 (inducedMetric (F + E) - inducedMetric F) ≤ n * (2 * M * ε + ε ^ 2) := by
  apply cNorm_zero_le_of_norm_bound (by positivity)
  intro x hx
  exact norm_inducedMetric_add_sub_le (hF x hx) (hE x hx) hM hε (hFM x hx) (hEε x hx)

/-- `main:eq:step-error`: C¹-to-C⁰ metric stability on a compact domain, sufficient
to estimate the contribution of `E_cut`. Only C¹ regularity at points of the domain is needed. -/
theorem cNorm_inducedMetric_add_sub_le (hs : IsCompact s)
    (hF : ∀ x ∈ s, ContDiffAt ℝ 1 F x) (hE : ∀ x ∈ s, ContDiffAt ℝ 1 E x) :
    cNorm s 0 (inducedMetric (F + E) - inducedMetric F) ≤
      n * (2 * cNorm s 1 F * cNorm s 1 E + cNorm s 1 E ^ 2) := by
  apply cNorm_inducedMetric_add_sub_le_of_fderiv_bounds
    (fun x hx ↦ (hF x hx).differentiableAt (by norm_num))
    (fun x hx ↦ (hE x hx).differentiableAt (by norm_num))
    (cNorm_nonneg s 1 F) (cNorm_nonneg s 1 E)
  · intro x hx
    simpa only [norm_iteratedFDeriv_one] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hF hx (le_refl 1)
  · intro x hx
    simpa only [norm_iteratedFDeriv_one] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hE hx (le_refl 1)

/-- `main:eq:step-error`, after `main:eq:joint-physical-profile`: a cutoff derivative
tail with decay `δ R^(-Q-b)` absorbs background derivative growth `Rᵇ`. The tail estimate and
background bound are explicit analytic inputs; this theorem proves their metric consequence. -/
theorem cNorm_metric_cutoff_le {CF CE δ R b Q : ℝ}
    (hF : ∀ x ∈ s, DifferentiableAt ℝ F x) (hE : ∀ x ∈ s, DifferentiableAt ℝ E x)
    (hCF : 0 ≤ CF) (hCE : 0 ≤ CE) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 1 ≤ R) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hFM : ∀ x ∈ s, ‖fderiv ℝ F x‖ ≤ CF * R ^ b)
    (hEε : ∀ x ∈ s, ‖fderiv ℝ E x‖ ≤ CE * δ * R ^ (-Q - b)) :
    cNorm s 0 (inducedMetric (F + E) - inducedMetric F) ≤
      n * (2 * CF * CE + CE ^ 2) * δ * R ^ (-Q) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0 ≤ R ^ (-Q - b) := Real.rpow_nonneg hR0.le _
  have ht1 : R ^ (-Q - b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have htq : R ^ (-Q - b) ≤ R ^ (-Q) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hprod : R ^ b * R ^ (-Q - b) = R ^ (-Q) := by
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  have hsquare : δ ^ 2 * (R ^ (-Q - b)) ^ 2 ≤ δ * R ^ (-Q) := by
    have ht : δ * R ^ (-Q - b) ≤ 1 :=
      (mul_le_mul hδ1 ht1 ht0 zero_le_one).trans_eq (one_mul 1)
    calc
      δ ^ 2 * (R ^ (-Q - b)) ^ 2 = (δ * R ^ (-Q - b)) ^ 2 := by ring
      _ ≤ δ * R ^ (-Q - b) := by
        simpa only [pow_two, mul_one] using
          mul_le_mul_of_nonneg_left ht (mul_nonneg hδ.le ht0)
      _ ≤ δ * R ^ (-Q) := mul_le_mul_of_nonneg_left htq hδ.le
  calc
    _ ≤ n * (2 * (CF * R ^ b) * (CE * δ * R ^ (-Q - b)) +
        (CE * δ * R ^ (-Q - b)) ^ 2) :=
      cNorm_inducedMetric_add_sub_le_of_fderiv_bounds hF hE
        (by positivity) (by positivity) hFM hEε
    _ = n * (2 * CF * CE * δ * (R ^ b * R ^ (-Q - b)) +
        CE ^ 2 * (δ ^ 2 * (R ^ (-Q - b)) ^ 2)) := by ring
    _ ≤ n * (2 * CF * CE * δ * R ^ (-Q) + CE ^ 2 * (δ * R ^ (-Q))) := by
      rw [hprod]
      gcongr
    _ = _ := by ring

end JanetCartan
