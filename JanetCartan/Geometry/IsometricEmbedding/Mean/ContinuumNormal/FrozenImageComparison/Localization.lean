module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.InnerCutoff
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2

/-!
# Supported inputs for the frozen image comparison

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, retain the fixed outer
cutoffs at radius `R`, and allow the input support radius `r ≤ R` to vary.
The lift is the existing cell zero extension. Its norm and integral identities
use the proved measure-preserving quotient, including normalized Haar measure.
These facts are inputs to the frozen periodic image energy comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {r R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The variable support ball fits the fixed outer cell
(`app:ch_background:prop:bg-frame`, small-support step). -/
theorem innerBall_subset_cell (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (hrR : r ≤ R) : ball (0 : E) r ⊆ halfOpenCell n := by
  apply (ball_subset_closedBall.trans (closedBall_subset_closedBall
    (show r ≤ 4 * R by linarith))).trans
  exact FixedCutoffs.closedBall_four_subset_cell hcell

/-- Quotient-ball support becomes literal physical support under the existing
zero extension (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem toEuclidean_supported_innerBall
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (f : OutputL2 n)
    (hf : ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) :
    ∀ᵐ x ∂volume, x ∉ ball (0 : E) r → toEuclidean (𝕜 := ℝ) f x = 0 := by
  apply toEuclidean_supported
  rwa [torusChart_eq_image (innerBall_subset_cell hR hcell hrR)]

/-- The physical zero extension preserves the exact norm, with no Jacobian
or Fourier normalization factor (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_zeroExtension (f : OutputL2 n) :
    ‖toEuclidean (𝕜 := ℝ) f‖ = ‖f‖ := toEuclidean.norm_map f

/-- The actual cell zero extension is in L¹ as well as L². This justifies
the ordinary Fourier integral in the frozen comparison
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_zeroExtension (f : OutputL2 n) :
    Integrable (toEuclidean (𝕜 := ℝ) f : E → E) := by
  have hf : Integrable (f : Torus n → E) := (Lp.memLp f).integrable (by norm_num)
  have hl : IntegrableOn (periodicLift f) (halfOpenCell n) :=
    measurePreserving_quotient.integrable_comp_of_integrable hf
  exact ((integrable_indicator_iff measurableSet_halfOpenCell).mpr hl).congr
    (toEuclidean_coe (𝕜 := ℝ) f).symm

/-- The error's L¹ quantity is unchanged by zero extension, using literal
Lebesgue and normalized Haar integrals (`app:ch_background:prop:bg-frame`). -/
theorem integral_norm_zeroExtension (f : OutputL2 n) :
    (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) = ∫ z, ‖f z‖ := by
  calc
    (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) =
        ∫ x, (halfOpenCell n).indicator (fun x ↦ ‖periodicLift f x‖) x := by
      apply integral_congr_ae
      filter_upwards [toEuclidean_coe (𝕜 := ℝ) f] with x hx
      rw [hx]
      by_cases h : x ∈ halfOpenCell n <;> simp [h]
    _ = ∫ x in halfOpenCell n, ‖periodicLift f x‖ :=
      integral_indicator measurableSet_halfOpenCell
    _ = ∫ z, ‖f z‖ := integral_periodicLift (fun z ↦ ‖f z‖)

/-- Every fixed outer cutoff is one on the variable inner ball. Its choice
precedes `r` (`app:ch_background:prop:bg-frame`, small-support step). -/
theorem fixedCutoff_one_on_innerBall
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (i : Fin 3) {z : Torus n} (hz : z ∈ torusQuotient '' ball (0 : E) r) :
    FixedCutoffs.periodic hR hcell i z = 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [FixedCutoffs.periodic_apply,
    centeredTorusRepresentative_quotient (innerBall_subset_cell hR hcell hrR hx)]
  apply interior_subset (FixedCutoffs.physical_plateau hR i _)
  apply (closedBall_subset_closedBall (show r ≤ ((i : ℕ) + 1 : ℝ) * R by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    nlinarith)) (ball_subset_closedBall hx)

/-- Multiplication by either fixed outer mask fixes every supported L² input,
without a smoothness assumption on that input (`app:ch_background:prop:bg-frame`). -/
theorem fixedCutoff_fixes_supported
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (i : Fin 3) (f : OutputL2 n)
    (hf : ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) :
    cutoffMultiplier (FixedCutoffs.periodic hR hcell i) f = f := by
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn (FixedCutoffs.periodic hR hcell i) f, hf]
    with z hz hzf
  rw [hz]
  by_cases hs : z ∈ torusQuotient '' ball (0 : E) r
  · rw [fixedCutoff_one_on_innerBall hR hcell hrR i hs, one_smul]
  · rw [hzf hs, smul_zero]

end JanetCartan.ContinuumNormal.FrozenImageComparison
