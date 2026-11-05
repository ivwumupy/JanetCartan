module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NoncommRing

/-! # Variance of bounded positive sampling blocks

The operator calculation in `app:ch_waves:thm:sampling`, valid in any ordered
complex C⋆-algebra, in particular bounded operators on a complex Hilbert space.
-/

open MeasureTheory
open scoped CStarAlgebra

@[expose] public noncomputable section

namespace JanetCartan.Sampling

variable {A Ω : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `app:ch_waves:thm:sampling`: a positive block bounded by `R I` satisfies `X² ≤ R X`. -/
theorem square_le_smul_of_nonneg {a : A} {R : ℝ} (ha : 0 ≤ a)
    (haR : a ≤ R • (1 : A)) : a ^ 2 ≤ R • a := by
  have h := Commute.sub_left (Algebra.commutes (R := ℝ) R a) (Commute.refl a)
  rw [Algebra.algebraMap_eq_smul_one] at h
  have hp := h.mul_nonneg (sub_nonneg.mpr haR) ha
  simpa only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← sq,
    sub_nonneg] using hp

omit [PartialOrder A] [StarOrderedRing A] in
/-- `app:ch_waves:thm:sampling`: the noncommutative centered second-moment identity. -/
theorem integral_centered_square (X : Ω → A) (hX : Integrable X μ)
    (hX₂ : Integrable (fun ω => X ω ^ 2) μ) :
    (∫ ω, (X ω - ∫ ω, X ω ∂μ) ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 := by
  let m := ∫ ω, X ω ∂μ
  have he (ω : Ω) : (X ω - m) ^ 2 = X ω ^ 2 - X ω * m - m * X ω + m ^ 2 := by noncomm_ring
  change (∫ ω, (X ω - m) ^ 2 ∂μ) = _
  simp_rw [he]
  have h1 : Integrable (fun ω => X ω ^ 2 - X ω * m) μ := hX₂.sub (hX.mul_const m)
  have h2 : Integrable (fun ω => X ω ^ 2 - X ω * m - m * X ω) μ := h1.sub (hX.const_mul m)
  rw [integral_add h2 (integrable_const _),
    integral_sub h1 (hX.const_mul m),
    integral_sub hX₂ (hX.mul_const m), integral_mul_const_of_integrable hX,
    integral_const_mul_of_integrable hX]
  simp only [integral_const, probReal_univ, one_smul]
  dsimp [m]
  noncomm_ring

/-- `app:ch_waves:thm:sampling`: each block contributes at most `R E[X]` to variance.
Strong measurability and the almost-everywhere bounds suffice; no independence is needed here. -/
theorem block_variance_le (X : Ω → A) {R : ℝ} (hR : 0 ≤ R)
    (hX : AEStronglyMeasurable X μ)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hbound : ∀ᵐ ω ∂μ, X ω ≤ R • (1 : A)) :
    (∫ ω, (X ω - ∫ ω, X ω ∂μ) ^ 2 ∂μ) ≤ R • (∫ ω, X ω ∂μ) := by
  have hnorm : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ R := by
    filter_upwards [hpos, hbound] with ω hp hb
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hR hp).2
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hb)
  have hi : Integrable X μ := Integrable.of_bound hX R hnorm
  have hi₂ : Integrable (fun ω => X ω ^ 2) μ := by
    simpa only [sq] using hi.bdd_mul hX hnorm
  rw [integral_centered_square X hi hi₂]
  have hm : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg_of_ae hpos
  calc
    (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ :=
      sub_le_self _ hm.isSelfAdjoint.sq_nonneg
    _ ≤ ∫ ω, R • X ω ∂μ := by
      apply integral_mono_ae hi₂ (hi.smul R)
      filter_upwards [hpos, hbound] with ω hp hb
      exact square_le_smul_of_nonneg hp hb
    _ = R • (∫ ω, X ω ∂μ) := integral_smul R X

/-- `app:ch_waves:thm:sampling`: summing the block estimates gives `V ≤ R E_h`,
where the two operators are the actual sums of centered second moments and expectations.
The same result applies to any fixed prefix, with the same `R`. -/
theorem sum_block_variance_le {ι : Type*} (s : Finset ι) (X : ι → Ω → A)
    {R : ℝ} (hR : 0 ≤ R) (hX : ∀ q ∈ s, AEStronglyMeasurable (X q) μ)
    (hpos : ∀ q ∈ s, ∀ᵐ ω ∂μ, 0 ≤ X q ω)
    (hbound : ∀ q ∈ s, ∀ᵐ ω ∂μ, X q ω ≤ R • (1 : A)) :
    (∑ q ∈ s, ∫ ω, (X q ω - ∫ ω, X q ω ∂μ) ^ 2 ∂μ) ≤
      R • (∑ q ∈ s, ∫ ω, X q ω ∂μ) := by
  rw [Finset.smul_sum]
  exact Finset.sum_le_sum fun q hq => block_variance_le (X q) hR
    (hX q hq) (hpos q hq) (hbound q hq)

end JanetCartan.Sampling
