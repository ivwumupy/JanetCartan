module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Actual cutoff and exterior operators

Bounded multiplication on the full real torus L² space, including the literal
adjoint and the vanishing of the exterior channel on the core in
`app:ch_background:defn:bg-row`. No oscillatory estimate is used here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

/-- Multiplication on vector-valued L² by an actual L∞ coefficient
(`app:ch_background:defn:bg-row`). -/
def coefficientMultiplier (a : Lp ℝ ∞ (volume : Measure (Torus n))) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL volume ∞ 2 2 a

/-- Pointwise meaning of cutoff multiplication (`app:ch_background:defn:bg-row`). -/
theorem coefficientMultiplier_coeFn (a : Lp ℝ ∞ (volume : Measure (Torus n)))
    (f : OutputL2 n) : coefficientMultiplier a f =ᵐ[volume] fun x ↦ a x • f x :=
  (ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder a f

/-- Boundedness of real cutoff multiplication (`app:ch_background:defn:bg-row`). -/
theorem coefficientMultiplier_norm_le (a : Lp ℝ ∞ (volume : Measure (Torus n))) :
    ‖coefficientMultiplier a‖ ≤ ‖a‖ := by
  calc
    ‖coefficientMultiplier a‖ ≤
        ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := Euclidean n)).holderL volume ∞ 2 2‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.opNorm_lsmul_le)
      (norm_nonneg _)
    _ = ‖a‖ := one_mul _

/-- The literal real adjoint of multiplication is itself
(`app:ch_background:defn:bg-row`). -/
theorem coefficientMultiplier_adjoint (a : Lp ℝ ∞ (volume : Measure (Torus n))) :
    (coefficientMultiplier a).adjoint = coefficientMultiplier a := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientMultiplier_coeFn a f, coefficientMultiplier_coeFn a g]
    with x hf hg
  rw [hf, hg, real_inner_smul_left, inner_smul_right]

/-- Multiplication by a continuous torus cutoff; smooth manuscript cutoffs are
special cases (`app:ch_background:defn:bg-row`). -/
def cutoffMultiplier (χ : C(Torus n, ℝ)) : OutputL2 n →L[ℝ] OutputL2 n :=
  coefficientMultiplier (ContinuousMap.toLp ∞ volume ℝ χ)

/-- The cutoff operator has exactly its advertised pointwise action
(`app:ch_background:defn:bg-row`). -/
theorem cutoffMultiplier_coeFn (χ : C(Torus n, ℝ)) (f : OutputL2 n) :
    cutoffMultiplier χ f =ᵐ[volume] fun x ↦ χ x • f x := by
  filter_upwards [coefficientMultiplier_coeFn (ContinuousMap.toLp ∞ volume ℝ χ) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) volume χ] with x hf hχ
  simpa only [cutoffMultiplier, hχ] using hf

/-- The sup norm controls the cutoff operator (`app:ch_background:defn:bg-row`). -/
theorem cutoffMultiplier_norm_le (χ : C(Torus n, ℝ)) : ‖cutoffMultiplier χ‖ ≤ ‖χ‖ := by
  apply (coefficientMultiplier_norm_le _).trans
  calc
    ‖ContinuousMap.toLp ∞ volume ℝ χ‖ ≤ ‖ContinuousMap.toLp (E := ℝ) ∞ (volume : Measure (Torus n)) ℝ‖ * ‖χ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖χ‖ := mul_le_mul_of_nonneg_right
      (by simpa using (ContinuousMap.toLp_norm_le (p := ∞) (E := ℝ)
        (𝕜 := ℝ) (volume : Measure (Torus n)))) (norm_nonneg _)
    _ = ‖χ‖ := one_mul _

/-- Real cutoff multiplication is self-adjoint (`app:ch_background:defn:bg-row`). -/
theorem cutoffMultiplier_adjoint (χ : C(Torus n, ℝ)) :
    (cutoffMultiplier χ).adjoint = cutoffMultiplier χ :=
  coefficientMultiplier_adjoint _

/-- The actual auxiliary exterior channel `A_out = 1 - ψ`
(`app:ch_background:defn:bg-row`). -/
def exteriorChannel (ψ : C(Torus n, ℝ)) : OutputL2 n →L[ℝ] OutputL2 n :=
  cutoffMultiplier (1 - ψ)

/-- Pointwise exterior-channel formula (`app:ch_background:defn:bg-row`). -/
theorem exteriorChannel_coeFn (ψ : C(Torus n, ℝ)) (f : OutputL2 n) :
    exteriorChannel ψ f =ᵐ[volume] fun x ↦ (1 - ψ x) • f x :=
  cutoffMultiplier_coeFn (1 - ψ) f

/-- Boundedness on the full exterior input (`app:ch_background:prop:bg-frame`). -/
theorem exteriorChannel_norm_le (ψ : C(Torus n, ℝ)) :
    ‖exteriorChannel ψ‖ ≤ ‖1 - ψ‖ := cutoffMultiplier_norm_le _

/-- The exterior channel is literally self-adjoint (`app:ch_background:defn:bg-row`). -/
theorem exteriorChannel_adjoint (ψ : C(Torus n, ℝ)) :
    (exteriorChannel ψ).adjoint = exteriorChannel ψ := cutoffMultiplier_adjoint _

/-- The auxiliary exterior channel vanishes on the core whenever `ψ = 1` there
(`app:ch_background:prop:bg-frame`). This is an almost-everywhere assertion on L² classes. -/
theorem exteriorChannel_zero_on_core (ψ : C(Torus n, ℝ)) (core : Set (Torus n))
    (hψ : ∀ x ∈ core, ψ x = 1) (f : OutputL2 n) :
    ∀ᵐ x ∂volume, x ∈ core → exteriorChannel ψ f x = 0 := by
  filter_upwards [exteriorChannel_coeFn ψ f] with x hx
  intro hcore
  simp [hx, hψ x hcore]

/-- The exterior construction agrees with the abstract complement used in the
normal augmentation lemmas (`app:ch_background:defn:bg-row`). -/
theorem exteriorChannel_eq_sub (ψ : C(Torus n, ℝ)) :
    exteriorChannel ψ = ContinuousLinearMap.id ℝ (OutputL2 n) - cutoffMultiplier ψ := by
  ext1 f
  apply Lp.ext
  filter_upwards [exteriorChannel_coeFn ψ f, cutoffMultiplier_coeFn ψ f,
    Lp.coeFn_sub f (cutoffMultiplier ψ f)] with x he hc hs
  change exteriorChannel ψ f x = (f - cutoffMultiplier ψ f) x
  rw [he, hs, Pi.sub_apply, hc, sub_smul, one_smul]

end JanetCartan.ContinuumRow
