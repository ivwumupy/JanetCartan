module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointTaylor
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual coefficients for freezing a symbol

The Taylor integral in `app:ch_background:prop:bg-frame`, Step 3. The identity
only requires smoothness on the fixed open star-shaped physical neighborhood.
The cutoff is fixed before a small support radius is chosen. These statements
apply to matrix-valued symbols as well as scalar symbols; they do not assert
an L² realization of the resulting operators.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumNormal

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_background:prop:bg-frame`, Step 3: the literal coordinate Taylor
integral of the completed symbol, before applying a fixed physical cutoff. -/
def freezingTaylorCoefficient (a : E → E → F) (i : Fin d) (x ξ : E) : F :=
  ∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun z ↦ a z ξ) (t • x) (EuclideanSpace.basisFun (Fin d) ℝ i)

/-- `app:ch_background:prop:bg-frame`, Step 3: a fixed physical extension.
The Taylor identity for this symbol is claimed only on the plateau of `β`. -/
def extendedFreezingTaylorCoefficient (a : E → E → F) (β : E → ℝ)
    (i : Fin d) (x ξ : E) : F :=
  β x • freezingTaylorCoefficient a i x ξ

/-- `app:ch_background:prop:bg-frame`, Step 3: exact symbol Taylor identity.
Only the segment from zero to the evaluation point needs to be smooth. -/
theorem symbol_sub_frozen_eq_sum [CompleteSpace F]
    (a : E → E → F) (x ξ : E)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 (fun z ↦ a z ξ) (t • x)) :
    a x ξ - a 0 ξ = ∑ i, x i • freezingTaylorCoefficient a i x ξ := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ (fun z ↦ a z ξ) (t • x))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact (((ha t ht').continuousAt_fderiv (by simp)).comp (f := fun s : ℝ ↦ s • x)
      (show ContinuousAt (fun s : ℝ ↦ s • x) t from by fun_prop)).continuousWithinAt
  have h := amplitude_eq_diagonal_add_integral (fun z ↦ a z ξ) 0 x
    (by simpa using ha)
  let L : E →L[ℝ] F := ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z ↦ a z ξ) (t • x)
  have hsum := congrArg L
    ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x)
  change L (∑ i, x i • EuclideanSpace.basisFun (Fin d) ℝ i) = L x at hsum
  rw [map_sum] at hsum
  simp only [map_smul] at hsum
  simp only [L, ContinuousLinearMap.intervalIntegral_apply hint] at hsum
  change a x ξ - a 0 ξ = ∑ i, x i • (∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun z ↦ a z ξ) (t • x) (EuclideanSpace.basisFun (Fin d) ℝ i))
  rw [hsum]
  exact sub_eq_iff_eq_add.mpr (by simpa only [zero_add, sub_zero] using h.trans (add_comm _ _))

/-- `app:ch_background:prop:bg-frame`, Step 3: the star-shaped neighborhood
supplies all segments used in the symbol Taylor identity. -/
theorem symbol_sub_frozen_eq_sum_on [CompleteSpace F]
    (a : E → E → F) {U : Set E} (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (ha : ∀ ξ, ContDiffOn ℝ 1 (fun z ↦ a z ξ) U) {x : E} (hx : x ∈ U) (ξ : E) :
    a x ξ - a 0 ξ = ∑ i, x i • freezingTaylorCoefficient a i x ξ := by
  apply symbol_sub_frozen_eq_sum
  intro t ht
  exact (ha ξ).contDiffAt (hU.mem_nhds (hstar.smul_mem hx ht.1 ht.2))

/-- `app:ch_background:prop:bg-frame`, Step 3: the fixed extension agrees
with the Taylor decomposition precisely where its physical mask is one. -/
theorem symbol_sub_frozen_eq_sum_extended [CompleteSpace F]
    (a : E → E → F) (β : E → ℝ) {U : Set E} (hU : IsOpen U)
    (hstar : StarConvex ℝ 0 U) (ha : ∀ ξ, ContDiffOn ℝ 1 (fun z ↦ a z ξ) U)
    {x : E} (hx : x ∈ U) (hβ : β x = 1) (ξ : E) :
    a x ξ - a 0 ξ = ∑ i, x i • extendedFreezingTaylorCoefficient a β i x ξ := by
  simpa only [extendedFreezingTaylorCoefficient, hβ, one_smul] using
    symbol_sub_frozen_eq_sum_on a hU hstar ha hx ξ

/-- `app:ch_background:prop:bg-frame`, Step 3: a primitive first derivative
bound gives a uniform zeroth-order Taylor coefficient bound, independent of `r`. -/
theorem norm_freezingTaylorCoefficient_le (a : E → E → F) (i : Fin d) (x ξ : E)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fun z ↦ a z ξ) (t • x)‖ ≤ M) :
    ‖freezingTaylorCoefficient a i x ξ‖ ≤ M := by
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) ?_).trans_eq (by simp)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨(by simpa using ht : 0 < t ∧ t ≤ 1).1.le,
    (by simpa using ht : 0 < t ∧ t ≤ 1).2⟩
  exact ((fderiv ℝ (fun z ↦ a z ξ) (t • x)).le_opNorm _).trans
    (by simpa only [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one, mul_one] using hM t ht')

/-- `app:ch_background:prop:bg-frame`, Step 3: the fixed extension has
physical support inside its fixed cutoff support. -/
theorem support_extendedFreezingTaylorCoefficient_subset
    (a : E → E → F) (β : E → ℝ) (i : Fin d) (ξ : E) :
    Function.support (fun x ↦ extendedFreezingTaylorCoefficient a β i x ξ) ⊆
      Function.support β :=
  Function.support_smul_subset_left β (fun x ↦ freezingTaylorCoefficient a i x ξ)

end JanetCartan.ContinuumNormal
