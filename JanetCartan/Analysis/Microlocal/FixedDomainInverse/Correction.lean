module

public import JanetCartan.Analysis.Operator.SmallSupport
public import JanetCartan.Analysis.Operator.GradedInverse

import Mathlib.Tactic.Abel

/-!
# Support and physical identity of the localized correction

The last step of `app:ch_regular:thm:exact-correction` in `paper.tex`, for the
actual L² operator `SmallSupport.localizedResidual`. The input `R` must be the
complete residual, with its original sign. No component is removed here.

These are conditional assembly lemmas: the contraction and the localized
parametrix identity are explicit inputs. Support and physical identities are
almost-everywhere statements on L² representatives. Identifying the resulting
class with a smooth function requires the concrete Sobolev scale and its
embedding theorem; no such identification is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace JanetCartan.FixedDomainInverse

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

open SmallSupport

/-- The corrected source `z = T (χ₂ h)` in
`app:ch_regular:thm:exact-correction`, using one base-space inverse. -/
def correctedSource (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U)) : Lp F 2 μ →L[ℝ] Lp F 2 μ :=
  (neumannInverse (localizedResidual hp χ₂ χ₃ hU R)).comp
    (bumpL2 (p := 2) le_rfl χ₂)

/-- The pointwise L² equation used to prove support containment in
`app:ch_regular:thm:exact-correction`. The zero extension is retained explicitly. -/
theorem correctedSource_coeFn (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1) (h : Lp F 2 μ) :
    correctedSource hp χ₂ χ₃ hU R h =ᵐ[μ] fun y ↦
      χ₂ y • h y - χ₂ y • U.indicator
        (R (bumpL2 (p := 2) le_rfl χ₃ (correctedSource hp χ₂ χ₃ hU R h))) y := by
  let z := correctedSource hp χ₂ χ₃ hU R h
  let K := localizedResidual hp χ₂ χ₃ hU R
  have hz : z = bumpL2 (p := 2) le_rfl χ₂ h - K z :=
    neumannInverse_eq_sub K hK _
  have heq : (z : E → F) =ᵐ[μ] fun y ↦
      (bumpL2 (p := 2) le_rfl χ₂ h) y - (K z) y := by
    conv_lhs => rw [hz]
    exact Lp.coeFn_sub _ _
  filter_upwards [heq, bumpL2_coeFn (p := 2) le_rfl χ₂ h,
    localizedResidual_coeFn hp χ₂ χ₃ hU R z] with y hy hχ hR
  exact hy.trans (congrArg₂ (fun a b : F ↦ a - b) hχ hR)

/-- The corrected source vanishes off `tsupport χ₂` almost everywhere
(`app:ch_regular:thm:exact-correction`). -/
theorem correctedSource_ae_zero_off_support (hp : 2 ≤ p) {x : E}
    (χ₂ χ₃ : ContDiffBump x) {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1) (h : Lp F 2 μ) :
    ∀ᵐ y ∂μ, y ∉ tsupport (χ₂ : E → ℝ) →
      correctedSource hp χ₂ χ₃ hU R h y = 0 := by
  filter_upwards [correctedSource_coeFn hp χ₂ χ₃ hU R hK h] with y hy
  intro hout
  rw [hy, image_eq_zero_of_notMem_tsupport hout]
  simp

/-- The source cutoff fixes the corrected source exactly in L², using its
plateau on the entire output support (`app:ch_regular:thm:exact-correction`). -/
theorem bumpL2_correctedSource (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) (h : Lp F 2 μ) :
    bumpL2 (p := 2) le_rfl χ₃ (correctedSource hp χ₂ χ₃ hU R h) =
      correctedSource hp χ₂ χ₃ hU R h := by
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₃
    (correctedSource hp χ₂ χ₃ hU R h),
    correctedSource_ae_zero_off_support hp χ₂ χ₃ hU R hK h] with y hχ hz
  rw [hχ]
  by_cases hy : y ∈ tsupport (χ₂ : E → ℝ)
  · rw [hnest y hy, one_smul]
  · rw [hz hy, smul_zero]

/-- On the output plateau, the *complete* residual satisfies `z + R z = h`
(`app:ch_regular:thm:exact-correction`). The domain condition removes precisely
the zero-extension indicator, and nesting removes precisely the source cutoff. -/
theorem correctedSource_add_residual (hp : 2 ≤ p) {x : E}
    (χ₂ χ₃ : ContDiffBump x) {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) (h : Lp F 2 μ) :
    ∀ᵐ y ∂μ, y ∈ U → χ₂ y = 1 →
      correctedSource hp χ₂ χ₃ hU R h y +
        R (correctedSource hp χ₂ χ₃ hU R h) y = h y := by
  have heq := correctedSource_coeFn hp χ₂ χ₃ hU R hK h
  rw [bumpL2_correctedSource hp χ₂ χ₃ hU R hK hnest h] at heq
  filter_upwards [heq] with y hy
  intro hyU hχ
  rw [hχ, one_smul, one_smul, indicator_of_mem hyU] at hy
  exact eq_sub_iff_add_eq.mp hy

/-- The physical identity `app:ch_regular:eq:exact-physical`, conditional on the
localized parametrix identity for supported inputs. `S` and `P` may take values
in a space of distributions; no bounded derivative on L² is assumed. Their
displayed representatives and the angular term `A` need only satisfy the exact
input identity. The final angular discrepancy remains in the conclusion. -/
theorem exact_physical_ae (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U)
    (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1)
    (hsupport : tsupport (χ₂ : E → ℝ) ⊆ U)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    {X : Type*} (S : Lp F 2 μ → X) (P : X → E → F) (A : Lp F 2 μ → E → F)
    (hparam : ∀ v : Lp F 2 μ, (∀ᵐ y ∂μ, y ∉ U → v y = 0) →
      ∀ᵐ y ∂μ, y ∈ U → P (S v) y = A v y + R v y) (h : Lp F 2 μ) :
    ∀ᵐ y ∂μ, y ∈ U → χ₂ y = 1 →
      P (S (correctedSource hp χ₂ χ₃ hU R h)) y =
        h y + (A (correctedSource hp χ₂ χ₃ hU R h) y -
          correctedSource hp χ₂ χ₃ hU R h y) := by
  have hs : ∀ᵐ y ∂μ, y ∉ U → correctedSource hp χ₂ χ₃ hU R h y = 0 := by
    filter_upwards [correctedSource_ae_zero_off_support hp χ₂ χ₃ hU R hK h] with y hy
    exact fun hout ↦ hy (fun hin ↦ hout (hsupport hin))
  filter_upwards [hparam _ hs,
    correctedSource_add_residual hp χ₂ χ₃ hU R hK hnest h] with y hP hz
  intro hyU hχ
  rw [hP hyU, ← hz hyU hχ]
  abel

end JanetCartan.FixedDomainInverse
