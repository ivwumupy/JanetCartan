module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.PhaseJets

/-!
# Buffered support of the weighted graph

All physical and conic masks in `app:ch_regular_base:eq:actual-matrix-inverse`
are retained. The original phase and matrix need only be smooth and nonsingular
on the buffered chart containing the mask's topological support. No global
invertibility is required by these continuity and support conclusions.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison WholeImageGeometry
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Both amplitudes vanish wherever the full mask vanishes, retaining physical
and conic support in `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedAmplitudes_eq_zero_of_mask_eq_zero
    (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat)
    {x u : E} (hc : c x u = 0) :
    maskedTransportAmplitude c U x u = 0 ∧ maskedWeightedAmplitude S c U x u = 0 := by
  simp [maskedTransportAmplitude, maskedWeightedAmplitude, hc]

/-- Both topological supports stay inside the original complete mask support.
This supplies the buffered-support input of the whole-image graph theorem in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem maskedAmplitudes_tsupport_subset
    (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat) :
    tsupport (Function.uncurry (maskedTransportAmplitude c U)) ⊆
      tsupport (Function.uncurry c) ∧
    tsupport (Function.uncurry (maskedWeightedAmplitude S c U)) ⊆
      tsupport (Function.uncurry c) := by
  constructor <;> apply closure_mono <;> intro q hq <;> by_contra hc
  · exact hq (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U (not_ne_iff.mp hc)).1
  · exact hq (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U (not_ne_iff.mp hc)).2

/-- Compact physical support is inherited literally from the mask. The same
`Kout` can be passed to the whole-image graph consumer of
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedAmplitudes_physical_support
    (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat)
    (Kout : Set E) (hc : ∀ x u, x ∉ Kout → c x u = 0) :
    (∀ x u, x ∉ Kout → maskedTransportAmplitude c U x u = 0) ∧
    (∀ x u, x ∉ Kout → maskedWeightedAmplitude S c U x u = 0) :=
  ⟨fun x u hx ↦ (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U (hc x u hx)).1,
    fun x u hx ↦ (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U (hc x u hx)).2⟩

/-- Local weighted smoothness from the original phase, complete mask and matrix.
Only the original determinant gaps on the buffered chart occur as premises.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeightedAmplitude_contDiffOn {S : E → E → ℝ}
    {c : E → E → ℝ} {U : E → E → Mat} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D))
    (hJ : ∀ x ∈ X, ∀ u ∈ D, phaseJacobian S x u ≠ 0)
    (hdet : ∀ x ∈ X, ∀ u ∈ D, (U x u).det ≠ 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (maskedWeightedAmplitude S c U)) (X ×ˢ D) := by
  let f : E × E → WeightedPrimitiveCoefficients n r :=
    fun q ↦ (c q.1 q.2, weightedPhaseDifferential S q.1 q.2, U q.1 q.2)
  have hf : ContDiffOn ℝ ∞ f (X ×ˢ D) :=
    hc.prodMk ((weightedPhaseDifferential_contDiffOn hX hD hcX hS).prodMk hU)
  have hcomp : ContDiffOn ℝ ∞ (weightedPrimitiveCoefficient ∘ f) (X ×ˢ D) := by
    intro q hq
    have hgap := hJ q.1 hq.1 q.2 hq.2
    rw [phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2] at hgap
    exact (weightedPrimitiveCoefficient_contDiffAt (abs_ne_zero.mp hgap)
      (hdet q.1 hq.1 q.2 hq.2)).comp_contDiffWithinAt q (hf q hq)
  apply hcomp.congr
  intro q hq
  dsimp [Function.uncurry, weightedPrimitiveCoefficient, f, maskedWeightedAmplitude]
  rw [phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2]

/-- Buffered mask support turns local weighted smoothness into global
smoothness, hence the global continuity required by the whole-image theorem.
There is no gap assumption off the chart in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedAmplitudes_contDiff {S : E → E → ℝ}
    {c : E → E → ℝ} {U : E → E → Mat} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D))
    (hJ : ∀ x ∈ X, ∀ u ∈ D, phaseJacobian S x u ≠ 0)
    (hdet : ∀ x ∈ X, ∀ u ∈ D, (U x u).det ≠ 0)
    (hbuffer : tsupport (Function.uncurry c) ⊆ X ×ˢ D) :
    ContDiff ℝ ∞ (Function.uncurry (maskedTransportAmplitude c U)) ∧
    ContDiff ℝ ∞ (Function.uncurry (maskedWeightedAmplitude S c U)) := by
  have ht : ContDiffOn ℝ ∞ (Function.uncurry (maskedTransportAmplitude c U)) (X ×ˢ D) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hc).smul hU
  have hw := maskedWeightedAmplitude_contDiffOn hX hD hcX hS hc hU hJ hdet
  have he (q : E × E) (hq : q ∉ X ×ˢ D) :
      Function.uncurry c =ᶠ[𝓝 q] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hq (hbuffer h))
  constructor <;> apply contDiff_iff_contDiffAt.mpr <;> intro q
  · by_cases hq : q ∈ X ×ˢ D
    · exact ht.contDiffAt ((hX.prod hD).mem_nhds hq)
    · apply (contDiffAt_const (c := (0 : Mat))).congr_of_eventuallyEq
      filter_upwards [he q hq] with p hp
      exact (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U hp).1
  · by_cases hq : q ∈ X ×ˢ D
    · exact hw.contDiffAt ((hX.prod hD).mem_nhds hq)
    · apply (contDiffAt_const (c := (0 : Mat))).congr_of_eventuallyEq
      filter_upwards [he q hq] with p hp
      exact (maskedAmplitudes_eq_zero_of_mask_eq_zero S c U hp).2

/-- A product physical/conic mask specializes to the literal paper weight,
including both factors, in `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeightedAmplitude_product_mask
    (S : E → E → ℝ) (χt χg : E → ℝ) (U : E → E → Mat) (x u : E) :
    maskedWeightedAmplitude S (fun x u ↦ χt x * χg u) U x u =
      (χt x : ℂ) • ((χg u : ℂ) •
        ((phaseJacobian S x u : ℂ) • ((U x u)⁻¹).conjTranspose)) := by
  ext i j
  simp [maskedWeightedAmplitude, weightedForwardAmplitude, reverseWeight,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

end JanetCartan.FourierIntegral.UncutNormal
