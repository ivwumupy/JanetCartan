module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Coordinates

/-!
# Spatial Taylor coefficients for both normal-amplitude positions

Reuse the existing freezing calculus for the full normal amplitude, before
any diagonal reduction. The origin-vanishing density difference is the concrete
consumer. A fixed proof cutoff retains compact physical support; it is one on
the original amplitude support. All derivative estimates lose exactly one
physical derivative. Source: `app:ch_background:prop:bg-frame`, Step 3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace NNReal
namespace JanetCartan.ContinuumNormal.ActualConstruction
open Pseudodifferential AmplitudeBound
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))

/-- The coordinate Taylor integral for BOTH physical positions of the normal
amplitude, using the existing freezing calculus
(`app:ch_background:prop:bg-frame`, Step 3). -/
def fullPositionTaylorCoefficient (b : E → P → ℂ) (i : Fin (2 * n))
    (ξ : E) (z : P) : ℂ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (b ξ) (t • z)
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

/-- The two-position Taylor coefficient is jointly smooth. This instantiates
`contDiff_freezingTaylorCoefficient` on the full amplitude, with its frequency
parameter retained (`app:ch_background:prop:bg-frame`, Step 3). -/
theorem contDiff_fullPositionTaylorCoefficient (b : E → P → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin (2 * n)) :
    ContDiff ℝ ∞ (Function.uncurry (fullPositionTaylorCoefficient b i)) := by
  let a : P → P → ℂ := fun z η ↦ b (freezingOutputProjection η) z
  have ha : ContDiff ℝ ∞ (Function.uncurry a) :=
    hb.comp ((freezingOutputProjection.contDiff.comp contDiff_snd).prodMk contDiff_fst)
  have ht := contDiff_freezingTaylorCoefficient a ha i
  have hh : ContDiff ℝ ∞ (fun p : E × P ↦
      freezingTaylorCoefficient a i p.2 (pairedPosition p.1 0)) :=
    ht.comp (contDiff_snd.prodMk
      (pairedPositionCLM.contDiff.comp (contDiff_fst.prodMk contDiff_const)))
  change ContDiff ℝ ∞ (fun p : E × P ↦ ∫ t in (0 : ℝ)..1,
    fderiv ℝ (b p.1) (t • p.2) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))
  simpa only [a, freezingTaylorCoefficient, freezingOutputProjection_pairedPosition] using hh

/-- Each physical derivative of the actual Taylor coefficient costs exactly
one primitive physical derivative, without a frequency derivative
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem norm_iteratedFDeriv_fullPositionTaylorCoefficient_le
    (b : E → P → ℂ) (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ))
    (i : Fin (2 * n)) (ξ : E) (k : ℕ) (M : ℝ)
    (hM : ∀ z, ‖iteratedFDeriv ℝ (k + 1) (b ξ) z‖ ≤ M) (z : P) :
    ‖iteratedFDeriv ℝ k (fullPositionTaylorCoefficient b i ξ) z‖ ≤ M := by
  let a : P → P → ℂ := fun z _ ↦ b ξ z
  have ha : ContDiff ℝ ∞ (Function.uncurry a) := (hb ξ).comp contDiff_fst
  let L : P →L[ℝ] P × P := ContinuousLinearMap.inl ℝ P P
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simp [L, Prod.norm_def]
  have hf : ContDiff ℝ ∞ (Function.uncurry (freezingTaylorCoefficient a i)) :=
    contDiff_freezingTaylorCoefficient a ha i
  have hh := norm_iteratedFDeriv_comp_linear_le L
    (Function.uncurry (freezingTaylorCoefficient a i)) hf k z
  change ‖iteratedFDeriv ℝ k (fullPositionTaylorCoefficient b i ξ) z‖ ≤ _ at hh
  apply hh.trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hL)).trans
  apply norm_iteratedFDeriv_freezingTaylorCoefficient_le a ha i (z, 0) k M
  intro t _
  have hfst : ‖ContinuousLinearMap.fst ℝ P P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.1‖ ≤ 1 * ‖p‖
    simpa only [one_mul] using norm_fst_le p
  exact (norm_iteratedFDeriv_comp_linear_le (ContinuousLinearMap.fst ℝ P P)
    (b ξ) (hb ξ) (k + 1) _).trans
      ((mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hfst)).trans (hM _))

/-- A fixed physical proof cutoff makes the two-position Taylor coefficient
compactly supported. It is independent of the eventual support radius
(`app:ch_background:prop:bg-frame`, Step 3). -/
def maskedFullPositionTaylorAmplitude (b : E → P → ℂ) (θ : P → ℝ)
    (i : Fin (2 * n)) (ξ : E) (z : P) : ℂ :=
  θ z • fullPositionTaylorCoefficient b i ξ z

/-- The fixed cutoff preserves joint smoothness of the Taylor amplitude
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem contDiff_maskedFullPositionTaylorAmplitude (b : E → P → ℂ) (θ : P → ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (hθ : ContDiff ℝ ∞ θ)
    (i : Fin (2 * n)) :
    ContDiff ℝ ∞ (Function.uncurry (maskedFullPositionTaylorAmplitude b θ i)) :=
  (hθ.comp contDiff_snd).smul (contDiff_fullPositionTaylorCoefficient b hb i)

/-- The Taylor operator retains the fixed proof box. This cutoff does not
change the original normal amplitude on its support
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem supportedInCenteredBox_maskedFullPositionTaylorAmplitude
    (b : E → P → ℂ) (θ : P → ℝ) (R : ℝ)
    (hθ : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (i : Fin (2 * n)) (ξ : E) :
    SupportedInCenteredBox R (maskedFullPositionTaylorAmplitude b θ i ξ) := by
  intro z hz
  exact hθ z (fun h ↦ hz (by simp [maskedFullPositionTaylorAmplitude, h]))

/-- The finite Leibniz budget for the constructed Taylor amplitude. The cutoff
budget and primitive budget precede the varying support radius and datum
(`app:ch_background:prop:bg-frame`, Step 3). -/
def fullPositionTaylorBudget (B M : ℝ≥0) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * B * M

/-- Primitive physical jets supply the existing PDO derivative interface for
the constructed Taylor amplitude, with a single derivative reserve
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem hasAmplitudeDerivativeBound_maskedFullPositionTaylorAmplitude
    (b : E → P → ℂ) (θ : P → ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (hθ : ContDiff ℝ ∞ θ)
    (B M : ℝ≥0) (N : ℕ)
    (hB : ∀ k ≤ N, ∀ z, ‖iteratedFDeriv ℝ k θ z‖ ≤ B)
    (hM : ∀ ξ k, k ≤ N + 1 → ∀ z, ‖iteratedFDeriv ℝ k (b ξ) z‖ ≤ M)
    (i : Fin (2 * n)) :
    HasAmplitudeDerivativeBound (maskedFullPositionTaylorAmplitude b θ i) N
      (fullPositionTaylorBudget B M N) := by
  have hbi (ξ : E) : ContDiff ℝ ∞ (b ξ) :=
    hb.comp (contDiff_const.prodMk contDiff_id)
  intro ξ is his z
  have ht : ContDiff ℝ ∞ (fullPositionTaylorCoefficient b i ξ) :=
    (contDiff_fullPositionTaylorCoefficient b hb i).comp
      (contDiff_const.prodMk contDiff_id)
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
    (hθ.smul ht) is z).trans
  apply (norm_iteratedFDeriv_smul_le hθ ht z (by simp)).trans
  apply le_trans (b := ∑ j ∈ Finset.range (is.length + 1),
    (is.length.choose j : ℝ) * B * M)
  · apply Finset.sum_le_sum
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hB j hjN z) (by positivity))
      (norm_iteratedFDeriv_fullPositionTaylorCoefficient_le b hbi i ξ
        (is.length - j) M (hM ξ _ (by omega)) z)
      (norm_nonneg _) (by positivity)
  · unfold fullPositionTaylorBudget
    exact Finset.single_le_sum
      (f := fun k : ℕ ↦ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B * M)
      (fun k _ ↦ by positivity)
      (show is.length ∈ Finset.range (N + 1) by simpa using his)

/-- Exact two-position freezing when the amplitude vanishes at the spatial
origin. The proof cutoff is one on the ORIGINAL amplitude support; both
physical coordinates remain in the Taylor sum
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem fullAmplitude_eq_sum_maskedFullPositionTaylorAmplitude
    (b : E → P → ℂ) (θ : P → ℝ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (hzero : ∀ ξ, b ξ 0 = 0)
    (hθ : ∀ ξ z, b ξ z ≠ 0 → θ z = 1) (ξ : E) (z : P) :
    b ξ z = ∑ i, z i • maskedFullPositionTaylorAmplitude b θ i ξ z := by
  have h := symbol_sub_frozen_eq_sum (fun z (_ : P) ↦ b ξ z) z 0
    (fun _ _ ↦ (hb ξ).of_le (by simp) |>.contDiffAt)
  have hmask : θ z • b ξ z = b ξ z := by
    by_cases hz : b ξ z = 0
    · simp [hz]
    · rw [hθ ξ z hz, one_smul]
  rw [hzero, sub_zero] at h
  calc
    b ξ z = θ z • b ξ z := hmask.symm
    _ = θ z • ∑ i, z i • fullPositionTaylorCoefficient b i ξ z := congrArg _ h
    _ = _ := by simp only [Finset.smul_sum, maskedFullPositionTaylorAmplitude]; congr 1; funext i; exact smul_comm _ _ _

end JanetCartan.ContinuumNormal.ActualConstruction
