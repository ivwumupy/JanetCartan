module

public import JanetCartan.Analysis.Matrix.InverseBounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform inverse differential bounds from a determinant gap

The compact set used here consists of all linear maps with a specified norm
bound and determinant gap. It is fixed before choosing the phase family in
`app:ch_osc:setup:osc-normal`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.NormalComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The determinant gap in `app:ch_osc:setup:osc-normal` implies invertibility
of a finite dimensional differential. -/
theorem isInvertible_of_det_gap {A : E →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ) (hA : δ ≤ |A.det|) : A.IsInvertible := by
  have hu : IsUnit A.toLinearMap.det := isUnit_iff_ne_zero.mpr
    (abs_pos.mp (hδ.trans_le hA))
  refine ⟨(LinearMap.equivOfIsUnitDet hu).toContinuousLinearEquiv, ?_⟩
  ext v
  exact LinearMap.equivOfIsUnitDet_apply hu v

/-- A norm bound and determinant gap control the inverse differential,
uniformly before a family is selected (`app:ch_osc:prop:osc-normal`). -/
theorem exists_norm_inverse_le_of_det_gap (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K > 0, ∀ A : E →L[ℝ] E, ‖A‖ ≤ B → δ ≤ |A.det| → ‖A.inverse‖ ≤ K := by
  let S : Set (E →L[ℝ] E) := {A | ‖A‖ ≤ B ∧ δ ≤ |A.det|}
  have hS : IsCompact S := (isCompact_closedBall (0 : E →L[ℝ] E) B).of_isClosed_subset
    (isClosed_le continuous_norm continuous_const |>.inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs))
    (fun A hA ↦ by simpa only [mem_closedBall, dist_zero_right] using hA.1)
  have hc : ContinuousOn (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) S := by
    intro A hA
    exact ((isInvertible_of_det_gap hδ hA.2).contDiffAt_map_inverse (n := ∞)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hc
  exact ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun A hA hdet ↦ (hK A ⟨hA, hdet⟩).trans (le_max_right _ _)⟩

/-- Finite jets of an inverse linear-map field follow from forward jets and
the determinant gap (`app:ch_osc:prop:osc-normal`). This reuses the normed
algebra inversion estimate underlying `Matrix.InverseBounds`. -/
theorem exists_inverse_field_jet_bound_of_det_gap (N : ℕ) (B : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K > 0, ∀ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      (A : P → E →L[ℝ] E) (U : Set P), IsOpen U → ContDiffOn ℝ N A U →
      (∀ z ∈ U, δ ≤ |(A z).det|) →
      (∀ z ∈ U, ∀ k ≤ N, ‖iteratedFDeriv ℝ k A z‖ ≤ B) →
      ∀ z ∈ U, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q ↦ (A q).inverse) z‖ ≤ K := by
  obtain ⟨L, hL, hbound⟩ := exists_norm_inverse_le_of_det_gap (E := E) B hδ
  let D := max 1 B
  let K := (N.factorial : ℝ) * ((N.factorial : ℝ) * max 1 L ^ (N + 1)) * D ^ N
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro P _ _ A U hU hA hdet hj z hz k hk
  have hinv (q) (hq : q ∈ U) : (A q).IsInvertible := isInvertible_of_det_gap hδ (hdet q hq)
  have hunit (q) (hq : q ∈ U) : IsUnit (A q) :=
    isUnit_iff_exists.mpr ⟨(A q).inverse, (hinv q hq).self_comp_inverse,
      (hinv q hq).inverse_comp_self⟩
  have hLz : ‖Ring.inverse (A z)‖ ≤ L := by
    rw [ContinuousLinearMap.ringInverse_eq_inverse]
    exact hbound (A z) (by simpa using hj z hz 0 (Nat.zero_le N)) (hdet z hz)
  have hD (i) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i A U z‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hz]
    exact ((hj z hz i (hik.trans hk)).trans (le_max_right 1 B)).trans
      (le_self_pow₀ (le_max_left 1 B) (by omega))
  have h := norm_iteratedFDerivWithin_ringInverse_comp_le
    (hA.of_le (by exact_mod_cast hk)) hU.uniqueDiffOn hunit hz hLz hD
  rw [iteratedFDerivWithin_of_isOpen k hU hz, ContinuousLinearMap.ringInverse_eq_inverse] at h
  apply h.trans
  apply le_trans _ (le_max_right 1 K)
  have hf : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
  have hp : max 1 L ^ (k + 1) ≤ max 1 L ^ (N + 1) :=
    pow_le_pow_right₀ (le_max_left _ _) (by omega)
  have hd : D ^ k ≤ D ^ N := pow_le_pow_right₀ (le_max_left _ _) hk
  dsimp [K]
  gcongr

end JanetCartan.NormalComparison
