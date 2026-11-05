module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Nested

/-!
# All shell budgets of the fixed nested right multiplier

The fixed radial dilation is a contraction on the joint position-frequency
variables. Apply the already proved undilated mask budgets on its literal
compact image. The same dilation works at every order; there is no additional
derivative loss (`app:ch_regular_base:lem:retarded-kernel`).
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteMasks
open FourierIntegral.PrimitiveProfiles
open Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E" => Euclidean (d + 1)

/-- All normalized budgets for the actual enlarged collar used to nest the
spatial amplitude cutoff and right multiplier. They follow from the original
smooth angular mask and the compact buffer alone (`retarded-kernel`). -/
theorem boundedNormalizedSeminorm_dilatedConicMask
    {b : E → ℝ} (hb : ContDiff ℝ ∞ b) {L : ℝ} (hL : 1 ≤ L)
    {K : Set (X × E)} (hK : IsCompact K) (hzero : ∀ p ∈ K, p.2 ≠ 0) (m : ℕ) :
    BoundedNormalizedSeminorm K m (fun p : X × E ↦ (dilatedConicMask b L p.2 : ℂ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let T : X × E →L[ℝ] X × E :=
    (ContinuousLinearMap.fst ℝ X E).prod (L⁻¹ • ContinuousLinearMap.snd ℝ X E)
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change max ‖p.1‖ ‖L⁻¹ • p.2‖ ≤ 1 * ‖p‖
    rw [one_mul]
    apply max_le (norm_fst_le p)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hL)).trans (norm_snd_le p)
  have hTi := hK.image T.continuous
  have hTzero : ∀ p ∈ T '' K, p.2 ≠ 0 := by
    rintro p ⟨q, hq, rfl⟩
    exact smul_ne_zero (inv_ne_zero hLp.ne') (hzero q hq)
  have hmask := boundedNormalizedSeminorm_conicMask hb hTi hTzero m
  refine ⟨normalizedSeminorm (T '' K) m (fun p : X × E ↦ (conicMask b p.2 : ℂ)), ?_⟩
  rintro _ ⟨R, rfl⟩
  have hs : ContDiff ℝ ∞ (normalizedField (R : ℝ)
      (fun p : X × E ↦ (conicMask b p.2 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_conicMask hb).comp
      (contDiff_snd.const_smul (R : ℝ)))
  have h := cNorm_preAffine_contraction_le T hT 0 hTi isOpen_univ
    (subset_univ _) hs.contDiffOn
    (show MapsTo (fun p ↦ T p + 0) K (T '' K) from fun p hp ↦ by
      simpa only [add_zero] using mem_image_of_mem T hp) m
  have he : normalizedField (R : ℝ) (fun p : X × E ↦ (dilatedConicMask b L p.2 : ℂ)) =
      (normalizedField (R : ℝ) (fun p : X × E ↦ (conicMask b p.2 : ℂ))) ∘
        (fun p ↦ T p + 0) := by
    funext p
    simp only [normalizedField, dilatedConicMask, Function.comp_apply, add_zero]
    change (conicMask b (L⁻¹ • ((R : ℝ) • p.2)) : ℂ) =
      (conicMask b ((R : ℝ) • (L⁻¹ • p.2)) : ℂ)
    rw [smul_comm (L⁻¹) (R : ℝ)]
  change cNorm K m (normalizedField (R : ℝ)
    (fun p : X × E ↦ (dilatedConicMask b L p.2 : ℂ))) ≤ _
  rw [he]
  exact h.trans (cNorm_normalizedField_le hmask R.2)

end JanetCartan.RegularSector.FiniteMasks
