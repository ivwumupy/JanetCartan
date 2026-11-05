module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades

/-!
# Primitive joint output-mask profiles

The fixed buffered masks of `Localizers.Grades` supply the full joint
base/frequency profile needed after output rescaling, including mixed jets
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rescaling the output increment contracts every joint derivative norm.
The right side is a primitive symbol jet, not a differentiated product
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_rescaled_outputSymbol_le
    {f : CanonicalPhase E → ℂ} (hf : ContDiff ℝ ∞ f)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (xo : ℝ × E) (n : ℕ) (p : CanonicalPhase E) :
    ‖iteratedFDeriv ℝ n (fun q : CanonicalPhase E => f (xo + ρ⁻¹ • q.1, q.2)) p‖ ≤
      ‖iteratedFDeriv ℝ n f (xo + ρ⁻¹ • p.1, p.2)‖ := by
  let a : CanonicalPhase E →L[ℝ] CanonicalPhase E :=
    (ρ⁻¹ • ContinuousLinearMap.fst ℝ (ℝ × E) (ℝ × E)).prod
      (ContinuousLinearMap.snd ℝ (ℝ × E) (ℝ × E))
  have ha : ‖a‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖(ρ⁻¹ • q.1, q.2)‖ ≤ 1 * ‖q‖
    rw [one_mul, Prod.norm_def, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hρ))]
    exact max_le ((mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hρ)).trans
      (norm_fst_le q)) (norm_snd_le q)
  let g : CanonicalPhase E → ℂ := fun q => f ((xo, 0) + q)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have he : (fun q : CanonicalPhase E => f (xo + ρ⁻¹ • q.1, q.2)) = g ∘ a := by
    funext q
    simp [g, a]
  rw [he]
  rw [a.iteratedFDeriv_comp_right hg p (by simp)]
  apply ((iteratedFDeriv ℝ n g (a p)).norm_compContinuousLinearMap_le (fun _ => a)).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (a p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ha))
    _ = _ := by dsimp [g]; rw [iteratedFDeriv_comp_add_left]; simp [a]

/-- The actual physical mask has all the primitive joint rescaled grades,
uniformly in the external output base and frequency. Physical covector
normalization cancels `ρ`, while the output increment contributes a contraction
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_physicalMask_output_profile_le
    {m : CanonicalPhase E → ℝ} (hm : ContDiff ℝ ∞ m)
    {C : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n)
    (hb : ∀ n p, ‖iteratedFDeriv ℝ n m p‖ ≤ C n)
    {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (xo : ℝ × E)
    (n : ℕ) (p : CanonicalPhase E) :
    ‖iteratedFDeriv ℝ n (fun q : CanonicalPhase E =>
      (physicalMask ρ m (xo + ρ⁻¹ • q.1, ρ • q.2) : ℂ)) p‖ ≤ C n * L ^ n := by
  have hρ0 : ρ ≠ 0 := (zero_lt_one.trans_le hρ).ne'
  have he : (fun q : CanonicalPhase E =>
      (physicalMask ρ m (xo + ρ⁻¹ • q.1, ρ • q.2) : ℂ)) =
      fun q => (m (xo + ρ⁻¹ • q.1, q.2) : ℂ) := by
    funext q
    simp [physicalMask, hρ0]
  rw [he]
  apply (norm_iteratedFDeriv_rescaled_outputSymbol_le
    (Complex.ofRealCLM.contDiff.comp hm) hρ xo n p).trans
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ m) _‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hm.contDiffAt (by simp)]
  exact mask_derivative_grade (hC n) (hb n) hL _

/-- Fixed finite buffered families provide the joint primitive output profile
for both signs, with constants chosen before frequency, grade, external base
and derivative order. This discharges the mask input to the output amplitude
grade theorem (`app:ch_regular:lem:finite-chain`). -/
theorem exists_bufferedMask_output_profiles {ι : Type*} [Fintype ι]
    {m : ι → CanonicalPhase E → ℝ} {K O : ι → Set (CanonicalPhase E)}
    (hm : ∀ i, IsBufferedMask (m i) (K i) (O i)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ i (negative : Bool) (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
        ∀ (xo : ℝ × E) n p,
        ‖iteratedFDeriv ℝ n (fun q : CanonicalPhase E =>
          (physicalMask ρ (if negative then signedMask (m i) else m i)
            (xo + ρ⁻¹ • q.1, ρ • q.2) : ℂ)) p‖ ≤ C n * L ^ n := by
  obtain ⟨C, hC, hb⟩ := exists_bufferedMask_family_bounds hm
  refine ⟨C, hC, ?_⟩
  intro i negative ρ L hρ hL xo n p
  have hs : ContDiff ℝ ∞ (if negative then signedMask (m i) else m i) := by
    cases negative
    · exact (hm i).smooth
    · exact (hm i).signed.smooth
  exact norm_iteratedFDeriv_physicalMask_output_profile_le hs hC
    (hb i negative) hρ hL xo n p

end JanetCartan.FiniteChain.Retarded.KernelDecay
