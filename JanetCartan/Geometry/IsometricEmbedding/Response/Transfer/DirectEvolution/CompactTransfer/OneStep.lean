module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.IntegrationByParts

/-!
# Actual compact carrier derivative transfer

The one-step integral identity in `paper-v2.tex`, `new:eq:carrier-ibp`.
Primitive critical geometry supplies the phase trade; compact support supplies
the analytic hypotheses. Smoothness of the literal transfer coefficient is
supplied by `jc-direct-evolution-coefficient-jets`. No integral identity or
operator estimate is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {E F ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- Smoothness of the actual normalized oscillation, used to justify every
compact integral in `new:eq:carrier-ibp`. -/
theorem contDiffOn_oscillation
    {U : Set E} {D : Set (CarrierVariables n)}
    {f : E → CarrierVariables n → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D)) (ρ : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (oscillation f ρ)) (U ×ˢ D) :=
  (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul hf))).cexp

/-- The actual compact one-step derivative transfer, with the complete
amplitude and datum provisionally grouped as `g`. The direction is the literal
inverse-transpose segment average, not a supplied integration-by-parts identity.
This is `new:eq:carrier-ibp` before the final product-rule expansion. -/
theorem fderiv_integral_oscillation_smul
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {g : E → CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D))
    (hs : ∀ p ∈ U, Function.support (g p) ⊆ K)
    {q : E} (hq : q ∈ U) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : gradient (f q) (w₀ q) = 0)
    (hvalue : (fun p ↦ f p (w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0))
    (h₀ : w₀ q ∈ D)
    (hinv : ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (ρ : ℝ) (e : E)
    (hA : ContDiffOn ℝ ∞ (transferCoefficient f w₀ e q) D) :
    fderiv ℝ (fun p ↦ ∫ w, oscillation f ρ p w • g p w) q e =
      ∫ w, oscillation f ρ q w •
        (fderiv ℝ (fun p ↦ g p w) q e -
          weightedDivergence b (transferCoefficient f w₀ e q) (g q) w) := by
  let Ω := oscillation f ρ
  let A := transferCoefficient f w₀ e q
  have hΩ := contDiffOn_oscillation hf ρ
  have hΩq : ContDiffOn ℝ ∞ (Ω q) D :=
    hΩ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hq, hw⟩)
  have hgq : ContDiffOn ℝ ∞ (g q) D :=
    hg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hq, hw⟩)
  have hdΩ : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ (fun p ↦ Ω p w) q e) D :=
    ((contDiffOn_parameterFDeriv hU hD hΩ).clm_apply contDiffOn_const).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hq, hw⟩)
  have hdg : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ (fun p ↦ g p w) q e) D :=
    ((contDiffOn_parameterFDeriv hU hD hg).clm_apply contDiffOn_const).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hq, hw⟩)
  have hsdg := support_parameterFDeriv_subset hU hs hq e
  have hi₁ : Integrable (fun w ↦ fderiv ℝ (fun p ↦ Ω p w) q e • g q w) :=
    integrable_of_support_subset hD hK hKD (hdΩ.smul hgq)
      ((Function.support_smul_subset_right _ _).trans (hs q hq))
  have hi₂ : Integrable (fun w ↦ Ω q w • fderiv ℝ (fun p ↦ g p w) q e) :=
    integrable_of_support_subset hD hK hKD (hΩq.smul hdg)
      ((Function.support_smul_subset_right _ _).trans hsdg)
  have hi₃ : Integrable (fun w ↦ Ω q w • weightedDivergence b A (g q) w) :=
    integrable_of_support_subset hD hK hKD
      (hΩq.smul (contDiffOn_weightedDivergence b hD hA hgq))
      ((Function.support_smul_subset_right _ _).trans
        (support_weightedDivergence_subset b A hK.isClosed (hs q hq)))
  have hsΩg : ∀ p ∈ U, Function.support (fun w ↦ Ω p w • g p w) ⊆ K :=
    fun p hp ↦ (Function.support_smul_subset_right _ _).trans (hs p hp)
  rw [fderiv_integral_supported (g := fun p w ↦ Ω p w • g p w) hU hD hK hKD (hΩ.smul hg) hsΩg hq e]
  calc
    _ = ∫ w, (fderiv ℝ (fun p ↦ Ω p w) q e • g q w +
        Ω q w • fderiv ℝ (fun p ↦ g p w) q e) := by
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w ∈ K
      · have ho : ContDiffAt ℝ ∞ (fun p ↦ Ω p w) q := (hΩ.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hKD hw⟩)).comp q
          (contDiffAt_id.prodMk contDiffAt_const)
        have hb : ContDiffAt ℝ ∞ (fun p ↦ g p w) q := (hg.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hKD hw⟩)).comp q
          (contDiffAt_id.prodMk contDiffAt_const)
        simpa only [add_apply, ContinuousLinearMap.smulRight_apply,
          smul_apply, Pi.smul_def, add_comm] using
          congrArg (fun L : E →L[ℝ] F ↦ L e)
            (fderiv_fun_smul (ho.differentiableAt (by simp)) (hb.differentiableAt (by simp)))
      · have hz := Function.notMem_support.mp (fun h ↦ hw (hs q hq h))
        have hd := Function.notMem_support.mp (fun h ↦ hw (hsdg h))
        have hd' := Function.notMem_support.mp (fun h ↦ hw
          (support_parameterFDeriv_subset hU hsΩg hq e h))
        simp only [hz, hd, hd', smul_zero, add_zero]
    _ = (∫ w, fderiv ℝ (fun p ↦ Ω p w) q e • g q w) +
        ∫ w, Ω q w • fderiv ℝ (fun p ↦ g p w) q e := integral_add hi₁ hi₂
    _ = (∫ w, fderiv ℝ (Ω q) w (A w) • g q w) +
        ∫ w, Ω q w • fderiv ℝ (fun p ↦ g p w) q e := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w ∈ D
      · rw [fderiv_oscillation_external_eq_integration hU hD hcD hf hq hw₀
          hcritical hvalue h₀ hw (hinv w hw) ρ e]
      · have hz := Function.notMem_support.mp (fun h ↦ hw (hKD (hs q hq h)))
        simp only [hz, smul_zero]
    _ = -(∫ w, Ω q w • weightedDivergence b A (g q) w) +
        ∫ w, Ω q w • fderiv ℝ (fun p ↦ g p w) q e := by
      rw [integral_fderiv_vectorField_smul b hD hK hKD hΩq hgq hA (hs q hq)]
    _ = _ := by
      simp_rw [smul_sub]
      rw [integral_sub hi₂ hi₃]
      abel

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
