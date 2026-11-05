module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Product differences in the literal carrier density

The two normal factors, two reduced covectors and masks in
`app:ch_background:eq:bg-full-complex-amplitude` are multiplied before
spectator integration. The telescoping product estimate below retains one
small primitive difference and fixed common finite bounds. Its consumers are
the substituted-density estimate and the two-footpoint small-density branch.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open FullPhaseCharts.InverseEstimates
variable {E F G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Fixed Leibniz coefficient for products in the full density of
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def bilinearDifferenceConstant (L : F →L[ℝ] G →L[ℝ] H) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), ‖L‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)

/-- The fixed Leibniz coefficient is nonnegative, including order zero.
Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem bilinearDifferenceConstant_nonneg (L : F →L[ℝ] G →L[ℝ] H) (s : ℕ) :
    0 ≤ bilinearDifferenceConstant L s := by
  unfold bilinearDifferenceConstant
  positivity

/-- The exact two-term telescoping product estimate on a buffered domain.
No product-difference bound is assumed. Consumer: multiplying masks, normal
factors and reduced covectors in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem cNorm_bilinear_sub_le
    (L : F →L[ℝ] G →L[ℝ] H) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (s : ℕ)
    {f f₀ : E → F} {g g₀ : E → G}
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hg : ContDiffOn ℝ ∞ g U) (hg₀ : ContDiffOn ℝ ∞ g₀ U) :
    cNorm K s (fun x ↦ L (f x) (g x) - L (f₀ x) (g₀ x)) ≤
      bilinearDifferenceConstant L s *
        (cNorm K s (f - f₀) * cNorm K s g + cNorm K s f₀ * cNorm K s (g - g₀)) := by
  have he : (fun x ↦ L (f x) (g x) - L (f₀ x) (g₀ x)) =
      (fun x ↦ L ((f - f₀) x) (g x)) + (fun x ↦ L (f₀ x) ((g - g₀) x)) := by
    funext x
    simp [map_sub]
  rw [he]
  have hleft : ContDiffOn ℝ ∞ (fun x ↦ L ((f - f₀) x) (g x)) U :=
    (L.contDiff.comp_contDiffOn (hf.sub hf₀)).clm_apply hg
  have hright : ContDiffOn ℝ ∞ (fun x ↦ L (f₀ x) ((g - g₀) x)) U :=
    (L.contDiff.comp_contDiffOn hf₀).clm_apply (hg.sub hg₀)
  apply (cNorm_add_le_of_contDiffAt hK
    (fun x hx ↦ (hleft.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
    (fun x hx ↦ (hright.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))).trans
  exact (add_le_add (cNorm_bilinear_le_on L hK hU hKU (hf.sub hf₀) hg s)
    (cNorm_bilinear_le_on L hK hU hKU hf₀ (hg.sub hg₀) s)).trans_eq (by
      simp only [bilinearDifferenceConstant, Pi.sub_def]; ring)

/-- Uniform linear dependence on the primitive perturbation size. The order,
bilinear operation and common finite bound precede the varying fields and
perturbation. Consumer: the full substituted-density difference, with all
original factors retained. Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem cNorm_bilinear_sub_le_common_bounds
    (L : F →L[ℝ] G →L[ℝ] H) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (s : ℕ) {M : ℝ} (hM : 0 ≤ M)
    {f f₀ : E → F} {g g₀ : E → G} {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hg : ContDiffOn ℝ ∞ g U) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (hboundf : cNorm K s f₀ ≤ M) (hboundg : cNorm K s g ≤ M)
    (hfdiff : cNorm K s (f - f₀) ≤ ε) (hgdiff : cNorm K s (g - g₀) ≤ ε) :
    cNorm K s (fun x ↦ L (f x) (g x) - L (f₀ x) (g₀ x)) ≤
      (bilinearDifferenceConstant L s * (2 * M)) * ε := by
  apply (cNorm_bilinear_sub_le L hK hU hKU s hf hf₀ hg hg₀).trans
  calc
    _ ≤ bilinearDifferenceConstant L s * (ε * M + M * ε) := by
      apply mul_le_mul_of_nonneg_left _ (bilinearDifferenceConstant_nonneg L s)
      exact add_le_add (mul_le_mul hfdiff hboundg (cNorm_nonneg _ _ _) hε)
        (mul_le_mul hboundf hgdiff (cNorm_nonneg _ _ _) hM)
    _ = _ := by ring
end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
