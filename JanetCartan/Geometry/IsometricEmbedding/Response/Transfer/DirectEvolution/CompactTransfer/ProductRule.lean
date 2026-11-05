module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.OneStep

/-!
# The four terms of compact carrier transfer

The product-rule expansion of `paper-v2.tex`, `new:eq:carrier-ibp`.
A continuous bilinear map retains matrix multiplication order: the full
amplitude is the first argument and the original datum is the second.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {E M V F ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

private theorem fderiv_bilinear_apply (B : M →L[ℝ] V →L[ℝ] F)
    {α : E → M} {a : E → V} {q : E}
    (hα : DifferentiableAt ℝ α q) (ha : DifferentiableAt ℝ a q) (e : E) :
    fderiv ℝ (fun p ↦ B (α p) (a p)) q e =
      B (fderiv ℝ α q e) (a q) + B (α q) (fderiv ℝ a q e) := by
  simpa [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, add_comm] using
    congrArg (fun L : E →L[ℝ] F ↦ L e) (B.fderiv_of_bilinear hα ha)

/-- The source divergence differentiates both the full amplitude and the
original input, with their order preserved. This yields the last two terms
of `new:eq:carrier-ibp`. -/
theorem weightedDivergence_bilinear
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {A : CarrierVariables n → CarrierVariables n}
    {α : CarrierVariables n → M} {a : CarrierVariables n → V}
    {w : CarrierVariables n} (hA : DifferentiableAt ℝ A w)
    (hα : DifferentiableAt ℝ α w) (ha : DifferentiableAt ℝ a w) :
    weightedDivergence b A (fun z ↦ B (α z) (a z)) w =
      B (weightedDivergence b A α w) (a w) + B (α w) (fderiv ℝ a w (A w)) := by
  have he (i) : (fun z ↦ inner ℝ (b i) (A z) • B (α z) (a z)) =
      (fun z ↦ B (inner ℝ (b i) (A z) • α z) (a z)) := by
    funext z
    simp only [map_smul, smul_apply]
  have hi (i) :
      fderiv ℝ (fun z ↦ inner ℝ (b i) (A z) • B (α z) (a z)) w (b i) =
        B (fderiv ℝ (fun z ↦ inner ℝ (b i) (A z) • α z) w (b i)) (a w) +
          B (inner ℝ (b i) (A w) • α w) (fderiv ℝ a w (b i)) := by
    rw [he i]
    exact fderiv_bilinear_apply B (((differentiableAt_const (b i)).inner ℝ hA).smul hα)
      ha (b i)
  change (∑ i, fderiv ℝ (fun z ↦ inner ℝ (b i) (A z) • B (α z) (a z)) w (b i)) = _
  simp_rw [hi]
  have hsum := congrArg (fun v ↦ B (α w) (fderiv ℝ a w v)) (b.sum_repr' (A w))
  simp only [map_sum, map_smul] at hsum
  rw [← hsum]
  simp only [weightedDivergence, Finset.sum_add_distrib, map_sum, sum_apply,
    map_smul, smul_apply]

variable [FiniteDimensional ℝ E] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- The exact four-term compact integration-by-parts identity
`new:eq:carrier-ibp`, from primitive smooth critical geometry. The bilinear
map may be the literal matrix action. All masks remain inside `α`; no
derivative of the original datum is absorbed into a coefficient hypothesis. -/
theorem fderiv_integral_oscillation_bilinear
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : E → CarrierVariables n → M} {a : E → CarrierVariables n → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ D))
    (hs : ∀ p ∈ U, Function.support (α p) ⊆ K)
    {q : E} (hq : q ∈ U) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : gradient (f q) (w₀ q) = 0)
    (hvalue : (fun p ↦ f p (w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0))
    (h₀ : w₀ q ∈ D)
    (hinv : ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (ρ : ℝ) (e : E)
    (hA : ContDiffOn ℝ ∞ (transferCoefficient f w₀ e q) D) :
    fderiv ℝ (fun p ↦ ∫ w, oscillation f ρ p w • B (α p w) (a p w)) q e =
      ∫ w, oscillation f ρ q w •
        (B (fderiv ℝ (fun p ↦ α p w) q e) (a q w) +
         B (α q w) (fderiv ℝ (fun p ↦ a p w) q e) -
         B (weightedDivergence b (transferCoefficient f w₀ e q) (α q) w) (a q w) -
         B (α q w) (fderiv ℝ (a q) w (transferCoefficient f w₀ e q w))) := by
  let g : E → CarrierVariables n → F := fun p w ↦ B (α p w) (a p w)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D) :=
    (B.contDiff.comp_contDiffOn hα).clm_apply ha
  have hsg : ∀ p ∈ U, Function.support (g p) ⊆ K := by
    intro p hp w hw
    by_contra hn
    have hz := Function.notMem_support.mp (fun h ↦ hn (hs p hp h))
    exact hw (by simp [g, hz])
  rw [fderiv_integral_oscillation_smul b hU hD hcD hK hKD hf hg hsg hq hw₀
    hcritical hvalue h₀ hinv ρ e hA]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ D
  · have hαj : ContDiffAt ℝ ∞ (Function.uncurry α) (q, w) := hα.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hw⟩)
    have haj : ContDiffAt ℝ ∞ (Function.uncurry a) (q, w) := ha.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hw⟩)
    have hαe : DifferentiableAt ℝ (fun p ↦ α p w) q :=
      (hαj.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hae : DifferentiableAt ℝ (fun p ↦ a p w) q :=
      (haj.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hαw : DifferentiableAt ℝ (α q) w :=
      (hαj.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have haw : DifferentiableAt ℝ (a q) w :=
      (haj.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    change _ • (fderiv ℝ (fun p ↦ B (α p w) (a p w)) q e - _) = _
    rw [fderiv_bilinear_apply B hαe hae,
      weightedDivergence_bilinear b B
        ((hA.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)) hαw haw]
    congr 1
    abel
  · have hn : w ∉ K := fun h ↦ hw (hKD h)
    have hz := Function.notMem_support.mp (fun h ↦ hn (hs q hq h))
    have hdα := Function.notMem_support.mp (fun h ↦ hn
      (support_parameterFDeriv_subset hU hs hq e h))
    have hdg := Function.notMem_support.mp (fun h ↦ hn
      (support_parameterFDeriv_subset hU hsg hq e h))
    have hvα := Function.notMem_support.mp (fun h ↦ hn
      (support_weightedDivergence_subset b (transferCoefficient f w₀ e q) hK.isClosed (hs q hq) h))
    have hvg := Function.notMem_support.mp (fun h ↦ hn
      (support_weightedDivergence_subset b (transferCoefficient f w₀ e q) hK.isClosed (hsg q hq) h))
    simp only [hdg, hvg, hz, hdα, hvα, map_zero, zero_apply, sub_zero,
      add_zero, smul_zero]

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
