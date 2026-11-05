module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.StressBudgets
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Joint jets of the literal reduced source

The original real stress varies in the physical coordinate. Its existing
bilinear contraction, the factor one half and the physical cutoffs preserve
all total mixed derivative orders. This supplies the reduced source for
`app:ch_response:eq:response-graded-reduced` and both response envelopes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.ReducedSource
open Sampling.BackgroundModulation RawPrimary.AmplitudeGrades.Polynomial
open ResponseSourceExtension
variable {n d : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Tensor" => Matrix (Fin n) (Fin n) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin n)

private theorem source_fst_jet_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {w : E × Par} (hw : w.1 ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : E × Par ↦ f q.1) w‖ ≤ ‖iteratedFDeriv ℝ k f w.1‖ := by
  let pr := ContinuousLinearMap.fst ℝ E Par
  have hpr : ‖pr‖ ≤ 1 := pr.opNorm_le_bound zero_le_one (by intro q; simpa [pr] using norm_fst_le q)
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr hU hf hw k).trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr))

/-- Joint source jets retain the literal half stress contraction and both
physical cutoffs. Constants precede the source, coefficient scale and all
histories (`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_cutoff_reducedSource_joint_jet_constants
    {core chart : Set E} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    (AQ Ca : ℕ → ℝ) (hAQ : ∀ j, 0 ≤ AQ j) (hCa : ∀ j, 0 ≤ Ca j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (V : Set Par), IsOpen V →
      ∀ (Q : E → Fin n → MetricTensor n) (a : E × Par → Tensor) (A L : ℝ),
      0 ≤ A → 1 ≤ L → ContDiffOn ℝ ∞ Q chart → ContDiffOn ℝ ∞ a (chart ×ˢ V) →
      (∀ x ∈ tsupport χ.toFun, ∀ j, ‖iteratedFDeriv ℝ j Q x‖ ≤ AQ j * L ^ j) →
      (∀ w ∈ chart ×ˢ V, ∀ j, ‖iteratedFDeriv ℝ j a w‖ ≤ Ca j * A * L ^ j) →
      let b := fun w : E × Par ↦ χ.toFun w.1 •
        (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q w.1) (a w)))
      ContDiffOn ℝ ∞ b (univ ×ˢ V) ∧
        ∀ w ∈ univ ×ˢ V, ∀ j, ‖iteratedFDeriv ℝ j b w‖ ≤ C j * A * L ^ j := by
  let β := χ.toFun * η
  have hβ : ContDiff ℝ ∞ β := χ.smooth.mul hη
  let X := fun j ↦ cNorm (tsupport χ.toFun) j β
  have hX : ∀ j, 0 ≤ X j := fun _ ↦ cNorm_nonneg _ _ _
  let R := (1 / 2 : ℝ) • complexStressContractionLinear n
  let M : ℝ →L[ℝ] Vf →L[ℝ] Vf := ContinuousLinearMap.lsmul ℝ ℝ
  let H := productProfile R AQ Ca
  have hH := productProfile_nonneg R hAQ hCa
  refine ⟨productProfile M X H, productProfile_nonneg M hX hH, ?_⟩
  intro V hV Q a A L hA hL hQ ha hQb hab b
  let q := fun w : E × Par ↦ Q w.1
  have hq : ContDiffOn ℝ ∞ q (chart ×ˢ V) :=
    hQ.comp contDiffOn_fst (fun _ h ↦ h.1)
  have hr : ContDiffOn ℝ ∞ (fun w : E × Par ↦ R (q w) (a w)) (chart ×ˢ V) :=
    R.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (g := fun p : (Fin n → MetricTensor n) × Tensor ↦ R p.1 p.2)
      (f := fun w : E × Par ↦ (q w, a w)) (hq.prodMk ha)
  have he : b = fun w : E × Par ↦ β w.1 • (R (q w) (a w)) := by
    funext w
    change χ.toFun w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q w.1) (a w))) =
      (χ.toFun w.1 * η w.1) • ((1 / 2 : ℝ) • complexStressContraction (Q w.1) (a w))
    rw [smul_smul]
  have hzero (w : E × Par) (hw : w.1 ∉ tsupport χ.toFun) : b =ᶠ[𝓝 w] 0 := by
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
      (continuous_fst.tendsto w)
    filter_upwards [hz] with z hz
    change χ.toFun z.1 = 0 at hz
    simp only [b, hz, zero_smul, Pi.zero_apply]
  constructor
  · intro w hw
    by_cases hx : w.1 ∈ tsupport χ.toFun
    · rw [he]
      exact ((hβ.contDiffAt.comp w contDiffAt_fst).smul
        (hr.contDiffAt ((hchart.prod hV).mem_nhds ⟨χ.support_chart hx,hw.2⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero w hx)).contDiffWithinAt
  · intro w hw j
    by_cases hx : w.1 ∈ tsupport χ.toFun
    · have hwc : w ∈ chart ×ˢ V := ⟨χ.support_chart hx,hw.2⟩
      have hqj k : ‖iteratedFDeriv ℝ k q w‖ ≤ AQ k * L ^ k :=
        (source_fst_jet_le hchart hQ hwc.1 k).trans (hQb w.1 hx k)
      have hβj k : ‖iteratedFDeriv ℝ k (fun z : E × Par ↦ β z.1) w‖ ≤ X k * L ^ k := by
        apply (source_fst_jet_le isOpen_univ hβ.contDiffOn (mem_univ _) k).trans
        exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt χ.compact
          (fun _ _ ↦ hβ.contDiffAt.of_le (by simp)) hx le_rfl).trans
          (le_mul_of_one_le_right (hX k) (one_le_pow₀ hL))
      have hrj k : ‖iteratedFDeriv ℝ k (fun z ↦ R (q z) (a z)) w‖ ≤
          (H k * A) * L ^ k := by
        have h := jet_bilinear_le R (hchart.prod hV) hq ha hwc (b := 0) hL hAQ
          (fun k ↦ mul_nonneg (hCa k) hA) hqj (hab w hwc) k
        simpa only [Nat.sub_zero, H, productProfile, Finset.sum_mul, mul_assoc] using h
      have h := jet_bilinear_le M (hchart.prod hV) (hβ.comp contDiff_fst).contDiffOn hr hwc
        (b := 0) hL hX (fun k ↦ mul_nonneg (hH k) hA) hβj hrj j
      rw [he]
      simpa only [M, ContinuousLinearMap.lsmul_apply, Nat.sub_zero,
        H, productProfile, Finset.sum_mul, mul_assoc, Function.comp_apply] using h
    · rw [((hzero w hx).iteratedFDeriv ℝ j).self_of_nhds]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg (productProfile_nonneg M hX hH j) hA)
        (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ResponseTransfer.ReducedSource
