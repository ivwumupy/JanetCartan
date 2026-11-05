module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.JointJets

/-!
# Literal half-stress contraction with the original derivative reserve

The already constructed full-strain envelope supplies the source tensor.
Multiply by the SAME spatial masks and parameter cutoff, and contract with
the SAME physical projected stress. Natural subtraction is retained by the
existing bilinear jet calculus. Consumer: the initial Fourier source of the
complete inverse in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary
open Sampling.BackgroundModulation RawPrimary.AmplitudeGrades.Polynomial
variable {n d : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Tensor" => Matrix (Fin n) (Fin n) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin n)

private theorem reserved_source_fst_jet_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {w : E × Par} (hw : w.1 ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : E × Par ↦ f q.1) w‖ ≤ ‖iteratedFDeriv ℝ k f w.1‖ := by
  let pr := ContinuousLinearMap.fst ℝ E Par
  have hpr : ‖pr‖ ≤ 1 := pr.opNorm_le_bound zero_le_one (by intro q; simpa [pr] using norm_fst_le q)
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr hU hf hw k).trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr))

/-- The literal fixed cutoffs and half stress contraction preserve every
available source reserve, including its low-order plateau. Neither source
norms nor reduced-source estimates are assumed; the supplied tensor jets are
those of `exists_history_fullStrain_reserved_profiles`
(`app:ch_response:eq:response-graded-source`). -/
theorem exists_reducedSource_reserved_joint_constants
    {S chart : Set E} (hS : IsCompact S) (hchart : IsOpen chart) (hSchart : S ⊆ chart)
    {V : Set Par} (hV : IsOpen V)
    (χsrc η : E → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc) (hη : ContDiff ℝ ∞ η)
    (θ : Par → ℝ) (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ V)
    (AQ Ca : ℕ → ℝ) (hAQ : ∀ j, 0 ≤ AQ j) (hCa : ∀ j, 0 ≤ Ca j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (Q : E → Fin n → MetricTensor n) (a : E × Par → Tensor) (A K : ℝ) (reserve : ℕ),
      0 ≤ A → 1 ≤ K → ContDiffOn ℝ ∞ Q chart → ContDiffOn ℝ ∞ a (univ ×ˢ V) →
      (∀ w, w.1 ∉ S → a w = 0) →
      (∀ x ∈ S, ∀ j, ‖iteratedFDeriv ℝ j Q x‖ ≤ AQ j * K^(j-reserve)) →
      (∀ w, w.2 ∈ V → ∀ j, ‖iteratedFDeriv ℝ j a w‖ ≤ Ca j * A * K^(j-reserve)) →
      let b := fun w : E × Par ↦ θ w.2 • (χsrc w.1 •
        (η w.1 • ((1/2 : ℝ) • complexStressContraction (Q w.1) (a w))))
      ContDiff ℝ ∞ b ∧ (∀ w, w.1 ∉ S → b w = 0) ∧
        ∀ w j, ‖iteratedFDeriv ℝ j b w‖ ≤ C j * A * K^(j-reserve) := by
  let β := fun w : E × Par ↦ θ w.2 * χsrc w.1 * η w.1
  have hβ : ContDiff ℝ ∞ β := ((hθ.comp contDiff_snd).mul
    (hχsrc.comp contDiff_fst)).mul (hη.comp contDiff_fst)
  let X := fun j ↦ cNorm (S ×ˢ tsupport θ) j β
  have hX j : 0 ≤ X j := cNorm_nonneg _ _ _
  let R := (1/2 : ℝ) • complexStressContractionLinear n
  let M : ℝ →L[ℝ] Vf →L[ℝ] Vf := ContinuousLinearMap.lsmul ℝ ℝ
  let H := productProfile R AQ Ca
  have hH := productProfile_nonneg R hAQ hCa
  let C := productProfile M X H
  have hC := productProfile_nonneg M hX hH
  refine ⟨C,hC,?_⟩
  intro Q a A K reserve hA hK hQ ha haz hQb hab b
  let q := fun w : E × Par ↦ Q w.1
  have hq : ContDiffOn ℝ ∞ q (chart ×ˢ V) := hQ.comp contDiffOn_fst (fun _ h ↦ h.1)
  have haa : ContDiffOn ℝ ∞ a (chart ×ˢ V) := ha.mono (prod_mono (subset_univ _) Subset.rfl)
  have hr : ContDiffOn ℝ ∞ (fun w : E × Par ↦ R (q w) (a w)) (chart ×ˢ V) :=
    R.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (g := fun p : (Fin n → MetricTensor n) × Tensor ↦ R p.1 p.2)
      (f := fun w : E × Par ↦ (q w,a w)) (hq.prodMk haa)
  have he : b = fun w : E × Par ↦ β w • R (q w) (a w) := by
    funext w
    change θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) •
      complexStressContraction (Q w.1) (a w)))) =
      (θ w.2 * χsrc w.1 * η w.1) • ((1/2 : ℝ) • complexStressContraction (Q w.1) (a w))
    simp only [smul_smul,mul_assoc]
  have hzeroX w (hw : w.1 ∉ S) : b =ᶠ[𝓝 w] 0 := by
    have hnb : ∀ᶠ z : E × Par in 𝓝 w, z.1 ∉ S :=
      (hS.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hw
    filter_upwards [hnb] with z hz
    simp only [b,haz z hz,map_zero,smul_zero,Pi.zero_apply]
  have hzeroθ w (hw : w.2 ∉ tsupport θ) : b =ᶠ[𝓝 w] 0 := by
    have hn := (notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto (continuous_snd.tendsto w)
    filter_upwards [hn] with z hz
    change θ z.2 = 0 at hz
    simp only [b,hz,zero_smul,Pi.zero_apply]
  have hregular : ContDiff ℝ ∞ b := contDiff_iff_contDiffAt.mpr fun w ↦ by
    by_cases hx : w.1 ∈ S
    · by_cases hp : w.2 ∈ tsupport θ
      · rw [he]
        exact hβ.contDiffAt.smul
          (hr.contDiffAt ((hchart.prod hV).mem_nhds ⟨hSchart hx,hsθ hp⟩))
      · exact contDiffAt_const.congr_of_eventuallyEq (hzeroθ w hp)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzeroX w hx)
  refine ⟨hregular,fun w hw ↦ (hzeroX w hw).eq_of_nhds,?_⟩
  intro w j
  by_cases hx : w.1 ∈ S
  · by_cases hp : w.2 ∈ tsupport θ
    · have hwc : w ∈ chart ×ˢ V := ⟨hSchart hx,hsθ hp⟩
      have hqj k : ‖iteratedFDeriv ℝ k q w‖ ≤ AQ k*K^(k-reserve) :=
        (reserved_source_fst_jet_le hchart hQ hwc.1 k).trans (hQb w.1 hx k)
      have hβj k : ‖iteratedFDeriv ℝ k β w‖ ≤ X k*K^(k-reserve) :=
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (hS.prod hcθ)
          (fun _ _ ↦ hβ.contDiffAt.of_le (by simp)) ⟨hx,hp⟩ le_rfl).trans
          (le_mul_of_one_le_right (hX k) (one_le_pow₀ hK))
      have hrj k : ‖iteratedFDeriv ℝ k (fun z ↦ R (q z) (a z)) w‖ ≤
          (H k*A)*K^(k-reserve) := by
        have hb := jet_bilinear_le R (hchart.prod hV) hq haa hwc (b := reserve) hK hAQ
          (fun k ↦ mul_nonneg (hCa k) hA) hqj (hab w hwc.2) k
        simpa only [H,productProfile,Finset.sum_mul,mul_assoc] using hb
      have hb := jet_bilinear_le M (hchart.prod hV) hβ.contDiffOn hr hwc
        (b := reserve) hK hX (fun k ↦ mul_nonneg (hH k) hA) hβj hrj j
      rw [he]
      simpa only [C,M,ContinuousLinearMap.lsmul_apply,H,productProfile,Finset.sum_mul,mul_assoc] using hb
    · rw [((hzeroθ w hp).iteratedFDeriv ℝ j).self_of_nhds]
      simpa only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using
        mul_nonneg (mul_nonneg (hC j) hA) (pow_nonneg (zero_le_one.trans hK) (j-reserve))
  · rw [((hzeroX w hx).iteratedFDeriv ℝ j).self_of_nhds]
    simpa only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using
      mul_nonneg (mul_nonneg (hC j) hA) (pow_nonneg (zero_le_one.trans hK) (j-reserve))

end JanetCartan.PhysicalPrimary
