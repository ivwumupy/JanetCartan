module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Reparametrization
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Tame operations on fixed linear images of balls

These are the composition and nullvector-product operations on the retained
physical cylinder in `app:ch_waves:eq:joint-tame`. All coordinate costs are
fixed before the varying functions; there is no change of norm convention.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame
open FullPhaseCharts.InverseEstimates

variable {E E' F F' G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The reverse coordinate estimate on a fixed compact image
(`app:ch_waves:eq:joint-tame`). -/
theorem cNorm_image_le_pullback [FiniteDimensional ℝ E]
    (e : E ≃L[ℝ] E') (a : E) (ρ : ℝ) {U : Set E'} (hU : IsOpen U)
    (hKU : e '' closedBall a ρ ⊆ U) {f : E' → G} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    cNorm (e '' closedBall a ρ) m f ≤ linearNormCost e.symm.toContinuousLinearMap m *
      cNorm (closedBall a ρ) m (f ∘ e) := by
  have hcomp := cNorm_comp_linear_le e.symm.toContinuousLinearMap
    (isCompact_closedBall a ρ) (hU.preimage e.continuous)
    (fun x hx ↦ hKU (mem_image_of_mem e hx))
    (hf.comp e.contDiff.contDiffOn (fun _ hx ↦ hx))
    (S := e '' closedBall a ρ)
    (by rintro _ ⟨x, hx, rfl⟩; simpa using hx) m
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hcomp

/-- Composition on two fixed coordinate images of balls. This applies to the
potential along the flow and to the footpoint pullback. The compact domains
and the reserve two are independent of order (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_comp_le_ballImage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] E') (d : F ≃L[ℝ] F')
    (a : E) (b : F) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E') (V : Set F'), IsOpen U → IsOpen V →
      e '' closedBall a ρ ⊆ U → d '' closedBall b σ ⊆ V →
      ∀ (f : E' → F') (g : F' → G), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g V →
      MapsTo f (e '' closedBall a ρ) (d '' closedBall b σ) →
      cNorm (e '' closedBall a ρ) 1 f ≤ M → cNorm (d '' closedBall b σ) 1 g ≤ N →
      cNorm (e '' closedBall a ρ) m (g ∘ f) ≤
        C * (1 + cNorm (e '' closedBall a ρ) (m + 2) f +
          cNorm (d '' closedBall b σ) (m + 2) g) := by
  let A := fun j ↦ ‖d.symm.toContinuousLinearMap‖ * linearNormCost e.toContinuousLinearMap j
  let B := fun j ↦ linearNormCost d.toContinuousLinearMap j
  have hA j : 0 ≤ A j := mul_nonneg (norm_nonneg _) (linearNormCost_pos _ _).le
  have hB j : 0 < B j := linearNormCost_pos _ _
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_uniform_local (G := G)
    a b hρ hσ m (mul_nonneg (hA 1) hM) (mul_nonneg (hB 1).le hN)
  let J := linearNormCost e.symm.toContinuousLinearMap m
  have hJ : 0 < J := linearNormCost_pos _ _
  refine ⟨J * C * (1 + A (m + 2) + B (m + 2)),
    mul_pos (mul_pos hJ hC) (by linarith [hA (m + 2), hB (m + 2)]), ?_⟩
  intro U V hU hV hKU hKV f g hf hg hm hfl hgl
  let f' := fun x ↦ d.symm (f (e x))
  let g' := g ∘ d
  have hf' : ContDiffOn ℝ ∞ f' (e ⁻¹' U) :=
    d.symm.contDiff.comp_contDiffOn (hf.comp e.contDiff.contDiffOn (fun _ hx ↦ hx))
  have hg' : ContDiffOn ℝ ∞ g' (d ⁻¹' V) :=
    hg.comp d.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hballU : closedBall a ρ ⊆ e ⁻¹' U := fun x hx ↦ hKU (mem_image_of_mem e hx)
  have hballV : closedBall b σ ⊆ d ⁻¹' V := fun x hx ↦ hKV (mem_image_of_mem d hx)
  have hfn (j) : cNorm (closedBall a ρ) j f' ≤ A j * cNorm (e '' closedBall a ρ) j f := by
    have hh := cNorm_postLinear_le_on (isCompact_closedBall a ρ) j d.symm.toContinuousLinearMap
      (fun x hx ↦ ((hf.contDiffAt (hU.mem_nhds (hballU hx))).comp x
        e.contDiff.contDiffAt).of_le (by simp))
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (cNorm_comp_linear_le e.toContinuousLinearMap ((isCompact_closedBall a ρ).image e.continuous)
        hU hKU hf (fun x hx ↦ mem_image_of_mem e hx) j) (norm_nonneg _)).trans_eq
          (by dsimp [A]; ring))
  have hgn (j) : cNorm (closedBall b σ) j g' ≤ B j * cNorm (d '' closedBall b σ) j g :=
    cNorm_comp_linear_le d.toContinuousLinearMap ((isCompact_closedBall b σ).image d.continuous)
      hV hKV hg (fun x hx ↦ mem_image_of_mem d hx) j
  have hm' : MapsTo f' (closedBall a ρ) (closedBall b σ) := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hm (mem_image_of_mem e hx)
    change d.symm (f (e x)) ∈ _
    rw [← he, d.symm_apply_apply]
    exact hy
  have hh := hb _ _ (hU.preimage e.continuous) (hV.preimage d.continuous)
    hballU hballV f' g' hf' hg' hm'
    ((hfn 1).trans (mul_le_mul_of_nonneg_left hfl (hA 1)))
    ((hgn 1).trans (mul_le_mul_of_nonneg_left hgl (hB 1).le))
  have hreg : ContDiffOn ℝ ∞ (g ∘ f) (U ∩ f ⁻¹' V) :=
    hg.comp (hf.mono inter_subset_left) (fun _ hx ↦ hx.2)
  have hopen : IsOpen (U ∩ f ⁻¹' V) := hf.continuousOn.isOpen_inter_preimage hU hV
  have hin : e '' closedBall a ρ ⊆ U ∩ f ⁻¹' V := fun x hx ↦ ⟨hKU hx, hKV (hm hx)⟩
  have hr := cNorm_image_le_pullback e a ρ hopen hin hreg m
  have heq : (g ∘ f) ∘ e = g' ∘ f' := by
    funext x
    simp [g', f']
  rw [heq] at hr
  apply (hr.trans (mul_le_mul_of_nonneg_left hh hJ.le)).trans
  have hfi := hfn (m + 2)
  have hgi := hgn (m + 2)
  have hnonf := cNorm_nonneg (e '' closedBall a ρ) (m + 2) f
  have hnong := cNorm_nonneg (d '' closedBall b σ) (m + 2) g
  have hi : 1 + cNorm (closedBall a ρ) (m + 2) f' + cNorm (closedBall b σ) (m + 2) g' ≤
      (1 + A (m + 2) + B (m + 2)) *
        (1 + cNorm (e '' closedBall a ρ) (m + 2) f + cNorm (d '' closedBall b σ) (m + 2) g) := by
    nlinarith [hA (m + 2), hB (m + 2),
      mul_nonneg (hA (m + 2)) hnong, mul_nonneg (hB (m + 2)).le hnonf]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (mul_nonneg hJ.le hC.le)

/-- Scalar multiplication on the physical coordinate image, with one high
norm and fixed low budgets (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_smul_le_ballImage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] E') (a : E) {ρ : ℝ} (hρ : 0 < ρ)
    (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E'), IsOpen U → e '' closedBall a ρ ⊆ U →
      ∀ (f : E' → ℝ) (g : E' → F), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      cNorm (e '' closedBall a ρ) 1 f ≤ M → cNorm (e '' closedBall a ρ) 1 g ≤ N →
      cNorm (e '' closedBall a ρ) m (fun x ↦ f x • g x) ≤
        C * (1 + cNorm (e '' closedBall a ρ) (m + 2) f +
          cNorm (e '' closedBall a ρ) (m + 2) g) := by
  let A := fun j ↦ linearNormCost e.toContinuousLinearMap j
  let J := linearNormCost e.symm.toContinuousLinearMap m
  have hA j : 0 < A j := linearNormCost_pos _ _
  have hJ : 0 < J := linearNormCost_pos _ _
  obtain ⟨C, hC, hb⟩ := exists_cNorm_smul_le_uniform_local (F := F) a hρ m
    (mul_nonneg (hA 1).le hM) (mul_nonneg (hA 1).le hN)
  refine ⟨J * C * (1 + A (m + 2)),
    mul_pos (mul_pos hJ hC) (by linarith [hA (m + 2)]), ?_⟩
  intro U hU hKU f g hf hg hfl hgl
  have hball : closedBall a ρ ⊆ e ⁻¹' U := fun x hx ↦ hKU (mem_image_of_mem e hx)
  have hf' := hf.comp e.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hg' := hg.comp e.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hfn (j) := cNorm_comp_linear_le e.toContinuousLinearMap
    ((isCompact_closedBall a ρ).image e.continuous) hU hKU hf
    (fun x hx ↦ mem_image_of_mem e hx) j
  have hgn (j) := cNorm_comp_linear_le e.toContinuousLinearMap
    ((isCompact_closedBall a ρ).image e.continuous) hU hKU hg
    (fun x hx ↦ mem_image_of_mem e hx) j
  have hh := hb _ (hU.preimage e.continuous) hball (f ∘ e) (g ∘ e) hf' hg'
    ((hfn 1).trans (mul_le_mul_of_nonneg_left hfl (hA 1).le))
    ((hgn 1).trans (mul_le_mul_of_nonneg_left hgl (hA 1).le))
  apply ((cNorm_image_le_pullback e a ρ hU hKU (hf.smul hg) m).trans
    (mul_le_mul_of_nonneg_left hh hJ.le)).trans
  have hi : 1 + cNorm (closedBall a ρ) (m + 2) (f ∘ e) +
      cNorm (closedBall a ρ) (m + 2) (g ∘ e) ≤
      (1 + A (m + 2)) * (1 + cNorm (e '' closedBall a ρ) (m + 2) f +
        cNorm (e '' closedBall a ρ) (m + 2) g) := by
    have hfi := hfn (m + 2)
    have hgi := hgn (m + 2)
    change cNorm (closedBall a ρ) (m + 2) (f ∘ e) ≤ A (m + 2) * _ at hfi
    change cNorm (closedBall a ρ) (m + 2) (g ∘ e) ≤ A (m + 2) * _ at hgi
    nlinarith [cNorm_nonneg (e '' closedBall a ρ) (m + 2) f,
      cNorm_nonneg (e '' closedBall a ρ) (m + 2) g, hA (m + 2)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (mul_nonneg hJ.le hC.le)

end JanetCartan.NullTransport.AmplitudeTame
