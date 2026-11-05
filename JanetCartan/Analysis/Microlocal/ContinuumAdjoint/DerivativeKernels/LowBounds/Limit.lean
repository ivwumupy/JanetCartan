module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization

/-!
# Removing compact carrier regularization

The Fatou and bounded-extension argument of `CarrierExtension.Limit`, in the
adjoint direction from scalar Euclidean measurement data to the literal carrier
space. The consumer supplies bounds proved by `RegularizedBound`; the final
primitive theorem discharges that premise. Since the adjoint integrals converge
for every L² datum, the linear map can be constructed on the entire input space.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

/-- Fatou on the literal carrier measure, used to remove regularization in
`app:ch_background:prop:bg-adjoint`. -/
theorem modifiedAdjointLimit_memLp_bound (v : ℕ → CarrierL2 n)
    (g : CarrierVariable n → ℂ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖v k‖ ≤ C)
    (hl : ∀ᵐ u ∂carrierMeasure n, Tendsto (fun k ↦ v k u) atTop (𝓝 (g u))) :
    MemLp g 2 (carrierMeasure n) ∧ (eLpNorm g 2 (carrierMeasure n)).toReal ≤ C := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ Lp.aestronglyMeasurable (v k)) hl
  have he : eLpNorm g 2 (carrierMeasure n) ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun k ↦ Lp.aestronglyMeasurable (v k)) hm hl
    apply Eventually.of_forall
    intro k
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (v k))]
    change ENNReal.ofReal ‖v k‖ ≤ _
    exact ENNReal.ofReal_le_ofReal (hb k)
  exact ⟨he.trans_lt ENNReal.ofReal_lt_top, ENNReal.toReal_le_of_le_ofReal hC he⟩

/-- The limit defines a unique bounded operator on all measurement L² inputs.
This is the distinct-space counterpart of `exists_carrierLimit_extension`,
using the same Fatou and linear-extension machinery
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_modifiedAdjointLimit_operator
    (T : ℕ → Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n)
    (g : Lp (α := Euclidean n) ℂ 2 → CarrierVariable n → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖T k‖ ≤ C)
    (hl : ∀ f, ∀ᵐ u ∂carrierMeasure n,
      Tendsto (fun k ↦ T k f u) atTop (𝓝 (g f u))) :
    ∃ U : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
      ‖U‖ ≤ C ∧ (∀ f, U f =ᵐ[carrierMeasure n] g f) ∧
      ∀ W : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        (∀ f, W f =ᵐ[carrierMeasure n] g f) → W = U := by
  have hmem (f) := modifiedAdjointLimit_memLp_bound (fun k ↦ T k f) (g f)
    (mul_nonneg hC (norm_nonneg _))
    (fun k ↦ ((T k).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))) (hl f)
  let F : Lp (α := Euclidean n) ℂ 2 → CarrierL2 n := fun f ↦ (hmem f).1.toLp (g f)
  have hF (f) : F f =ᵐ[carrierMeasure n] g f := (hmem f).1.coeFn_toLp
  have hadd (f h) : g (f + h) =ᵐ[carrierMeasure n] g f + g h := by
    have he : ∀ᵐ u ∂carrierMeasure n, ∀ k : ℕ,
        T k (f + h) u = T k f u + T k h u := by
      apply ae_all_iff.mpr
      intro k
      simpa only [map_add, Filter.EventuallyEq, Pi.add_apply] using Lp.coeFn_add (T k f) (T k h)
    filter_upwards [hl (f + h), hl f, hl h, he] with u h₁ h₂ h₃ hu
    exact tendsto_nhds_unique (h₁.congr hu) (h₂.add h₃)
  have hsmul (c : ℂ) (f) : g (c • f) =ᵐ[carrierMeasure n] c • g f := by
    have he : ∀ᵐ u ∂carrierMeasure n, ∀ k : ℕ, T k (c • f) u = c • T k f u := by
      apply ae_all_iff.mpr
      intro k
      simpa only [map_smul, Filter.EventuallyEq, Pi.smul_apply] using Lp.coeFn_smul c (T k f)
    filter_upwards [hl (c • f), hl f, he] with u h₁ h₂ hu
    exact tendsto_nhds_unique (h₁.congr hu) (tendsto_const_nhds.smul h₂)
  let L : Lp (α := Euclidean n) ℂ 2 →ₗ[ℂ] CarrierL2 n :=
    { toFun := F
      map_add' := fun f h ↦ Lp.ext <| (hF (f + h)).trans <| (hadd f h).trans <|
        ((hF f).add (hF h)).symm.trans (Lp.coeFn_add (F f) (F h)).symm
      map_smul' := fun c f ↦ Lp.ext <| (hF (c • f)).trans <| (hsmul c f).trans <|
        ((hF f).const_smul c).symm.trans (Lp.coeFn_smul c (F f)).symm }
  have hL (f) : ‖L f‖ ≤ C * ‖f‖ := by
    change ‖(hmem f).1.toLp (g f)‖ ≤ _
    rw [Lp.norm_toLp]
    exact (hmem f).2
  let U := L.mkContinuous C hL
  refine ⟨U, ContinuousLinearMap.opNorm_le_bound _ hC hL, hF, ?_⟩
  intro W hW
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hW f).trans (hF f).symm)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
