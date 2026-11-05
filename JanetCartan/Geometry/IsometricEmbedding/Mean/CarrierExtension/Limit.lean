module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Tests

/-!
# Fatou and density for carrier regularizations

The limiting step of `app:ch_background:prop:bg-frame`, Step 1.
This adapts the checked `FourierIntegral.L2Realization.Limit` argument to
the distinct carrier input and torus output measures. No graph calculus is
used, and no identification of initial data with torus data is made.
Consumer: `exists_carrierL2Extension`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.ContinuumRow

variable {n : ℕ}
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "H" => ComplexOutputL2 n

/-- Fatou supplies both membership and the low bound for the test limit in
`app:ch_background:eq:bg-T`; no L² convergence is assumed. -/
theorem carrierLimit_memLp_bound (v : ℕ → H) (g : Torus n → V)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖v k‖ ≤ C)
    (hl : ∀ᵐ x ∂volume, Tendsto (fun k ↦ v k x) atTop (𝓝 (g x))) :
    MemLp g 2 volume ∧ (eLpNorm g 2 volume).toReal ≤ C := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ Lp.aestronglyMeasurable (v k)) hl
  have he : eLpNorm g 2 volume ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun k ↦ Lp.aestronglyMeasurable (v k)) hm hl
    apply Eventually.of_forall
    intro k
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (v k))]
    change ENNReal.ofReal ‖v k‖ ≤ _
    exact ENNReal.ofReal_le_ofReal (hb k)
  exact ⟨he.trans_lt ENNReal.ofReal_lt_top,
    ENNReal.toReal_le_of_le_ofReal hC he⟩

/-- The test limit of uniformly bounded regularizations has a unique bounded
extension with the same constant (`app:ch_background:eq:bg-T`). Linearity
of the limit is proved from the regularizations, rather than imposed on it. -/
theorem exists_carrierLimit_extension
    (T : ℕ → CarrierL2 n →L[ℂ] H) (g : carrierInitialTestSpace n → Torus n → V)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖T k‖ ≤ C)
    (hl : ∀ u, ∀ᵐ x ∂volume,
      Tendsto (fun k ↦ T k (carrierInitialTestToLp u) x) atTop (𝓝 (g u x))) :
    ∃ U : CarrierL2 n →L[ℂ] H, ‖U‖ ≤ C ∧ ‖U.adjoint‖ ≤ C ∧
      (∀ u, U (carrierInitialTestToLp u) =ᵐ[volume] g u) ∧
      ∀ W : CarrierL2 n →L[ℂ] H, (∀ u, W (carrierInitialTestToLp u) =ᵐ[volume] g u) → W = U := by
  have hmem (u) := carrierLimit_memLp_bound (fun k ↦ T k (carrierInitialTestToLp u)) (g u)
    (mul_nonneg hC (norm_nonneg _))
    (fun k ↦ ((T k).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))) (hl u)
  let F : carrierInitialTestSpace n → H := fun u ↦ (hmem u).1.toLp (g u)
  have hF (u) : F u =ᵐ[volume] g u := (hmem u).1.coeFn_toLp
  have hadd (u v) : g (u + v) =ᵐ[volume] g u + g v := by
    have he : ∀ᵐ x ∂volume, ∀ k : ℕ,
        T k (carrierInitialTestToLp (u + v)) x =
          T k (carrierInitialTestToLp u) x + T k (carrierInitialTestToLp v) x := by
      apply ae_all_iff.mpr
      intro k
      simpa only [map_add, Filter.EventuallyEq, Pi.add_apply] using Lp.coeFn_add (T k (carrierInitialTestToLp u))
        (T k (carrierInitialTestToLp v))
    filter_upwards [hl (u + v), hl u, hl v, he] with x h₁ h₂ h₃ hx
    exact tendsto_nhds_unique (h₁.congr hx) (h₂.add h₃)
  have hsmul (c : ℂ) (u) : g (c • u) =ᵐ[volume] c • g u := by
    have he : ∀ᵐ x ∂volume, ∀ k : ℕ,
        T k (carrierInitialTestToLp (c • u)) x = c • T k (carrierInitialTestToLp u) x := by
      apply ae_all_iff.mpr
      intro k
      simpa only [map_smul, Filter.EventuallyEq, Pi.smul_apply] using Lp.coeFn_smul c (T k (carrierInitialTestToLp u))
    filter_upwards [hl (c • u), hl u, he] with x h₁ h₂ hx
    exact tendsto_nhds_unique (h₁.congr hx) (tendsto_const_nhds.smul h₂)
  let L : carrierInitialTestSpace n →ₗ[ℂ] H :=
    { toFun := F
      map_add' := fun u v ↦ Lp.ext <| (hF (u + v)).trans <| (hadd u v).trans <|
        ((hF u).add (hF v)).symm.trans (Lp.coeFn_add (F u) (F v)).symm
      map_smul' := fun c u ↦ Lp.ext <| (hF (c • u)).trans <| (hsmul c u).trans <|
        ((hF u).const_smul c).symm.trans (Lp.coeFn_smul c (F u)).symm }
  have hL (u) : ‖L u‖ ≤ C * ‖carrierInitialTestToLp u‖ := by
    change ‖(hmem u).1.toLp (g u)‖ ≤ _
    rw [Lp.norm_toLp]
    exact (hmem u).2
  let U := L.extendOfNorm carrierInitialTestToLp
  have heq (u) : U (carrierInitialTestToLp u) = F u :=
    LinearMap.extendOfNorm_eq denseRange_carrierInitialTestToLp ⟨C, hL⟩ u
  have hU : ‖U‖ ≤ C := ContinuousLinearMap.opNorm_le_bound _ hC
    (LinearMap.norm_extendOfNorm_apply_le denseRange_carrierInitialTestToLp C hL)
  refine ⟨U, hU, ?_, fun u ↦ (heq u) ▸ hF u, ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using hU
  · intro W hW
    apply DFunLike.coe_injective
    apply denseRange_carrierInitialTestToLp.equalizer W.continuous U.continuous
    funext u
    exact Lp.ext ((hW u).trans ((heq u) ▸ hF u).symm)

end JanetCartan.ContinuumRow
