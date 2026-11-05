module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Jet

/-!
# Identification of the stress coefficient with the geometric frame

The rational second-jet formula in `app:ch_seed:setup:seed-current` agrees
with the already checked geometric construction.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius JanetCartan.StressFrame
open JanetCartan.AmbientResponse

namespace JanetCartan.ProjectedStressFrame

variable {n N : ℕ} {F : Euclidean n → Euclidean N} {x : Euclidean n}

/-- The jet metric is the actual induced metric operator
(`app:ch_seed:setup:seed-current`). -/
theorem jetMetric_stressJet (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    jetMetric (stressJet F x) = metricOperator F x := rfl

/-- Immersion implies invertibility of the jet metric
(`app:ch_seed:setup:seed-current`). -/
theorem isUnit_jetMetric_stressJet (hi : Function.Injective (fderiv ℝ F x)) :
    IsUnit (jetMetric (stressJet F x)) := by
  have hinj := (fderiv ℝ F x).adjoint_comp_self_injective_iff.mpr hi
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The inverse-Gram jet expression is exactly the geometric tangent projection
(`app:ch_seed:setup:seed-current`). -/
theorem jetTangent_stressJet (hi : Function.Injective (fderiv ℝ F x)) :
    jetTangent (stressJet F x) = tangentProjection F x := by
  ext w : 1
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨_, rfl⟩
  · rintro _ ⟨v, rfl⟩
    change inner ℝ (fderiv ℝ F x v)
      (w - fderiv ℝ F x (Ring.inverse (jetMetric (stressJet F x))
        ((fderiv ℝ F x).adjoint w))) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right, map_sub, inner_sub_right]
    apply sub_eq_zero.mpr
    congr 1
    change (fderiv ℝ F x).adjoint w =
      jetMetric (stressJet F x)
        (Ring.inverse (jetMetric (stressJet F x)) ((fderiv ℝ F x).adjoint w))
    exact (congrArg (fun T : Euclidean n →L[ℝ] Euclidean n ↦
      T ((fderiv ℝ F x).adjoint w))
      (Ring.mul_inverse_cancel _ (isUnit_jetMetric_stressJet hi))).symm

/-- The curried second differential gives the coordinate second partials
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem stressJet_second_apply (hF : ContDiffAt ℝ 2 F x) (i j : Fin n) :
    (stressJet F x).2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      partialDeriv (fun y ↦ partialDeriv F y j) x i := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  simp only [stressJet, partialDeriv,
    fderiv_clm_apply hd (differentiableAt_const _),
    add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]

/-- The jet second form is the actual normal projection of the Hessian
(`app:ch_seed:setup:seed-current`). -/
theorem jetSecondForm_stressJet (hF : ContDiffAt ℝ 2 F x)
    (hi : Function.Injective (fderiv ℝ F x)) (i j : Fin n) :
    jetSecondForm (stressJet F x) i j = secondFundamentalForm F x i j := by
  rw [jetSecondForm, jetTangent_stressJet hi, stressJet_second_apply hF]
  exact (secondFundamentalForm_eq_sub_tangentProjection F x i j).symm

/-- The jet contraction is the actual normal map on all matrices; its adjoint
is therefore also the actual Frobenius adjoint (`app:ch_seed:setup:seed-current`). -/
theorem jetNormalMap_stressJet (hF : ContDiffAt ℝ 2 F x)
    (hi : Function.Injective (fderiv ℝ F x)) :
    jetNormalMap (stressJet F x) = (normalMapLinear F x).toContinuousLinearMap := by
  ext H : 1
  change (∑ i, ∑ j, H i j • jetSecondForm (stressJet F x) i j) = normalMap F x H
  simp only [jetSecondForm_stressJet hF hi, normalMap]

/-- The second jet produces exactly the ambient operator used by canonical
normal completion (`app:ch_seed:setup:seed-current`). -/
theorem jetAmbient_stressJet (hF : ContDiffAt ℝ 2 F x)
    (hi : Function.Injective (fderiv ℝ F x)) :
    jetAmbient (stressJet F x) = ambientNormalOperator F x := by
  rw [jetAmbient, jetNormalMap_stressJet hF hi, jetTangent_stressJet hi]
  rfl

/-- The rational second-jet coefficient equals the actual projected cube stress
(`app:ch_seed:setup:seed-current`). No rank or projector identity is assumed. -/
theorem jetStress_stressJet (hF : ContDiffAt ℝ 2 F x)
    (hi : Function.Injective (fderiv ℝ F x)) (i : Fin n) :
    jetStress (cubeStress n i) (stressJet F x) = projectedStress F x i := by
  rw [jetStress, jetNormalMap_stressJet hF hi, jetAmbient_stressJet hF hi]
  rfl

/-- The normal singular-value gap supplies the lower operator bound needed
for a compact admissible jet range (`app:ch_seed:eq:seed-frame-tame`). -/
theorem jetAmbient_lower_bound_of_normal_gap (hF : ContDiffAt ℝ 2 F x)
    (hi : Function.Injective (fderiv ℝ F x)) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ w ∈ normalSpace F x,
      κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) (w : Euclidean N) :
    ‖w‖ ≤ max 1 (κ ^ 2)⁻¹ * ‖jetAmbient (stressJet F x) w‖ := by
  rw [jetAmbient_stressJet hF hi]
  obtain ⟨hu, hbound⟩ := ambientNormalOperator_inverse_bound hκ hgap
  have heq : Ring.inverse (ambientNormalOperator F x) (ambientNormalOperator F x w) = w :=
    congrArg (fun T : Euclidean N →L[ℝ] Euclidean N ↦ T w)
      (Ring.inverse_mul_cancel _ hu)
  calc
    ‖w‖ = ‖Ring.inverse (ambientNormalOperator F x) (ambientNormalOperator F x w)‖ :=
      congrArg norm heq.symm
    _ ≤ ‖Ring.inverse (ambientNormalOperator F x)‖ * ‖ambientNormalOperator F x w‖ :=
      (Ring.inverse (ambientNormalOperator F x)).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

end JanetCartan.ProjectedStressFrame
