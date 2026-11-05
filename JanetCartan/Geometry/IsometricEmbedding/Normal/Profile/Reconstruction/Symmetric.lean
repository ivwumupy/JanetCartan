module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.JetInverse

/-!
# Symmetric Frobenius domain of the ambient normal inverse

The full matrix implementation of `app:ch_waves:eq:ambient-normal-inverse`
agrees with the manuscript's symmetric tensor operator. The two inverse laws
below identify its restriction to the stress orthogonal complement.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.GeometricProfile

/-- `app:ch_waves:defn:geometry`: the second-jet contraction restricted to
the symmetric tensors with their inherited Frobenius inner product. -/
def secondJetSymmetricNormalMap {n N : ℕ}
    (J : SecondJet (Euclidean n) (Euclidean N)) : SymmetricTensor n →L[ℝ] Euclidean N :=
  (secondJetNormalMap J).comp (symmetricTensorSubmodule n).subtypeL

/-- `app:ch_waves:eq:ambient-normal-inverse`: the symmetric adjoint has the
same entries as the full-matrix adjoint, with the Frobenius normalization. -/
theorem secondJetSymmetricNormalMap_adjoint {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x)) (w : Euclidean N) :
    ((secondJetSymmetricNormalMap (secondJet f x)).adjoint w : MetricTensor n) =
      normalPairing f (fun _ ↦ w) x := by
  have hs := normalPairing_isSymm (x := x) (fun _ ↦ w)
    (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
  have he : (secondJetSymmetricNormalMap (secondJet f x)).adjoint w =
      (⟨normalPairing f (fun _ ↦ w) x, hs⟩ : SymmetricTensor n) := by
    apply ext_inner_right ℝ
    intro H
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ w (secondJetNormalMap (secondJet f x) H.val) =
      tensorPairing (normalPairing f (fun _ ↦ w) x) H.val
    rw [secondJetNormalMap_eq hf hi]
    change inner ℝ w (normalMap f x H.val) = _
    rw [inner_normalMap_eq_tensorPairing f (fun _ ↦ w)]
    exact (real_inner_comm (H.val : MetricTensor n) (normalPairing f (fun _ ↦ w) x)).symm
  exact congrArg Subtype.val he

/-- `app:ch_waves:eq:ambient-normal-inverse`: restricting `B` to `Sym²`
does not change the ambient operator `BB* + P_tan`. -/
theorem secondJetAmbientOperator_eq_symmetric_formula {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x)) :
    secondJetAmbientOperator (secondJet f x) =
      (secondJetSymmetricNormalMap (secondJet f x)).comp
        (secondJetSymmetricNormalMap (secondJet f x)).adjoint + tangentProjection f x := by
  ext w : 1
  rw [secondJetAmbientOperator_eq hf hi, AmbientResponse.ambientNormalOperator_apply]
  change _ = secondJetNormalMap (secondJet f x)
    ((secondJetSymmetricNormalMap (secondJet f x)).adjoint w).val + _
  rw [secondJetSymmetricNormalMap_adjoint hf hi, secondJetNormalMap_eq hf hi]
  rfl

/-- `app:ch_waves:eq:ambient-normal-inverse`: the ambient formula takes values
in the actual normal space. -/
theorem secondJetNormalInverse_mem_normalSpace {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N)))
    (H : MetricTensor n) : secondJetNormalInverse (secondJet f x) H ∈ normalSpace f x := by
  change (secondJetNormalInverse (secondJet f x)).toLinearMap H ∈ _
  rw [secondJetNormalInverse_eq_canonicalNormalCompletion hf hi hrank]
  exact AmbientResponse.canonicalNormalCompletion_mem_normalSpace f x H

/-- `app:ch_waves:eq:ambient-normal-inverse`: the inverse of the extended
adjoint recovers the normal part of an arbitrary ambient vector. -/
theorem secondJetNormalInverse_normalPairing {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N)))
    (w : Euclidean N) :
    secondJetNormalInverse (secondJet f x) (normalPairing f (fun _ ↦ w) x) =
      normalProjection f x w := by
  let v : normalSpace f x := ⟨normalProjection f x w, by
    exact Submodule.starProjection_apply_mem _ _⟩
  have hp : normalPairing f (fun _ ↦ w) x =
      (AmbientResponse.normalMapToNormal f x).adjoint v := by
    rw [AmbientResponse.adjoint_normalMapToNormal]
    exact (normalPairing_normalProjection f (fun _ ↦ w) x).symm
  change (secondJetNormalInverse (secondJet f x)).toLinearMap _ = _
  rw [secondJetNormalInverse_eq_canonicalNormalCompletion hf hi hrank,
    AmbientResponse.canonicalNormalCompletion, dite_eq_left hrank, hp]
  exact congrArg Subtype.val (NormalInverse.normalCompletion_adjoint _ _ v)

/-- `app:ch_waves:defn:geometry`: on normals the formula is a left inverse
of the actual symmetric adjoint `B*`. -/
theorem secondJetNormalInverse_symmetric_adjoint {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N)))
    (w : normalSpace f x) :
    secondJetNormalInverse (secondJet f x)
      ((secondJetSymmetricNormalMap (secondJet f x)).adjoint w).val = w := by
  rw [secondJetSymmetricNormalMap_adjoint hf hi,
    secondJetNormalInverse_normalPairing hf hi hrank]
  exact normalProjection_eq_self_of_mem_normalSpace w.property

/-- `app:ch_waves:defn:geometry`: on the symmetric stress orthogonal
complement the formula is also a right inverse of `B*`. -/
theorem symmetric_adjoint_secondJetNormalInverse {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N)))
    (H : SymmetricTensor n)
    (hH : H ∈ (secondJetSymmetricNormalMap (secondJet f x)).kerᗮ) :
    (secondJetSymmetricNormalMap (secondJet f x)).adjoint
      (secondJetNormalInverse (secondJet f x) H.val) = H := by
  have hr : H ∈ LinearMap.range
      (secondJetSymmetricNormalMap (secondJet f x)).toLinearMap.adjoint := by
    rw [← LinearMap.orthogonal_ker]
    exact hH
  obtain ⟨w, rfl⟩ := hr
  apply Subtype.ext
  rw [secondJetSymmetricNormalMap_adjoint hf hi]
  change normalPairing f (fun _ ↦ secondJetNormalInverse (secondJet f x)
    ((secondJetSymmetricNormalMap (secondJet f x)).adjoint w).val) x = _
  rw [secondJetSymmetricNormalMap_adjoint hf hi,
    secondJetNormalInverse_normalPairing hf hi hrank]
  change normalPairing f (fun _ ↦ normalProjection f x w) x =
    ((secondJetSymmetricNormalMap (secondJet f x)).adjoint w).val
  rw [secondJetSymmetricNormalMap_adjoint hf hi]
  exact normalPairing_normalProjection f (fun _ ↦ w) x

/-- `app:ch_waves:defn:geometry`: the full-matrix rank hypothesis is
surjectivity onto the actual normal space already on symmetric tensors. -/
theorem secondJetSymmetricNormalMap_range {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N))) :
    Set.range (secondJetSymmetricNormalMap (secondJet f x)) =
      (normalSpace f x : Set (Euclidean N)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨H, rfl⟩
    change secondJetNormalMap (secondJet f x) H.val ∈ _
    rw [secondJetNormalMap_eq hf hi]
    exact normalMap_mem_normalSpace f x H.val
  · intro w hw
    obtain ⟨H, hH⟩ := (show w ∈ Set.range (normalMap f x) by rw [hrank]; exact hw)
    let v := AmbientResponse.canonicalNormalCompletion f x H
    refine ⟨⟨normalPairing f (fun _ ↦ v) x,
      normalPairing_isSymm _ (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt⟩, ?_⟩
    change secondJetNormalMap (secondJet f x) _ = w
    rw [secondJetNormalMap_eq hf hi]
    exact (AmbientResponse.canonicalNormalCompletion_normal_equation hrank H).trans hH

/-- `app:ch_waves:eq:ambient-normal-inverse`: `I - B* Nmathsf` on symmetric
Frobenius tensors is precisely orthogonal projection onto the stress kernel. -/
theorem symmetric_stressProjection_formula {n N : ℕ}
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x))
    (hrank : Set.range (normalMap f x) = (normalSpace f x : Set (Euclidean N)))
    (H : SymmetricTensor n) :
    H - (secondJetSymmetricNormalMap (secondJet f x)).adjoint
      (secondJetNormalInverse (secondJet f x) H.val) =
      (secondJetSymmetricNormalMap (secondJet f x)).ker.starProjection H := by
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · change secondJetSymmetricNormalMap (secondJet f x) (_ - _) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    change secondJetNormalMap (secondJet f x) H.val =
      secondJetNormalMap (secondJet f x)
        ((secondJetSymmetricNormalMap (secondJet f x)).adjoint _).val
    rw [secondJetSymmetricNormalMap_adjoint hf hi, secondJetNormalMap_eq hf hi]
    change normalMap f x H.val = normalMap f x (normalPairing f
      (fun _ ↦ (secondJetNormalInverse (secondJet f x)).toLinearMap H.val) x)
    rw [secondJetNormalInverse_eq_canonicalNormalCompletion hf hi hrank]
    exact (AmbientResponse.canonicalNormalCompletion_normal_equation hrank H.val).symm
  · rw [sub_sub_cancel]
    change (secondJetSymmetricNormalMap (secondJet f x)).toLinearMap.adjoint _ ∈
      (secondJetSymmetricNormalMap (secondJet f x)).toLinearMap.kerᗮ
    rw [LinearMap.orthogonal_ker]
    exact ⟨_, rfl⟩

end JanetCartan.GeometricProfile
