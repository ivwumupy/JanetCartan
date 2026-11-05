module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction

/-!
# A common low-order neighborhood for all geometric coefficients

The stress neighborhood of `app:ch_background:defn:bg-geometry` also supplies
full normal rank for `app:ch_waves:eq:ambient-normal-inverse`. Restricted
orthogonal projection identifies the varying normal space with the reference
space. No normal-rank or inverse-coefficient estimate is added as a premise.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.StressFrame

namespace JanetCartan.GeometricProfile

open NormalRankStability StressFrame

/-- `app:ch_waves:eq:ambient-normal-inverse`: the first-jet formula is the
orthogonal projection onto the actual orthogonal complement of its range. -/
theorem firstJetNormalProjection_eq_starProjection {n N : ℕ}
    {L : Euclidean n →L[ℝ] Euclidean N} (hL : Function.Injective L) :
    firstJetNormalProjection L = (LinearMap.range L.toLinearMap)ᗮ.starProjection := by
  have h := firstJetNormalProjection_eq (f := fun y ↦ L y) (x := 0)
    (by simpa using hL)
  simpa [normalProjection, normalSpace] using h

/-- `app:ch_background:defn:bg-geometry`: the second-jet contraction always
lands in the moving normal space, without any symmetry assumption on the jet. -/
theorem secondJetNormalMap_mem_orthogonal {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hi : Function.Injective J.1)
    (H : MetricTensor n) :
    secondJetNormalMap J H ∈ (LinearMap.range J.1.toLinearMap)ᗮ := by
  change (∑ i, ∑ j, H i j • secondJetSecondForm J i j) ∈ _
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [secondJetSecondForm, firstJetNormalProjection_eq_starProjection hi]
  exact Submodule.starProjection_apply_mem _ _

/-- `app:ch_background:defn:bg-geometry` and `app:ch_waves:eq:ambient-normal-inverse`:
surjectivity after fixed-space comparison implies full rank onto the moving
normal space. The proof uses injectivity of the nearby projection restriction. -/
theorem secondJetNormalMap_range_of_comparison {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hi : Function.Injective J.1)
    (hp : ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) :
    Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨H, rfl⟩
    exact secondJetNormalMap_mem_orthogonal hi H
  · intro w hw
    obtain ⟨H, hH⟩ := hB ((normalSpace F x).orthogonalProjectionOnto w)
    have hinj := projectionBetween_injective (LinearMap.range J.1.toLinearMap)ᗮ
      (normalSpace F x) (by rwa [← firstJetNormalProjection_eq_starProjection hi])
    have he : (⟨secondJetNormalMap J H.val, secondJetNormalMap_mem_orthogonal hi H.val⟩ :
        (LinearMap.range J.1.toLinearMap)ᗮ) = ⟨w, hw⟩ := hinj hH
    exact ⟨H.val, congrArg Subtype.val he⟩

/-- `app:ch_background:defn:bg-geometry`: the shared cube-reference
neighborhood supplies the full-rank input to the actual ambient normal inverse. -/
theorem secondJetNormalMap_range_of_mem_cubeStressJetNeighborhood
    {n : ℕ} (hn : 5 ≤ n)
    {J : SecondJet (Euclidean n) (Euclidean (n + Fintype.card (CoordinatePair n)))}
    (hJ : J ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean (n + Fintype.card (CoordinatePair n)))) :=
  secondJetNormalMap_range_of_comparison _ _ hJ.1 hJ.2.1
    (cubeStressJetNeighborhood_spec hn hJ).1

end JanetCartan.GeometricProfile
