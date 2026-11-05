module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Jet

/-!
# A fixed low-order neighborhood for stress coefficients

In `app:ch_background:defn:bg-geometry`, the operator neighborhood of the
reference supplies surjectivity, a basis, and a positive Gram gap. This module
expresses that neighborhood in second-jet variables. None of those conclusions
is included in the definition of the neighborhood.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

variable {n N : ℕ}

/-- The explicit low-order jet neighborhood in
`app:ch_background:defn:bg-geometry`: immersion, nearby normal projections,
and a nearby second form in the fixed reference normal space. -/
def stressJetNeighborhood (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (δ : ℝ) : Set (SecondJet (Euclidean n) (Euclidean N)) :=
  {J | Function.Injective J.1 ∧
    ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1 ∧
    ‖secondJetFixedSymmetricNormalMap F x J - symmetricNormalMap F x‖ < δ}

/-- `app:ch_background:defn:bg-geometry`: the reference neighborhood theorem
supplies rank, the specified basis and a uniform Gram gap for all jets in the
explicit neighborhood. -/
theorem exists_stressJetNeighborhood {n N : ℕ} (hn : 5 ≤ n)
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hsurj : Function.Surjective (symmetricNormalMap F x))
    (hker : (symmetricNormalMap F x).ker =
      Submodule.span ℝ (Set.range (cubeSymmetricStress n))) :
    ∃ δ > 0, ∃ γ > 0, ∀ J ∈ stressJetNeighborhood F x δ,
      Function.Surjective (secondJetFixedSymmetricNormalMap F x J) ∧
        HasCubeStressFrame (secondJetFixedSymmetricNormalMap F x J).ker γ := by
  obtain ⟨δ, hδ, γ, hγ, h⟩ := exists_operator_cubeStressFrame_neighborhood hn
    (symmetricNormalMap F x) hsurj hker
  exact ⟨δ, hδ, γ, hγ, fun J hJ ↦ h _ hJ.2.2⟩

/-- `app:ch_background:defn:bg-geometry`: for the actual analytic cube
reference, all reference rank and kernel hypotheses are discharged. -/
theorem exists_cubeBending_stressJetNeighborhood {n : ℕ} (hn : 5 ≤ n) :
    ∃ δ > 0, ∃ γ > 0,
      ∀ J ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0 δ,
        Function.Surjective
          (secondJetFixedSymmetricNormalMap (ReferenceConstruction.cubeBending n) 0 J) ∧
        HasCubeStressFrame
          (secondJetFixedSymmetricNormalMap (ReferenceConstruction.cubeBending n) 0 J).ker γ :=
  exists_stressJetNeighborhood hn _ _ (symmetricNormalMap_cubeBending_surjective hn)
    (symmetricNormalMap_cubeBending_ker hn)

/-- A fixed radius furnished by the proved reference-neighborhood theorem
for `app:ch_background:eq:bg-frame-tame`. Shared by all coefficient bounds. -/
def cubeStressJetRadius {n : ℕ} (hn : 5 ≤ n) : ℝ :=
  (exists_cubeBending_stressJetNeighborhood hn).choose

/-- `app:ch_background:defn:bg-geometry`: positivity of the shared radius. -/
theorem cubeStressJetRadius_pos {n : ℕ} (hn : 5 ≤ n) : 0 < cubeStressJetRadius hn :=
  (exists_cubeBending_stressJetNeighborhood hn).choose_spec.1

/-- The shared positive Gram gap in `app:ch_background:defn:bg-geometry`,
chosen from a proved existence theorem, without additional geometric input. -/
def cubeStressJetGramGap {n : ℕ} (hn : 5 ≤ n) : ℝ :=
  (exists_cubeBending_stressJetNeighborhood hn).choose_spec.2.choose

/-- `app:ch_background:defn:bg-geometry`: positivity of the shared Gram gap. -/
theorem cubeStressJetGramGap_pos {n : ℕ} (hn : 5 ≤ n) : 0 < cubeStressJetGramGap hn :=
  (exists_cubeBending_stressJetNeighborhood hn).choose_spec.2.choose_spec.1

/-- `app:ch_background:defn:bg-geometry`: the shared explicit neighborhood
provides surjectivity and the specified frame with its uniform Gram gap. -/
theorem cubeStressJetNeighborhood_spec {n : ℕ} (hn : 5 ≤ n)
    {J : SecondJet (Euclidean n) (Euclidean (n + Fintype.card (CoordinatePair n)))}
    (hJ : J ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    Function.Surjective
      (secondJetFixedSymmetricNormalMap (ReferenceConstruction.cubeBending n) 0 J) ∧
    HasCubeStressFrame
      (secondJetFixedSymmetricNormalMap (ReferenceConstruction.cubeBending n) 0 J).ker
      (cubeStressJetGramGap hn) :=
  (exists_cubeBending_stressJetNeighborhood hn).choose_spec.2.choose_spec.2 J hJ

/-- `app:ch_background:defn:bg-geometry`: every positive-radius jet
neighborhood contains the actual cube reference jet at the center. -/
theorem secondJet_cubeBending_zero_mem_stressJetNeighborhood {n : ℕ}
    (hn : 5 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    secondJet (ReferenceConstruction.cubeBending n) 0 ∈
      stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0 δ := by
  have hi : IsImmersionOn (ReferenceConstruction.cubeBending n) Set.univ :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun y _ ↦ ReferenceConstruction.cubeBending_inducedMetric (by omega) y)
  have hi0 := hi 0 (Set.mem_univ 0)
  refine ⟨hi0, ?_, ?_⟩
  · change ‖normalProjection (ReferenceConstruction.cubeBending n) 0 -
      firstJetNormalProjection (fderiv ℝ (ReferenceConstruction.cubeBending n) 0)‖ < 1
    rw [firstJetNormalProjection_eq hi0]
    simp
  · rw [secondJetFixedSymmetricNormalMap_eq _ _
      (ReferenceConstruction.cubeBending_analyticOnNhd n).contDiff hi0,
      fixedSymmetricNormalMap_self]
    convert hδ using 1
    rw [show symmetricNormalMap (ReferenceConstruction.cubeBending n) 0 -
      symmetricNormalMap (ReferenceConstruction.cubeBending n) 0 = 0 by
        ext H : 1
        simp]
    rw [ContinuousLinearMap.opNorm_zero]

/-- `app:ch_background:defn:bg-geometry`: the jet stresses are exactly the
projections in the fixed-space frame theorem. -/
theorem secondJetCubeStress_eq_projectedCubeStress
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)}
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) (i : Fin n) :
    secondJetCubeStress F x J i =
      projectedCubeStress (secondJetFixedSymmetricNormalMap F x J).toLinearMap i := by
  rw [secondJetCubeStress, secondJetStressProjection,
    NormalInverse.continuousKernelProjection_eq_starProjection _ hB]
  rfl

end JanetCartan.GeometricProfile
