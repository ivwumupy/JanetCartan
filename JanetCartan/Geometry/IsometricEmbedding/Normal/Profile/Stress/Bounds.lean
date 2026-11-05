module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Neighborhood

/-!
# One-high bounds for the actual symmetric stress projection

The projector and projected stresses in `app:ch_background:eq:bg-frame-tame`
have fixed derivative reserve two. Compact second-jet ranges supply all low
bounds. The final theorem derives the rank condition from the actual cube
reference neighborhood, rather than assuming a projected basis.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

variable {n N : ℕ}

/-- `app:ch_background:eq:bg-frame-tame`: one-high estimate for the actual
symmetric stress projector, uniform over a compact nondegenerate jet range. -/
theorem exists_cNorm_stressProjection_le_closedBall
    (F : Euclidean n → Euclidean N) (x a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (hi : ∀ J ∈ t, Function.Injective J.1)
    (hp : ∀ J ∈ t, ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1)
    (hb : ∀ J ∈ t, Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Euclidean n → Euclidean N, ContDiff ℝ ∞ G →
      Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r
          (fun y ↦ (symmetricNormalMap G y).ker.starProjection) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, h⟩ := exists_cNorm_secondJet_comp_le_closedBall a hρ ht
    (g := secondJetStressProjection F x)
    (fun J hJ ↦ (contDiffAt_secondJetStressProjection F x (hi J hJ) (hb J hJ)).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun G hG hGt ↦ ?_⟩
  have he : cNorm (Metric.closedBall a ρ) r
      (fun y ↦ (symmetricNormalMap G y).ker.starProjection) =
      cNorm (Metric.closedBall a ρ) r (secondJetStressProjection F x ∘ secondJet G) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    exact (eventuallyEq_secondJetStressProjection F x hG (y := y)
      (hi (secondJet G y) (hGt hy)) (hp (secondJet G y) (hGt hy))
      (hb (secondJet G y) (hGt hy))).symm
  exact he.trans_le (h G hG hGt)

/-- `app:ch_background:eq:bg-frame-tame`: each specified geometric cube
stress obeys the same fixed-shift, one-high estimate. -/
theorem exists_cNorm_geometricCubeStress_le_closedBall
    (F : Euclidean n → Euclidean N) (x a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (hi : ∀ J ∈ t, Function.Injective J.1)
    (hp : ∀ J ∈ t, ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1)
    (hb : ∀ J ∈ t, Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (r : ℕ) (i : Fin n) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Euclidean n → Euclidean N, ContDiff ℝ ∞ G →
      Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) ≤
          C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, h⟩ := exists_cNorm_secondJet_comp_le_closedBall a hρ ht
    (g := fun J ↦ secondJetCubeStress F x J i)
    (fun J hJ ↦ (contDiffAt_secondJetCubeStress F x (hi J hJ) (hb J hJ) i).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun G hG hGt ↦ ?_⟩
  have he : cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) =
      cNorm (Metric.closedBall a ρ) r ((fun J ↦ secondJetCubeStress F x J i) ∘ secondJet G) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    exact (eventuallyEq_secondJetCubeStress F x hG (y := y)
      (hi (secondJet G y) (hGt hy)) (hp (secondJet G y) (hGt hy))
      (hb (secondJet G y) (hGt hy)) i).symm
  exact he.trans_le (h G hG hGt)

/-- `app:ch_background:eq:bg-frame-tame`: a single estimate for the projector
and the sum of all projected cube-stress norms. -/
theorem exists_cNorm_stressProjection_and_frame_le_closedBall
    (F : Euclidean n → Euclidean N) (x a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (hi : ∀ J ∈ t, Function.Injective J.1)
    (hp : ∀ J ∈ t, ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1)
    (hb : ∀ J ∈ t, Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Euclidean n → Euclidean N, ContDiff ℝ ∞ G →
      Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r
            (fun y ↦ (symmetricNormalMap G y).ker.starProjection) +
          ∑ i, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, h⟩ := exists_cNorm_stressProjection_le_closedBall F x a hρ ht hi hp hb r
  choose D hD hbound using
    exists_cNorm_geometricCubeStress_le_closedBall F x a hρ ht hi hp hb r
  refine ⟨C + ∑ i, D i, add_pos_of_pos_of_nonneg hC
    (Finset.sum_nonneg fun i _ ↦ (hD i).le), fun G hG hGt ↦ ?_⟩
  calc
    _ ≤ C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) +
        ∑ i, D i * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) :=
      add_le_add (h G hG hGt) (Finset.sum_le_sum fun i _ ↦ hbound i G hG hGt)
    _ = _ := by simp only [add_mul, Finset.sum_mul]

/-- `app:ch_background:defn:bg-geometry` and `app:ch_background:eq:bg-frame-tame`:
one fixed neighborhood of the actual cube reference supplies the basis, Gram
gap, and projector/frame bounds. Only explicit compact low-order neighborhood
conditions remain; rank and projected independence are conclusions. -/
theorem exists_cubeBending_stressProjection_and_frame_bounds {n : ℕ} (hn : 5 ≤ n) :
    ∃ δ > 0, ∃ γ > 0,
      ∀ (a : Euclidean n) (ρ : ℝ), 0 < ρ →
      ∀ t : Set (SecondJet (Euclidean n)
        (Euclidean (n + Fintype.card (CoordinatePair n)))), IsCompact t →
      t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0 δ →
      ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        (∀ y ∈ Metric.closedBall a ρ,
          HasCubeStressFrame (symmetricNormalMap G y).ker γ) ∧
        cNorm (Metric.closedBall a ρ) r
            (fun y ↦ (symmetricNormalMap G y).ker.starProjection) +
          ∑ i, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨δ, hδ, γ, hγ, h⟩ := exists_cubeBending_stressJetNeighborhood hn
  refine ⟨δ, hδ, γ, hγ, fun a ρ hρ t ht hsub r ↦ ?_⟩
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_stressProjection_and_frame_le_closedBall
    (ReferenceConstruction.cubeBending n) 0 a hρ ht
    (fun J hJ ↦ (hsub hJ).1) (fun J hJ ↦ (hsub hJ).2.1)
    (fun J hJ ↦ (h J (hsub hJ)).1) r
  refine ⟨C, hC, fun G hG hGt ↦ ⟨?_, hbound G hG hGt⟩⟩
  intro y hy
  have hJ := hsub (hGt hy)
  have hf := (h _ hJ).2
  rw [secondJetFixedSymmetricNormalMap_eq _ _ hG (y := y) hJ.1] at hf
  have hp := hJ.2.1
  change ‖normalProjection (ReferenceConstruction.cubeBending n) 0 -
    firstJetNormalProjection (fderiv ℝ G y)‖ < 1 at hp
  rw [firstJetNormalProjection_eq (f := G) (x := y) hJ.1] at hp
  rwa [fixedSymmetricNormalMap_ker _ _ _ _ hp] at hf

end JanetCartan.GeometricProfile
