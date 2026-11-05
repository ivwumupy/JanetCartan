module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Gram.Jet

/-!
# One-high bounds for the actual inverse stress Gram matrix

The inverse Gram term in `app:ch_background:eq:bg-frame-tame` has fixed
derivative shift two. The shared cube-reference neighborhood supplies the
frame basis and invertibility, while a compact second-jet range supplies the
uniform coefficient bounds. All matrix norms are Frobenius norms.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

/-- `app:ch_background:defn:bg-geometry`: the explicit shared neighborhood
implies independence of the actual projected cube stresses. -/
theorem linearIndependent_geometricCubeStress_of_mem_cubeStressJetNeighborhood
    {n : ℕ} (hn : 5 ≤ n)
    {G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n))}
    (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hJ : secondJet G y ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    LinearIndependent ℝ (geometricCubeStress G y) := by
  obtain ⟨hB, hf⟩ := cubeStressJetNeighborhood_spec hn hJ
  have hi := linearIndependent_secondJetCubeStress _ _ hB hf
  have he : secondJetCubeStress (ReferenceConstruction.cubeBending n) 0 (secondJet G y) =
      geometricCubeStress G y := by
    funext i
    exact (eventuallyEq_secondJetCubeStress _ _ hG hJ.1 hJ.2.1 hB i).eq_of_nhds
  exact he ▸ hi

/-- `app:ch_background:defn:bg-geometry`: the actual frame Gram matrix is
invertible throughout the shared explicit neighborhood, with no extra premise. -/
theorem geometricCubeStressGram_isUnit_of_mem_cubeStressJetNeighborhood
    {n : ℕ} (hn : 5 ≤ n)
    {G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n))}
    (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hJ : secondJet G y ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    IsUnit (Matrix.gram ℝ (geometricCubeStress G y)) :=
  (Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_geometricCubeStress_of_mem_cubeStressJetNeighborhood hn hG hJ)).isUnit

/-- `app:ch_background:eq:bg-frame-tame`: the actual inverse frame Gram
matrix obeys a uniform one-high estimate with fixed shift two on any
positive-radius closed ball whose second jets lie in a fixed compact subset
of the shared cube-reference neighborhood. Independence, invertibility and
coefficient smoothness are derived from the neighborhood theorem. -/
theorem exists_cNorm_geometricCubeStressGram_inv_le_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r
          (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, h⟩ := exists_cNorm_secondJet_comp_le_closedBall a hρ ht
    (g := fun J ↦ (secondJetCubeStressGram (ReferenceConstruction.cubeBending n) 0 J)⁻¹)
    (fun J hJ ↦ (contDiffAt_secondJetCubeStressGram_inv _ _ (hsub hJ).1
      (cubeStressJetNeighborhood_spec hn (hsub hJ)).1
      (cubeStressJetNeighborhood_spec hn (hsub hJ)).2).of_le
        (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun G hG hGt ↦ ?_⟩
  have he : cNorm (Metric.closedBall a ρ) r
      (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) =
      cNorm (Metric.closedBall a ρ) r
        ((fun J ↦ (secondJetCubeStressGram (ReferenceConstruction.cubeBending n) 0 J)⁻¹) ∘
          secondJet G) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    have hJ := hsub (hGt hy)
    exact (eventuallyEq_secondJetCubeStressGram_inv _ _ hG hJ.1 hJ.2.1
      (cubeStressJetNeighborhood_spec hn hJ).1).symm
  exact he.trans_le (h G hG hGt)

end JanetCartan.GeometricProfile
