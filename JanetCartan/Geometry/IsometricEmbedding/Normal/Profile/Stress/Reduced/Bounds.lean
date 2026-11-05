module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula

/-!
# Fixed-shift one-high bounds for the actual reduced operator

The coefficient package contains every principal and zeroth-order coefficient
of `P_G` from `app:ch_waves:eq:reduced-symbol`. The estimate in
`app:ch_background:eq:bg-frame-tame` has derivative reserve exactly two.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

variable {n N : ℕ}

/-- `app:ch_background:eq:bg-frame-tame`: one high map norm controls the
entire actual reduced-operator coefficient field, uniformly on a compact
second-jet range satisfying the explicit low-order geometric conditions. -/
theorem exists_cNorm_geometricReducedCoefficients_le_closedBall
    (F : Euclidean n → Euclidean N) (x a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (hi : ∀ J ∈ t, Function.Injective J.1)
    (hp : ∀ J ∈ t, ‖normalProjection F x - firstJetNormalProjection J.1‖ < 1)
    (hb : ∀ J ∈ t, Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Euclidean n → Euclidean N, ContDiff ℝ ∞ G →
      Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r (geometricReducedCoefficients G) ≤
          C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, h⟩ := exists_cNorm_secondJet_comp_le_closedBall a hρ ht
    (g := secondJetReducedCoefficients F x)
    (fun J hJ ↦ (contDiffAt_secondJetReducedCoefficients F x (hi J hJ) (hb J hJ)).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun G hG hGt ↦ ?_⟩
  have he : cNorm (Metric.closedBall a ρ) r (geometricReducedCoefficients G) =
      cNorm (Metric.closedBall a ρ) r (secondJetReducedCoefficients F x ∘ secondJet G) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    exact (eventuallyEq_secondJetReducedCoefficients F x hG (y := y)
      (hi (secondJet G y) (hGt hy)) (hp (secondJet G y) (hGt hy))
      (hb (secondJet G y) (hGt hy))).symm
  exact he.trans_le (h G hG hGt)

/-- `app:ch_background:eq:bg-frame-tame`: in the fixed cube-reference
neighborhood the rank hypotheses are theorems, and all principal and
zeroth-order coefficients of the actual `P_G` obey the fixed-shift-two
one-high estimate. The constant is chosen before the smooth map `G`. -/
theorem exists_cNorm_cubeReducedCoefficients_le_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (htn : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
          cNorm (Metric.closedBall a ρ) r (geometricReducedCoefficients G) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) :=
  exists_cNorm_geometricReducedCoefficients_le_closedBall
    (ReferenceConstruction.cubeBending n) 0 a hρ ht
    (fun _ hJ ↦ (htn hJ).1) (fun _ hJ ↦ (htn hJ).2.1)
    (fun _ hJ ↦ (cubeStressJetNeighborhood_spec hn (htn hJ)).1) r

/-- `app:ch_background:defn:bg-geometry`: actual coefficient smoothness on
the fixed cube jet neighborhood follows from the formulas and the proved
reference rank theorem, with no smoothness premise on the coefficients. -/
theorem contDiffAt_cubeReducedCoefficients
    {n : ℕ} (hn : 5 ≤ n)
    {G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n))}
    (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hy : secondJet G y ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    ContDiffAt ℝ ∞ (geometricReducedCoefficients G) y :=
  contDiffAt_geometricReducedCoefficients (ReferenceConstruction.cubeBending n) 0 hG
    hy.1 hy.2.1 (cubeStressJetNeighborhood_spec hn hy).1

end JanetCartan.GeometricProfile
