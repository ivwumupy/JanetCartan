module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Gram
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# Tame stress coefficients

The full estimate in `app:ch_background:eq:bg-frame-tame` holds for the actual
symmetric kernel projector, projected cube stresses, inverse frame Gram matrix,
and all reduced-operator coefficients, including the Christoffel terms. It has
fixed derivative shift two on compact second-jet ranges in one cube-reference
neighborhood. That neighborhood supplies the frame basis and positive Gram gap;
no independence, coefficient smoothness, or coefficient bounds are assumed.

The same fixed shift transfers derivative profiles to each coefficient field.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

/-- `app:ch_background:defn:bg-geometry`: the shared cube-reference neighborhood
gives a basis of the actual stress kernel and the fixed positive Gram gap. -/
theorem hasCubeStressFrame_of_mem_cubeStressJetNeighborhood
    {n : ℕ} (hn : 5 ≤ n)
    {G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n))}
    (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hJ : secondJet G y ∈ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    HasCubeStressFrame (symmetricNormalMap G y).ker (cubeStressJetGramGap hn) := by
  have hf := (cubeStressJetNeighborhood_spec hn hJ).2
  rw [secondJetFixedSymmetricNormalMap_eq _ _ hG (y := y) hJ.1] at hf
  have hp := hJ.2.1
  change ‖normalProjection (ReferenceConstruction.cubeBending n) 0 -
    firstJetNormalProjection (fderiv ℝ G y)‖ < 1 at hp
  rw [firstJetNormalProjection_eq (f := G) (x := y) hJ.1] at hp
  rwa [fixedSymmetricNormalMap_ker _ _ _ _ hp] at hf

/-- `app:ch_background:eq:bg-frame-tame`: the sum of all four actual coefficient
norms has one high map norm with fixed shift two. The constant precedes the map,
and all rank and Gram-invertibility conditions follow from the explicit shared
cube-reference neighborhood. The inverse Gram uses its Frobenius norm; the
reduced coefficient package contains every principal and zeroth-order entry. -/
theorem exists_cNorm_stressCoefficients_le_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        cNorm (Metric.closedBall a ρ) r
            (fun y ↦ (symmetricNormalMap G y).ker.starProjection) +
          (∑ i, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i)) +
          cNorm (Metric.closedBall a ρ) r
            (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) +
          cNorm (Metric.closedBall a ρ) r (geometricReducedCoefficients G) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  obtain ⟨C, hC, hframe⟩ := exists_cNorm_stressProjection_and_frame_le_closedBall
    (ReferenceConstruction.cubeBending n) 0 a hρ ht
    (fun _ hJ ↦ (hsub hJ).1) (fun _ hJ ↦ (hsub hJ).2.1)
    (fun _ hJ ↦ (cubeStressJetNeighborhood_spec hn (hsub hJ)).1) r
  obtain ⟨D, hD, hgram⟩ :=
    exists_cNorm_geometricCubeStressGram_inv_le_closedBall hn a hρ ht hsub r
  obtain ⟨E, hE, hreduced⟩ :=
    exists_cNorm_cubeReducedCoefficients_le_closedBall hn a hρ ht hsub r
  refine ⟨C + D + E, add_pos (add_pos hC hD) hE, fun G hG hGt ↦ ?_⟩
  calc
    _ ≤ C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) +
        D * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) +
        E * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) :=
      add_le_add (add_le_add (hframe G hG hGt) (hgram G hG hGt)) (hreduced G hG hGt)
    _ = _ := by rw [add_mul, add_mul]

/-- `app:ch_background:defn:bg-geometry` and `app:ch_background:eq:bg-frame-tame`:
one fixed positive neighborhood radius and Gram gap give the actual stress basis
and the full four-term estimate. Only compact low-order jet-range conditions
remain; neither the frame nor any desired coefficient estimate is a premise. -/
theorem exists_cubeBending_stressCoefficients_bounds {n : ℕ} (hn : 5 ≤ n) :
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
          (∑ i, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i)) +
          cNorm (Metric.closedBall a ρ) r
            (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) +
          cNorm (Metric.closedBall a ρ) r (geometricReducedCoefficients G) ≤
            C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  refine ⟨cubeStressJetRadius hn, cubeStressJetRadius_pos hn,
    cubeStressJetGramGap hn, cubeStressJetGramGap_pos hn, fun a ρ hρ t ht hsub r ↦ ?_⟩
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_stressCoefficients_le_closedBall hn a hρ ht hsub r
  exact ⟨C, hC, fun G hG hGt ↦
    ⟨fun _ hy ↦ hasCubeStressFrame_of_mem_cubeStressJetNeighborhood hn hG (hsub (hGt hy)),
      hbound G hG hGt⟩⟩

/-- `app:cor:fixed-profile-transfer` applied to the complete estimate
`app:ch_background:eq:bg-frame-tame`: all four actual coefficient families
inherit one common profile constant with fixed reserve two. The constants are
chosen before the map, the scale, and the baseline orders. -/
theorem exists_stressCoefficient_profiles_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
        HasDerivativeProfile (Metric.closedBall a ρ) G R T A →
        1 ≤ T → (∀ r, 0 ≤ A r) → 2 + ν ≤ R →
        HasDerivativeProfile (Metric.closedBall a ρ)
          (fun y ↦ (symmetricNormalMap G y).ker.starProjection) ν T
          (fun r ↦ C r * (1 + A (r + 2))) ∧
        (∀ i, HasDerivativeProfile (Metric.closedBall a ρ)
          (fun y ↦ geometricCubeStress G y i) ν T
          (fun r ↦ C r * (1 + A (r + 2)))) ∧
        HasDerivativeProfile (Metric.closedBall a ρ)
          (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) ν T
          (fun r ↦ C r * (1 + A (r + 2))) ∧
        HasDerivativeProfile (Metric.closedBall a ρ) (geometricReducedCoefficients G) ν T
          (fun r ↦ C r * (1 + A (r + 2))) := by
  choose C hC hbound using exists_cNorm_stressCoefficients_le_closedBall hn a hρ ht hsub
  refine ⟨C, hC, fun G hG hGt R ν T A hp hT hA hloss ↦ ?_⟩
  have htotal (r : ℕ) := JointBudget.fixed_profile_transfer_bound
    (r := r) (c := 2) hT (hA (r + 2)) (hC r).le hloss
    (hp (r + 2)) (hbound r G hG hGt)
  have hprojector (r : ℕ) := cNorm_nonneg (Metric.closedBall a ρ) r
    (fun y ↦ (symmetricNormalMap G y).ker.starProjection)
  have hframe (r : ℕ) : 0 ≤
      ∑ i, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) :=
    Finset.sum_nonneg fun i _ ↦
      cNorm_nonneg (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i)
  have hgram (r : ℕ) := cNorm_nonneg (Metric.closedBall a ρ) r
    (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹)
  have hreduced (r : ℕ) := cNorm_nonneg (Metric.closedBall a ρ) r
    (geometricReducedCoefficients G)
  refine ⟨fun r ↦ ?_, fun i r ↦ ?_, fun r ↦ ?_, fun r ↦ ?_⟩
  · linarith only [htotal r, hframe r, hgram r, hreduced r]
  · have hi : cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y i) ≤
        ∑ j, cNorm (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y j) :=
      Finset.single_le_sum (fun j _ ↦
        cNorm_nonneg (Metric.closedBall a ρ) r (fun y ↦ geometricCubeStress G y j))
        (Finset.mem_univ i)
    linarith only [hi, htotal r, hprojector r, hgram r, hreduced r]
  · linarith only [htotal r, hprojector r, hframe r, hreduced r]
  · linarith only [htotal r, hprojector r, hframe r, hgram r]

end JanetCartan.GeometricProfile
