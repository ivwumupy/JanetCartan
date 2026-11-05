module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Neighborhood

/-!
# Fixed-shift bounds for all actual geometric coefficients

This assembles `app:ch_background:eq:bg-frame-tame` and the geometric
reconstruction part of `app:ch_waves:eq:joint-tame`. All constants are uniform
on a compact second-jet range in the proved cube-reference neighborhood.
The reserve is two, independently of the order. Phase and transport estimates
belong to the leading-wave construction, not to this coefficient theorem.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.StressFrame

namespace JanetCartan.GeometricProfile

open StressFrame

/-- The sum of the actual coefficient norms in
`app:ch_background:eq:bg-frame-tame` and `app:ch_waves:eq:ambient-normal-inverse`,
including metric, inverse metric, and every second-form entry. This is a
numerical expression, not an assumed package of coefficient estimates. -/
def geometricCoefficientNorm {n N : ℕ} (s : Set (Euclidean n)) (r : ℕ)
    (G : Euclidean n → Euclidean N) : ℝ :=
  (cNorm s r (inducedMetric G) + cNorm s r (fun y ↦ (inducedMetric G y)⁻¹)) +
    (∑ i, ∑ j, cNorm s r (fun y ↦ secondFundamentalForm G y i j)) +
    (cNorm s r (fun y ↦ (symmetricNormalMap G y).ker.starProjection) +
      (∑ i, cNorm s r (fun y ↦ geometricCubeStress G y i)) +
      cNorm s r (fun y ↦ (Matrix.gram ℝ (geometricCubeStress G y))⁻¹) +
      cNorm s r (geometricReducedCoefficients G)) +
    cNorm s r (fun y ↦ (AmbientResponse.canonicalNormalCompletion G y).toContinuousLinearMap)

/-- `app:ch_background:eq:bg-frame-tame`: the aggregate of actual norms is nonnegative. -/
theorem geometricCoefficientNorm_nonneg {n N : ℕ} (s : Set (Euclidean n)) (r : ℕ)
    (G : Euclidean n → Euclidean N) : 0 ≤ geometricCoefficientNorm s r G := by
  unfold geometricCoefficientNorm
  repeat' first
    | exact cNorm_nonneg _ _ _
    | apply add_nonneg
    | apply Finset.sum_nonneg
    | intro i hi

/-- `app:ch_background:eq:bg-frame-tame` and the geometric coefficient part of
`app:ch_waves:eq:joint-tame`: one high map norm controls every actual coefficient
with the common reserve two. The common low-order neighborhood supplies all
rank and Gram conditions; none of the desired estimates is a premise. -/
theorem exists_cNorm_geometricCoefficients_le_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
        ContDiff ℝ ∞ G → Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        geometricCoefficientNorm (Metric.closedBall a ρ) r G ≤
          C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) := by
  have hi : ∀ J ∈ t, Function.Injective J.1 := fun _ hJ ↦ (hsub hJ).1
  have hr := fun J (hJ : J ∈ t) ↦
    secondJetNormalMap_range_of_mem_cubeStressJetNeighborhood hn (hsub hJ)
  obtain ⟨M, hM, hm⟩ := exists_cNorm_metric_and_inverse_le_closedBall a hρ
    (ht.image continuous_fst) (by
      rintro L ⟨J, hJ, rfl⟩
      exact firstJetMetric_isUnit_of_injective (hi J hJ)) r
  choose B hB hb using exists_cNorm_secondFundamentalForm_le_closedBall a hρ ht hi r
  obtain ⟨S, hS, hs⟩ := exists_cNorm_stressCoefficients_le_closedBall hn a hρ ht hsub r
  obtain ⟨N, hN, hnrm⟩ :=
    exists_cNorm_canonicalNormalCompletion_le_closedBall a hρ ht hi hr r
  refine ⟨M + (∑ i, ∑ j, B i j) + S + N, ?_, fun G hG hGt ↦ ?_⟩
  · exact add_pos (add_pos (add_pos_of_pos_of_nonneg hM
      (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hB i j).le)) hS) hN
  · have hm' := hm G hG (fun y hy ↦ ⟨secondJet G y, hGt hy, rfl⟩)
    have hmetric : cNorm (Metric.closedBall a ρ) r (inducedMetric G) +
        cNorm (Metric.closedBall a ρ) r (fun y ↦ (inducedMetric G y)⁻¹) ≤
        M * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G) :=
      hm'.trans (mul_le_mul_of_nonneg_left
        (add_le_add_right (cNorm_mono_order (by omega)) 1) hM.le)
    have hform := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hb i j G hG hGt))
    have h := add_le_add (add_le_add (add_le_add hmetric hform) (hs G hG hGt))
      (hnrm G hG hGt)
    simpa only [geometricCoefficientNorm, ← Finset.sum_mul, ← add_mul] using h

/-- `app:cor:fixed-profile-transfer`: all actual coefficient norms together
inherit a common profile with reserve two. Constants precede the map, scale,
and baseline orders, and the scalar interpolation input has been discharged. -/
theorem exists_geometricCoefficient_profile_bound_closedBall
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
        ∀ r, geometricCoefficientNorm (Metric.closedBall a ρ) r G ≤
          (C r * (1 + A (r + 2))) * T ^ (r - ν) := by
  choose C hC hbound using exists_cNorm_geometricCoefficients_le_closedBall hn a hρ ht hsub
  exact ⟨C, hC, fun G hG hGt R ν T A hp hT hA hloss r ↦
    JointBudget.fixed_profile_transfer_bound hT (hA (r + 2)) (hC r).le hloss
      (hp (r + 2)) (hbound r G hG hGt)⟩

/-- `app:ch_waves:eq:joint-tame`, restricted to its actual geometric
reconstruction part: the same compact immersion jets and a compact covector
first-jet range give one high norm of either input. All geometric rank premises
of the reconstruction theorem follow from the shared cube neighborhood. -/
theorem exists_cNorm_geometricCoefficients_and_reconstruction_le_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn))
    {v : Set (Euclidean n × (Euclidean n →L[ℝ] Euclidean n))} (hv : IsCompact v)
    (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)))
        (u : Euclidean n → Euclidean n),
        ContDiff ℝ ∞ G → ContDiff ℝ ∞ u →
        Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        Set.MapsTo (fun y ↦ (u y, fderiv ℝ u y)) (Metric.closedBall a ρ) v →
        geometricCoefficientNorm (Metric.closedBall a ρ) r G +
          cNorm (Metric.closedBall a ρ) r
            (LeadingWave.reconstruction G (AmbientResponse.canonicalNormalCompletion G) u) ≤
          C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G +
            cNorm (Metric.closedBall a ρ) (r + 1) u) := by
  obtain ⟨C, hC, hcoef⟩ := exists_cNorm_geometricCoefficients_le_closedBall hn a hρ ht hsub r
  obtain ⟨D, hD, hrec⟩ := exists_cNorm_reconstruction_le_closedBall a hρ (ht.prod hv)
    (fun _ hq ↦ (hsub hq.1).1)
    (fun _ hq ↦ secondJetNormalMap_range_of_mem_cubeStressJetNeighborhood hn (hsub hq.1)) r
  refine ⟨C + D, add_pos hC hD, fun G u hG hu hGt huv ↦ ?_⟩
  have hc := (hcoef G hG hGt).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (cNorm_nonneg (Metric.closedBall a ρ) (r + 1) u)) hC.le)
  have hr := hrec G u hG hu (fun y hy ↦ ⟨hGt hy, huv hy⟩)
  simpa only [← add_mul] using add_le_add hc hr

/-- `app:cor:fixed-profile-transfer` and the geometric part of
`app:ch_waves:eq:joint-tame`: joint profiles transfer with one fixed reserve,
two for the immersion and one for the covector. Both high contributions share
the same scale exponent; no product of high norms occurs. -/
theorem exists_geometricCoefficients_and_reconstruction_profile_bound_closedBall
    {n : ℕ} (hn : 5 ≤ n) (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n)
      (Euclidean (n + Fintype.card (CoordinatePair n))))} (ht : IsCompact t)
    (hsub : t ⊆ stressJetNeighborhood (ReferenceConstruction.cubeBending n) 0
      (cubeStressJetRadius hn))
    {v : Set (Euclidean n × (Euclidean n →L[ℝ] Euclidean n))} (hv : IsCompact v) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)))
        (u : Euclidean n → Euclidean n),
        ContDiff ℝ ∞ G → ContDiff ℝ ∞ u →
        Set.MapsTo (secondJet G) (Metric.closedBall a ρ) t →
        Set.MapsTo (fun y ↦ (u y, fderiv ℝ u y)) (Metric.closedBall a ρ) v →
      ∀ (R S ν : ℕ) (T : ℝ) (A B : ℕ → ℝ),
        HasDerivativeProfile (Metric.closedBall a ρ) G R T A →
        HasDerivativeProfile (Metric.closedBall a ρ) u S T B →
        1 ≤ T → (∀ r, 0 ≤ A r) → (∀ r, 0 ≤ B r) → 2 + ν ≤ R → 1 + ν ≤ S →
        ∀ r, geometricCoefficientNorm (Metric.closedBall a ρ) r G +
          cNorm (Metric.closedBall a ρ) r
            (LeadingWave.reconstruction G (AmbientResponse.canonicalNormalCompletion G) u) ≤
          (C r * (1 + A (r + 2) + B (r + 1))) * T ^ (r - ν) := by
  choose C hC hbound using
    exists_cNorm_geometricCoefficients_and_reconstruction_le_closedBall hn a hρ ht hsub hv
  refine ⟨C, hC, fun G u hG hu hGt huv R S ν T A B hPG hPu hT hA hB hR hS r ↦ ?_⟩
  have hGhigh := (hPG (r + 2)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (show r + 2 - R ≤ r - ν by omega))
      (hA (r + 2)))
  have huhigh := (hPu (r + 1)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (show r + 1 - S ≤ r - ν by omega))
      (hB (r + 1)))
  calc
    _ ≤ C r * (1 + cNorm (Metric.closedBall a ρ) (r + 2) G +
        cNorm (Metric.closedBall a ρ) (r + 1) u) := hbound r G u hG hu hGt huv
    _ ≤ C r * (T ^ (r - ν) + A (r + 2) * T ^ (r - ν) +
        B (r + 1) * T ^ (r - ν)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (one_le_pow₀ hT) hGhigh) huhigh) (hC r).le
    _ = _ := by ring

end JanetCartan.GeometricProfile
