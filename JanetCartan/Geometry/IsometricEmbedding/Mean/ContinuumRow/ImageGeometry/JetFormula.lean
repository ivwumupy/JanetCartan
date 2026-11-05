module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced

/-!
# The image coefficients in the ambient inverse chart

For `app:ch_background:eq:bg-frame-tame` and `app:ch_waves:eq:reduced-symbol`,
the ambient normal inverse gives one formula on the entire admissible jet locus.
Unlike a fixed-normal-plane chart, this formula applies to the full compact
range of the actual reference. Both principal and connection entries are kept.
The consumer is the periodic coefficient construction for `ContinuumRow.imageChannel`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.ProjectedStressFrame JanetCartan.GeometricProfile

namespace JanetCartan.ContinuumRow.ImageGeometry

variable {n N : ℕ}

/-- The ambient inverse formula for every coefficient of `P_G`
(`app:ch_waves:eq:reduced-symbol`). In particular every zeroth-order entry
retains the negative stress-Christoffel contraction. -/
def ambientReducedCoefficients (J : StressJet n N) : ReducedCoefficientIndex n → ℝ
  | .inl (a, i, k) => jetStress (cubeStress n i) J a k
  | .inr (i, k) => -∑ a, ∑ b,
      jetStress (cubeStress n i) J a b * secondJetChristoffel J a b k

private def tensorEntry (a b : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) b).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) a))

/-- Smoothness of all image coefficients follows from the two actual inverse
formulas (`app:ch_background:eq:bg-frame-tame`). -/
theorem contDiffAt_ambientReducedCoefficients {J : StressJet n N}
    (hg : IsUnit (jetMetric J)) (hA : IsUnit (jetAmbient J)) :
    ContDiffAt ℝ ∞ (@ambientReducedCoefficients n N) J := by
  have hi : Function.Injective J.1 :=
    J.1.adjoint_comp_self_injective_iff.mp
      ((ContinuousLinearMap.isUnit_iff_bijective.mp hg).1)
  have hq (i a b : Fin n) :
      ContDiffAt ℝ ∞ (fun K ↦ jetStress (cubeStress n i) K a b) J :=
    (tensorEntry a b).contDiff.contDiffAt.comp J
      (contDiffAt_jetStress hg hA (cubeStress n i))
  apply contDiffAt_pi.mpr
  rintro (⟨a, i, k⟩ | ⟨i, k⟩)
  · exact hq i a k
  · exact (ContDiffAt.sum fun a _ ↦ ContDiffAt.sum fun b _ ↦
      (hq i a b).mul (contDiffAt_secondJetChristoffel
        (firstJetMetric_isUnit_of_injective hi) a b k)).neg

/-- The prescribed geometric cube stress equals the projected stress from the
ambient normal inverse; this is a proved identification of the two constructions
(`app:ch_background:defn:bg-geometry`). -/
theorem geometricCubeStress_val_eq_projectedStress
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (i : Fin n) :
    (StressFrame.geometricCubeStress F x i).val = projectedStress F x i :=
  (projectedStress_eq_projectedCubeStress hF hrank i).symm

/-- The ambient formula is exactly the existing geometric coefficient array,
including its entire zeroth-order term (`app:ch_waves:eq:reduced-symbol`). -/
theorem ambientReducedCoefficients_stressJet
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    ambientReducedCoefficients (stressJet F x) = geometricReducedCoefficients F x := by
  have htwo : ContDiffAt ℝ 2 F x := hF.contDiffAt.of_le (by simp)
  have hq (i : Fin n) : jetStress (cubeStress n i) (stressJet F x) =
      (StressFrame.geometricCubeStress F x i).val :=
    (jetStress_stressJet htwo hi i).trans
      (geometricCubeStress_val_eq_projectedStress htwo hrank i).symm
  funext c
  rcases c with ⟨a, i, k⟩ | ⟨i, k⟩
  · simp only [ambientReducedCoefficients, geometricReducedCoefficients,
      NullTransport.principalCoefficient, hq]
  · simp only [ambientReducedCoefficients, geometricReducedCoefficients,
      reducedZerothCoefficient, hq]
    change -∑ a, ∑ b, _ * secondJetChristoffel (secondJet F x) a b k = _
    simp only [secondJetChristoffel_eq hF]

/-- On an open immersive full-normal-rank domain the two formulas agree near
each point, so all physical jets agree (`app:ch_background:eq:bg-frame-tame`). -/
theorem ambientReducedCoefficients_eventuallyEq
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {x : Euclidean n} (hx : x ∈ U) :
    ambientReducedCoefficients ∘ stressJet F =ᶠ[𝓝 x] geometricReducedCoefficients F := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact ambientReducedCoefficients_stressJet hF (hi y hy) (hrank y hy)

/-- Actual smoothness of the geometric coefficient array on the geometric
working domain (`app:ch_background:defn:bg-geometry`). -/
theorem contDiffOn_geometricReducedCoefficients
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (geometricReducedCoefficients F) U := by
  intro x hx
  have hg := isUnit_jetMetric_stressJet (hi x hx)
  have hA : IsUnit (jetAmbient (stressJet F x)) := by
    rw [jetAmbient_stressJet (hF.contDiffAt.of_le (by simp)) (hi x hx)]
    exact AmbientResponse.ambientNormalOperator_isUnit (hrank x hx)
  exact (((contDiffAt_ambientReducedCoefficients hg hA).comp x
    (contDiff_stressJet hF).contDiffAt).congr_of_eventuallyEq
      (ambientReducedCoefficients_eventuallyEq hF hU hi hrank hx).symm).contDiffWithinAt

/-- A compact admissible ambient jet range gives a one-high estimate with
reserve exactly two. The current-neighborhood producer, rather than the caller
of the final construction, supplies this range (`app:ch_background:eq:bg-frame-tame`). -/
theorem exists_cNorm_ambientReducedCoefficients_comp_le
    (a : Euclidean n) {r : ℝ} (hr : 0 < r)
    {L : Set (StressJet n N)} (hL : IsCompact L)
    (hu : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      Set.MapsTo (stressJet F) (Metric.closedBall a r) L →
      cNorm (Metric.closedBall a r) m (ambientReducedCoefficients ∘ stressJet F) ≤
        C * (1 + cNorm (Metric.closedBall a r) (m + 2) F) := by
  exact exists_cNorm_secondJet_comp_le_closedBall a hr hL
    (fun J hJ ↦ (contDiffAt_ambientReducedCoefficients
      (hu J hJ).1 (hu J hJ).2).of_le (by simp))

end JanetCartan.ContinuumRow.ImageGeometry
