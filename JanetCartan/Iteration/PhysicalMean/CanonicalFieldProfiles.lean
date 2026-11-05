module

public import JanetCartan.Iteration.PhysicalBackground.BaseProfiles

/-!
# The actual physical mean base and its full strain

Consumer: `exists_history_completedMean_profile`, the physical field part of
`main:prop:mean`. This applies the existing actual uncut image/base producer and
the actual physical-history raising profile. No successful field or strain
profile is assumed, and no product of two full high C-norms is used.

The raw datum is the SAME original initializer plus the current positive
uncut raw right inverse of the finite source iterate. Its membership/profile
remain those producers' explicit obligation: the initializer may use its v=0
inverse, whereas the positive-current correction must use the positive Cpair
and coefficient profile, never the v=0 Czero specialization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open ContinuumRow CarrierSobolev AuxiliaryRawBand PhysicalBackground GeometricProfile

/-- Apply the SAME uncut base/full-strain producer to the actual physical
prefix. All field constants and the geometric threshold precede histories,
raw data and the source scale. Raw reserve `r0+1+n` suffices; hence the mean's
`s0=2*(floor(n/2)+2)` leaves room for both `r0=0` and `r0=1`.
The fixed tangent initializer `X0` and original source multiplier are retained
(`app:ch_mean_pairs:eq:mean-coarse-field-profile`, `main:prop:mean`). -/
theorem exists_history_fixedSourceBase_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius)
    (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 R))
    (D : ℕ → ℝ) (hD : ∀ s, 0 ≤ D s)
    {B : ℝ} (hB : 1 ≤ B) {rStar r₀ kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : r₀+3 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent*((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ (raw : AugmentedInput n ι), (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ L : ℝ, currentCoefficientScale R₀ stage ≤ L →
      (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s raw ≤ D s*L^(s-(r₀+1+n))) →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ (baseVariation χsrc raw F X₀) (ball 0 R) ∧
      ∀ s, cNorm (closedBall 0 r) s (baseVariation χsrc raw F X₀) +
        cNorm (closedBall 0 r) s (linearizedMetric F (baseVariation χsrc raw F X₀)) ≤
          C s*L^(s-r₀) := by
  obtain ⟨S, hS, C, hC, hraising⟩ := exists_history_halfTangent_profile
    G hr hrR hR hB hStar (show 2+(r₀+1) ≤ rStar by omega) horder
  obtain ⟨A, hA, hhistory⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) r)
    (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  obtain ⟨E, hE, hbase⟩ := exists_baseVariation_strain_profile (ι := ι)
    (isCompact_closedBall (0 : Euclidean n) r) isOpen_ball (closedBall_subset_ball hrR)
    χsrc hs X₀ hX₀ A C D hA hC hD
  refine ⟨S, hS, E, hE, ?_⟩
  intro R₀ hR₀ stage u ell hu raw hreg L hTL hraw F
  obtain ⟨hi, _, hCp⟩ := hraising R₀ hR₀ stage u ell hu
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hT : 1 ≤ currentCoefficientScale R₀ stage := one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) stage
  have hL : 1 ≤ L := hT.trans hTL
  have hFp : HasDerivativeProfile (closedBall 0 r) F (r₀+2) L A := by
    intro s
    apply (hhistory R₀ (hS.trans hR₀) stage u ell hu _ Subset.rfl s).trans
    apply mul_le_mul_of_nonneg_left _ (hA s)
    exact (pow_le_pow_left₀ (zero_le_one.trans hT) hTL _).trans
      (pow_le_pow_right₀ hL (by omega : s-rStar ≤ s-(r₀+2)))
  have hCr : HasDerivativeProfile (closedBall 0 r) (halfTangentCoefficient F) (r₀+1) L C := by
    intro s
    exact (hCp s).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hT) hTL _) (hC s))
  refine ⟨contDiffOn_baseVariation χsrc hs raw hreg isOpen_ball hF.contDiffOn hX₀ hi, ?_⟩
  exact hbase F hF hi raw hreg r₀ L hL hFp hCr hraw

end JanetCartan.PhysicalMean
