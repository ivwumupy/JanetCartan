module

public import JanetCartan.Iteration.PhysicalMean.LinearProfiles
public import JanetCartan.Iteration.PhysicalNormalInverse.Regularity

/-!
# Physical-history producers for the original uncut linear profiles

The image coefficients are the literal localized reduced coefficients of the
same physical Schwartz prefix, not a periodic history. Their reserve-two
geometric estimate and the physical map profile supply every image-factor and
exterior jet required by the actual uncut auxiliary estimate. The full source
reserve costs three map derivatives: two for the geometry and one in the
uncut image factor. No density or inverse profile is inferred from this fact.
The paired current-inverse/raw bound retains its exact positive-density
producer and is the explicit remaining input to the auxiliary source profile.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean ContinuumRow GeometricProfile
open ContinuumCommutator.ImageChannel.Differential

/-- The actual physical prefix supplies every primitive coefficient jet for
`exists_uncutAuxiliary_source_profile`. All constants precede the history,
array, source, sampled row, and fixed input cutoff. The fixed coefficient
cutoff, source/measurement masks, and exterior channel are unchanged
(`app:ch_background:eq:bg-frame-tame`, `app:ch_mean_pairs:eq:block-normal`). -/
theorem exists_history_auxiliary_source_coefficients {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) (hcell : r < 1/2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ ball 0 r)
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin s₀ : ℕ} (hStar : 8 ≤ rStar)
    (hreserve : s₀+3 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent*((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Ccoef : ℕ → ℝ, (∀ s, 0 ≤ Ccoef s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ a z, c a z = χ (AmplitudeBound.centeredTorusRepresentative z) *
        geometricReducedCoefficients (RevisedGlobal.finiteMap G.map u)
          (AmplitudeBound.centeredTorusRepresentative z) a) →
      (∀ a, IsSmoothPeriodic (c a)) ∧
      (∀ s a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤
          Ccoef s*currentCoefficientScale R₀ stage^(s-s₀)) ∧
      (∀ s j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤
          Ccoef s*currentCoefficientScale R₀ stage^(s-s₀)) := by
  obtain ⟨P, hP, S, hS, hcoeff⟩ :=
    PhysicalNormalInverse.exists_prescribed_history_image_coefficient_profiles
      G hr hrR hR hcell hχ hχs hB hStar horder
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) R) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  let D := fun s ↦ ∑ j ∈ Finset.range (s+2), P j*(1+A (j+2))
  have hD (s : ℕ) : 0 ≤ D s :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hP j).le (by linarith [hA (j+2)])
  let ext : C(Torus n, ℝ) := 1-ψ
  have hext : IsSmoothPeriodic (ext : Torus n → ℝ) :=
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩
  let L := fun m ↦ cNorm (fundamentalCell n) m (periodicLift χmeas) +
    cNorm (fundamentalCell n) m (periodicLift χsrc) +
    cNorm (fundamentalCell n) m (periodicLift ext)
  have hL (m : ℕ) : 0 ≤ L m :=
    add_nonneg (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  have hfixed (m j : ℕ) (hjm : j ≤ m) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j (periodicLift χmeas) x‖ ≤ L m ∧
      ‖iteratedFDeriv ℝ j (periodicLift χsrc) x‖ ≤ L m ∧
      ‖iteratedFDeriv ℝ j (periodicLift ext) x‖ ≤ L m := by
    refine ⟨(hm.norm_iteratedFDeriv_le_cNorm hjm x).trans ?_,
      (hs.norm_iteratedFDeriv_le_cNorm hjm x).trans ?_,
      (hext.norm_iteratedFDeriv_le_cNorm hjm x).trans ?_⟩ <;>
      dsimp only [L] <;> linarith [cNorm_nonneg (fundamentalCell n) m (periodicLift χmeas),
        cNorm_nonneg (fundamentalCell n) m (periodicLift χsrc),
        cNorm_nonneg (fundamentalCell n) m (periodicLift ext)]
  refine ⟨S, hS, fun s ↦ D s+L (s+1), fun s ↦ add_nonneg (hD s) (hL (s+1)), ?_⟩
  intro R₀ hR₀ stage u ell hu c hformula
  obtain ⟨hc, hjets⟩ := hcoeff R₀ hR₀ stage u ell hu c hformula
  have htwo := hS.trans hR₀
  have hT : 1 ≤ currentCoefficientScale R₀ stage :=
    one_le_currentCoefficientScale (by linarith) stage
  have hF := hprofile R₀ htwo stage u ell hu (closedBall (0 : Euclidean n) R) Subset.rfl
  have hcBound (s : ℕ) (a : ReducedCoefficientIndex n) (j : ℕ) (hj : j ≤ s+1)
      (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        D s*currentCoefficientScale R₀ stage^(s-s₀) := by
    have hPj : 0 ≤ P j*(1+A (j+2)) := mul_nonneg (hP j).le (by linarith [hA (j+2)])
    have hbudget : P j*(1+A (j+2)) ≤ D s :=
      Finset.single_le_sum (f := fun k ↦ P k*(1+A (k+2)))
        (fun k _ ↦ mul_nonneg (hP k).le (by linarith [hA (k+2)]))
        (show j ∈ Finset.range (s+2) by simp only [Finset.mem_range]; omega)
    have hp : 1 ≤ currentCoefficientScale R₀ stage^(j+2-rStar) := one_le_pow₀ hT
    calc
      _ ≤ P j*(1+cNorm (closedBall (0 : Euclidean n) R) (j+2)
          (RevisedGlobal.finiteMap G.map u)) := hjets j a x
      _ ≤ P j*(1+A (j+2)*currentCoefficientScale R₀ stage^(j+2-rStar)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (hF (j+2))) (hP j).le
      _ ≤ P j*((1+A (j+2))*currentCoefficientScale R₀ stage^(j+2-rStar)) := by
        apply mul_le_mul_of_nonneg_left _ (hP j).le
        nlinarith
      _ = (P j*(1+A (j+2)))*currentCoefficientScale R₀ stage^(j+2-rStar) := by ring
      _ ≤ (P j*(1+A (j+2)))*currentCoefficientScale R₀ stage^(s-s₀) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) hPj
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (pow_nonneg (zero_le_one.trans hT) _)
  have hfixedBudget (s : ℕ) : L (s+1) ≤
      (D s+L (s+1))*currentCoefficientScale R₀ stage^(s-s₀) :=
    (le_add_of_nonneg_left (hD s)).trans
      (le_mul_of_one_le_right (add_nonneg (hD s) (hL (s+1))) (one_le_pow₀ hT))
  refine ⟨hc, ?_, ?_⟩
  · intro s
    rintro (a | b) j hj x
    · exact (hcBound s a j hj x).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (hL (s+1))) (pow_nonneg (zero_le_one.trans hT) _))
    · cases b
      · exact (hfixed (s+1) j hj x).1.trans (hfixedBudget s)
      · exact (hfixed (s+1) j hj x).2.1.trans (hfixedBudget s)
  · intro s j hj x
    exact (hfixed (s+1) j hj x).2.2.trans (hfixedBudget s)

/-- Apply the actual physical coefficient producer and the actual uncut
auxiliary tame theorem to the SAME current inverse. Both auxiliary channels
are retained. The remaining paired estimate is exactly the current-normal
inverse/raw output and its positive-density reserve, not a linear-response
profile (`app:ch_mean_pairs:eq:block-normal`, `new:eq:source-bound`). -/
theorem exists_history_uncutAuxiliary_source_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) (hcell : r < 1/2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ ball 0 r)
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin s₀ : ℕ} (hStar : 8 ≤ rStar)
    (hreserve : s₀+3 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent*((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ))
    (Craw : ℕ → ℝ) (hCraw : ∀ s, 0 ≤ Craw s) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ CE : ℕ → ℝ, (∀ s, 0 ≤ CE s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ (c : ReducedCoefficientIndex n → C(Torus n, ℝ)) (hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ a z, c a z = χ (AmplitudeBound.centeredTorusRepresentative z) *
        geometricReducedCoefficients (RevisedGlobal.finiteMap G.map u)
          (AmplitudeBound.centeredTorusRepresentative z) a) →
      ∀ (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
        (hreg : ∀ (e : SmoothResidual n) (j : ℕ),
          (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
            (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ι j),
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q₀ w) +
          (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s
            ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (Q₀ w)) ≤
        Craw s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          currentCoefficientScale R₀ stage^(s-s₀)*‖w‖)) →
      ∀ (e : SmoothResidual n) (s : ℕ),
        residualSobolevSeminorm n s
          (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) ≤
        CE s*(residualSobolevSeminorm n s e +
          currentCoefficientScale R₀ stage^(s-s₀)*‖smoothResidualToL2 n e‖) := by
  obtain ⟨S, hS, Ccoef, hCcoef, hcoeff⟩ := exists_history_auxiliary_source_coefficients
    G hr hrR hR hcell χ hχ hχs χmeas χsrc ψ hm hs hψ hB hStar hreserve horder
  obtain ⟨CE, hCE, haux⟩ := exists_uncutAuxiliary_source_profile (n := n) (ι := ι)
    (hCcoef 0) Craw Ccoef hCraw hCcoef s₀
  refine ⟨S, hS, CE, hCE, ?_⟩
  intro R₀ hR₀ stage u ell hu c hc hformula U Q₀ hreg hpair e s
  obtain ⟨_, hhigh, hext⟩ := hcoeff R₀ hR₀ stage u ell hu c hformula
  have hlow : ∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
      (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ Ccoef 0 := by
    simpa only [Nat.zero_add, Nat.zero_sub, pow_zero, mul_one] using hhigh 0
  have hextLow : ∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
      (periodicLift ((1-ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ Ccoef 0 := by
    simpa only [Nat.zero_add, Nat.zero_sub, pow_zero, mul_one] using hext 0
  exact haux (currentCoefficientScale R₀ stage)
    (one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) stage)
    c hc χmeas χsrc ψ hm hs hψ hlow hhigh hextLow hext U Q₀ hreg hpair e s

end JanetCartan.PhysicalMean
