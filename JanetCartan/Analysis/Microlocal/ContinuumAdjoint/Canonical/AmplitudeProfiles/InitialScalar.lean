module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Interpolation
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Profiles of the original initial scalar

The function is literally `extendedInitialScalar`, with its fixed bump supported
inside the original `R / 8` norm domain. The only varying inputs are the original
scalar, its local smoothness and its low/high norms on that same closed ball.
Smoothness on `R / 4` is the input retained in
`CanonicalCarrier.exists_canonical_nullAmplitude_bounds`; the low norm is part
of the parent's fixed finite-low class, and the high norm is included in its
common immersion/initial budget. No flow or composite profile is assumed.

Consumers: `hscalar` and `A₀` in
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers.ConstructedCarrierJets
open FullPhaseCharts.InverseEstimates

variable {n : ℕ}

/-- Complex smoothness for the literal scalar input `hscalar` of the adjoint
endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_complex_contDiff (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8))) :
    ContDiff ℝ ∞ (fun p ↦ (extendedInitialScalar z₀ hR initial p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (extendedInitialScalar_contDiff z₀ hR initial hi)

/-- The relabeled initial bump has fixed compact support, before the original
scalar varies (`app:ch_background:prop:bg-adjoint`). -/
theorem initialScalarCutoff_hasCompactSupport (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (initialScalar (n := n) (initialBump z₀ hR)) := by
  let L : CarrierVariable n →L[ℝ] Euclidean (n - 1) × Euclidean 3 :=
    (ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean (n - 1))).prod
      (CanonicalCarrier.parameter.comp
        (ContinuousLinearMap.fst ℝ CarrierParameter (Euclidean (n - 1))))
  have hinj : Function.Injective L := by
    intro p q hpq
    have hfst : p.1 = q.1 := by
      apply (TransportKernel.sliceCoordinates 2).symm.injective
      rw [← CanonicalCarrier.parameter_eq_sliceCoordinates_symm]
      exact congrArg Prod.snd hpq
    exact Prod.ext hfst (congrArg Prod.fst hpq)
  exact (initialBump (n := n) z₀ hR).hasCompactSupport.comp_isClosedEmbedding
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj))

/-- Every extended initial scalar is supported in the SAME fixed relabeled
bump, used to globalize its interpolated jets
(`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_tsupport_subset (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    tsupport (extendedInitialScalar z₀ hR initial) ⊆
      tsupport (initialScalar (n := n) (initialBump z₀ hR)) :=
  tsupport_mul_subset_left

/-- Compact support of the exact real initial extension; no regularity outside
its original initial ball is required (`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_hasCompactSupport (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    HasCompactSupport (extendedInitialScalar z₀ hR initial) :=
  (initialScalarCutoff_hasCompactSupport z₀ hR).of_isClosed_subset isClosed_closure
    (extendedInitialScalar_tsupport_subset z₀ hR initial)

/-- Compact support is preserved by the complex inclusion used in the raw
adjoint endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_complex_hasCompactSupport (z₀ : Euclidean 3)
    {R : ℝ} (hR : 0 < R) (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    HasCompactSupport (fun p ↦ (extendedInitialScalar z₀ hR initial p : ℂ)) :=
  (extendedInitialScalar_hasCompactSupport z₀ hR initial).comp_left Complex.ofReal_zero

/-- Fixed cutoff and relabeling cost no derivatives. All constants precede the
original scalar, which is measured only on its original `R / 8` closed ball.
Consumer: the two interpolation endpoints for the initial-scalar profile in
`app:ch_background:prop:bg-adjoint`, `app:ch_waves:eq:joint-tame`. -/
theorem exists_cNorm_extendedInitialScalar_le (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    {L : Set (CarrierVariable n)} (hL : IsCompact L) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
        ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
        ∀ m, cNorm L m (extendedInitialScalar z₀ hR initial) ≤
          C m * cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) m initial := by
  let p₀ := ((0 : Euclidean (n - 1)), z₀)
  let K := closedBall p₀ (R / 8)
  let O := ball p₀ (R / 4)
  let χ := initialBump (n := n) z₀ hR
  let ψ := fun p : CarrierVariable n ↦ (p.2, CanonicalCarrier.parameter p.1)
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_snd.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_fst)
  have hKO : K ⊆ O := closedBall_subset_ball (by linarith)
  let B := fun m ↦ (∑ j ∈ Finset.range (m + 1),
    ‖(ContinuousLinearMap.mul ℝ ℝ)‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm K m χ
  have hB (m) : 0 ≤ B m := mul_nonneg (Finset.sum_nonneg
    (fun _ _ ↦ mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ))
      (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))))
    (cNorm_nonneg ..)
  choose E hE he using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound (G := ℝ)
    hL (fun p _ ↦ hψ.contDiffAt (x := p)) m
  refine ⟨fun m ↦ E m * (1 + B m), fun m ↦ mul_pos (hE m) (by linarith [hB m]), ?_⟩
  intro initial hi m
  let f := fun q ↦ χ q * initial q
  have hsmall : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)) :=
    hi.mono (ball_subset_ball (by linarith))
  have hf : ContDiff ℝ ∞ f :=
    Localization.contDiff_of_contDiffOn_support_neighborhood isOpen_ball
      (χ.contDiff.contDiffOn.mul hsmall)
      (tsupport_mul_subset_left.trans (initialBump_tsupport_subset z₀ hR))
  have hloc : cNorm K m f ≤ B m * cNorm K m initial :=
    cNorm_bilinear_le_on (ContinuousLinearMap.mul ℝ ℝ) (isCompact_closedBall ..)
      isOpen_ball hKO χ.contDiff.contDiffOn hi m
  have hb : ∀ j ≤ m, ∀ q, ‖iteratedFDeriv ℝ j f q‖ ≤ B m * cNorm K m initial := by
    intro j hj q
    by_cases hq : q ∈ K
    · exact (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall ..)
        (hf.of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hq hj).trans hloc
    · have hz : iteratedFDeriv ℝ j f q = 0 := by
        by_contra hn
        exact hq (ball_subset_closedBall
          (initialBump_tsupport_subset z₀ hR
            (tsupport_mul_subset_left (support_iteratedFDeriv_subset j hn))))
      rw [hz, norm_zero]
      exact mul_nonneg (hB m) (cNorm_nonneg ..)
  have hh := he m f (B m * cNorm K m initial)
    (mul_nonneg (hB m) (cNorm_nonneg ..))
    (fun _ _ ↦ hf.contDiffAt.of_le (by simp)) (fun j hj p _ ↦ hb j hj (ψ p))
  exact hh.trans (by
    dsimp only
    nlinarith [mul_nonneg (hE m).le (cNorm_nonneg K m initial)])

/-- Global complex jets of the exact initial extension, with the natural
truncated exponent required by `A₀` in the raw adjoint endpoint. The reserve
`2*(n+1)` is independent of `s`, and `s = 0` is included. Every larger common
high budget is accepted, allowing the parent to add the immersion high norm.
The only analytic inputs are local smoothness and the original scalar's fixed
low norm (`app:ch_background:prop:bg-adjoint`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_extendedInitialScalar_profile (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (M : ℝ) (s : ℕ) :
    ∃ A₀ : ℕ → ℝ, (∀ i, 0 ≤ A₀ i) ∧
      ∀ (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
        ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
        cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (2*(n+1)) initial ≤ M →
        ∀ H : ℝ,
          1 + cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
            (s+2*(n+1)) initial ≤ H →
          ∀ p : CarrierVariable n, ∀ i ≤ s+2*(n+1),
            ‖iteratedFDeriv ℝ i (fun q ↦ (extendedInitialScalar z₀ hR initial q : ℂ)) p‖ ≤
              A₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  obtain ⟨ρ, hρ, hsupp⟩ :=
    (initialScalarCutoff_hasCompactSupport (n := n) z₀ hR).isBounded.subset_closedBall_lt
      0 (0 : CarrierVariable n)
  let J := closedBall (0 : CarrierVariable n) ρ
  obtain ⟨C, hC, hc⟩ := exists_cNorm_extendedInitialScalar_le z₀ hR (isCompact_closedBall (0 : CarrierVariable n) ρ)
  let b := 2*(n+1)
  obtain ⟨A₀, hA₀, ha⟩ := exists_closedBall_reserve_profile (F := ℝ)
    (0 : CarrierVariable n) hρ b s (C b * M) (C (b+s))
  refine ⟨A₀, hA₀, ?_⟩
  intro initial hi hlow H hhigh p i hi'
  have hf := extendedInitialScalar_contDiff z₀ hR initial
    (hi.mono (ball_subset_ball (by linarith)))
  have hH : 1 ≤ H := by
    linarith [cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
      (s+2*(n+1)) initial]
  have hlo : cNorm J b (extendedInitialScalar z₀ hR initial) ≤ C b * M :=
    (hc initial hi b).trans (mul_le_mul_of_nonneg_left hlow (hC b).le)
  have hhi : cNorm J (b+s) (extendedInitialScalar z₀ hR initial) ≤ C (b+s) * H := by
    apply (hc initial hi (b+s)).trans
    apply mul_le_mul_of_nonneg_left _ (hC (b+s)).le
    simpa only [b, Nat.add_comm] using (le_trans (le_add_of_nonneg_left zero_le_one) hhigh)
  change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ extendedInitialScalar z₀ hR initial) p‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  by_cases hp : p ∈ J
  · exact ha _ hf hlo H hH hhi i (by dsimp [b]; omega) p hp
  · have hz : iteratedFDeriv ℝ i (extendedInitialScalar z₀ hR initial) p = 0 := by
      by_contra hn
      exact hp (hsupp ((extendedInitialScalar_tsupport_subset z₀ hR initial)
        (support_iteratedFDeriv_subset i hn)))
    rw [hz, norm_zero]
    exact mul_nonneg (hA₀ i) (Real.rpow_nonneg (zero_le_one.trans hH) _)

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
