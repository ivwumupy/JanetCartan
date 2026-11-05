module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Adjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CoerciveNormal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ActualBootstrap
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedRow.Estimates

/-!
# One retained inverse, its full raw adjoint and both densities

Compose the actual common-measurement bootstrap with the existing finite
raw-adjoint producer and the fixed density multipliers. The image and carrier
norm domains are retained separately in one additive coefficient profile.
No operator, normal, inverse or cutoff is reselected by Sobolev order.

The input local raw bounds and kernel identities are the checked outputs of
`ContinuumRow.exists_initialized_retained_continuum_row`. The image jets use
that same producer; the C8 neighborhood and smoothness are derived from the
admissible history. Only the uniform reflected first-derivative baseline on the SAME
selection and the SAME normal's positive gap still need the common-family
applications owned by `both-commutator-budget` and `both-normal-coercivity`.
This theorem performs the analytic assembly once those inputs are available;
it does not assert their unconditional geometric construction.

The reference `G`, radius and primitive constants are fixed arguments here.
Applying this result separately at each normalized source scale does not give
the uniform-in-`σ` constants required by `PositiveBackground.SourceInverse`.
That application needs one common radius, gap and carrier/adjoint budgets
before all `σ ∈ (0, σ₀]`, from the normalized-family construction.

Consumers: `PositiveBackground.SourceInverse`, `AuxiliaryRealization`,
`PreparedHistory`, `CanonicalChange`, `Current`, and
`app:ch_background:prop:bg-inverse` / `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.ContinuumInverse
open ContinuumRow ContinuumRow.CommonMeasurement ContinuumCommutator
  ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
  CarrierSobolev AmplitudeBound Pseudodifferential
  PeriodicLocalL2

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Compare the raw-adjoint producer's compact union with the separate image
and carrier domains in `app:ch_background:eq:bg-r-inverse`, without assuming
that either domain contains the other. -/
private theorem cNorm_union_le_add_of_smooth
    {K K' : Set (Euclidean n)} (hK : IsCompact K) (hK' : IsCompact K')
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F) (m : ℕ) :
    cNorm (K ∪ K') m F ≤ cNorm K m F + cNorm K' m F := by
  unfold cNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  apply Real.sSup_le _ (add_nonneg (sSup_norm_iteratedFDeriv_nonneg K j F)
    (sSup_norm_iteratedFDeriv_nonneg K' j F))
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · exact (le_csSup (bddAbove_norm_iteratedFDeriv hK (hF.of_le (by simp)) (le_refl j))
      (mem_image_of_mem _ hx)).trans
        (le_add_of_nonneg_right (sSup_norm_iteratedFDeriv_nonneg K' j F))
  · exact (le_csSup (bddAbove_norm_iteratedFDeriv hK' (hF.of_le (by simp)) (le_refl j))
      (mem_image_of_mem _ hx)).trans
        (le_add_of_nonneg_left (sSup_norm_iteratedFDeriv_nonneg K j F))

/-- Retain the supplied coercivity exterior and its actual plateau while
instantiating the full augmented raw estimate and the fixed density
multiplier on the SAME history inverse (`app:ch_background:eq:bg-r-inverse`,
`app:ch_background:eq:bg-density-adjoint`). The raw shift is `2*(n+1)+14`,
and density increases it exactly once to `2*(n+1)+15`. Constants precede
histories, positive initial scalars and source data. The local raw estimates
are the initialized row's proved outputs, not assumptions about its inverse.
The remaining low-baseline and coercivity applications are named above. -/
theorem exists_retained_history_inverse_estimates_with_exterior
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ)
    (core : Set (Torus n)) (hcore : ∀ x ∈ core, ψ x = 1)
    (G : FlatReference n)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    {δ : ℝ} (hδ : 0 < δ)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (Cpdo Craw : ι → ℕ → ℝ)
    (hCpdo : ∀ i p, 0 ≤ Cpdo i p) (hCraw : ∀ i s, 0 ≤ Craw i s)
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    {rMask angle : ι → ℝ} (hrMask : ∀ i, 0 < rMask i) (hangle : ∀ i, 0 < angle i)
    (χinitial : ι → ContDiffBump (0 : CarrierVariable n)) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C D : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ (∀ s, 0 ≤ D s) ∧
      ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm (Metric.closedBall 0 (6 * r)) (j + 2) F)) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) F + cNorm (Kin i) (p + 14) (initial i)))) →
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (d : ι → CarrierData n (embeddingDimension n))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      (∀ i w, (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
      (∀ i s, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s ((V i).adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
        rawSobolevNorm s ((V i).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
          Craw i s * (‖w‖ + (1 + cNorm K (s + 2 * (n + 1) + 14) F +
            cNorm (Kin i) (s + 2 * (n + 1) + 14) (initial i)) *
            ‖PeriodicSobolevSpace.toL2 s w‖)) →
      let χ := FixedCutoffs.periodic hr hcell 1
      let A := augmentedRow (imageChannel c χ (FixedCutoffs.periodic hr hcell 2))
        (fun i ↦ restrictCarrier χ (V i)) ψ
      let E := CoerciveInverse.normalOperator A
      let S := periodicSobolevScale n (Euclidean n)
      let X := augmentedInputSobolevScale n ι
      let H := retainedCoefficientProfile K (Metric.closedBall 0 (6 * r)) Kin F initial
      (∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2) →
        (∀ e, A (CoerciveInverse.rightInverse A e) = e ∧
          ‖E.inverse e‖ ≤ γ⁻¹ * ‖e‖ ∧
          ∀ᵐ x ∂volume, x ∈ core →
            (CoerciveInverse.rightInverse A e).snd x = 0) ∧
        (∀ s e, e ∈ S.level s →
          E.inverse e ∈ S.level s ∧ CoerciveInverse.rightInverse A e ∈ X.level s ∧
          S.gradeNorm s (E.inverse e) + X.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
            C s * (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖)) ∧
        (∀ s e, e ∈ S.level (s + 1) →
          let raw := CoerciveInverse.rightInverse A e
          ∃ hu : ∀ i, MemRawSobolev 1 (raw.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z₀ i) (θ₀ i) (hrMask i) (hangle i) (raw.fst.snd i) (hu i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z₀ i) (θ₀ i) (hrMask i) (hangle i) (χinitial i)
                (raw.fst.snd i) (hu i)))) ∧
            densityUncutFamilySize z₀ θ₀ hrMask hangle s raw ≤
              D s * (S.gradeNorm (s + 1) e + (1 + H (s + (2 * (n + 1) + 15))) * ‖e‖) ∧
            densityFamilySize z₀ θ₀ hrMask hangle χinitial s raw ≤
              D s * (S.gradeNorm (s + 1) e + (1 + H (s + (2 * (n + 1) + 15))) * ‖e‖)) := by
  classical
  let Kimage := Metric.closedBall (0 : Euclidean n) (6 * r)
  have horder3 : displacementLoss n + bandExponent * (3 + (n : ℝ) / 2) + 2 < kMin := by
    have hband : (0 : ℝ) ≤ bandExponent := by norm_num [bandExponent]
    refine lt_of_le_of_lt ?_ horder
    gcongr
    norm_num
  obtain ⟨Cstep, hCstep, T, hT, helliptic⟩ := exists_retained_history_elliptic_estimates_with_exterior
    hn hr hcell ψ hψ G.map G.contDiff K Kimage (isCompact_closedBall ..) Kin
    P hP Cpdo hCpdo M hM horder3 hγ
  obtain ⟨Tnear, hTnear, hnearHistory⟩ :=
    HistoryGeometry.exists_initialScale_for_c8_neighborhood G.map (6 * r) horder hδ
  obtain ⟨Craw', hCraw', hadjoint⟩ := exists_measured_retained_augmented_bounds
    G hK (6 * r) Kin hδ.le
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    ψ
    (FixedCutoffs.periodic_smooth hr hcell 1) (FixedCutoffs.periodic_smooth hr hcell 2)
    hψ P hP Craw hCraw
  obtain ⟨L, hL, hdensity⟩ := exists_densityFamily_gradeNorm_bounds
    z₀ θ₀ hrMask hangle χinitial
  let C := fun s ↦ bootstrapConstant γ Cstep s +
    Craw' s * (bootstrapConstant γ Cstep s + γ⁻¹)
  have hC (s) : 0 ≤ C s := by
    exact add_nonneg (bootstrapConstant_nonneg hγ hCstep s)
      (mul_nonneg (hCraw' s) (add_nonneg (bootstrapConstant_nonneg hγ hCstep s)
        (inv_nonneg.mpr hγ.le)))
  refine ⟨C, fun s ↦ L s * C (s + 1), hC,
    fun s ↦ mul_nonneg (hL s) (hC (s + 1)), max T Tnear,
    hT.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ stage u ell hu F c hc hcjet initial b hb hhigh hlow
    R B hs hB d V hV hrep hraw χ A E S X H hgap
  have hF := hu.contDiff_finiteHistoryMap G.contDiff
  have hnear := hnearHistory R₀ ((le_max_right _ _).trans hR₀) stage u ell hu
  have hnormal := CoerciveInverse.normalOperator_gap A hgap
  obtain ⟨_, _, hinv⟩ := helliptic R₀ ((le_max_left _ _).trans hR₀) stage u ell hu c hc hcjet initial b hb
    hhigh hlow R B hs hB V hV hnormal
  have hrawActual := hadjoint F hF hnear c hc hcjet initial d V hrep hraw
  have hrawBound (s : ℕ) (w : OutputL2 n) (hw : w ∈ S.level s) :
      A.adjoint w ∈ X.level s ∧ X.gradeNorm s (A.adjoint w) ≤
        Craw' s * (S.gradeNorm s w + (1 + H (s + (2 * (n + 1) + 14))) * ‖w‖) := by
    obtain ⟨hm, hbnd⟩ := hrawActual s w hw
    refine ⟨hm, hbnd.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (hCraw' s)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    have hdom := cNorm_union_le_add_of_smooth hK (isCompact_closedBall 0 (6 * r)) hF
      (s + (2 * (n + 1) + 14))
    dsimp only [H, retainedCoefficientProfile]
    simp only [Nat.add_assoc] at hdom ⊢
    linarith
  have hfull (s : ℕ) (e : OutputL2 n) (he : e ∈ S.level s) :
      E.inverse e ∈ S.level s ∧ CoerciveInverse.rightInverse A e ∈ X.level s ∧
      S.gradeNorm s (E.inverse e) + X.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
        C s * (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖) := by
    have hi := hinv s e he
    refine ⟨hi.1, (hrawBound s _ hi.1).1, ?_⟩
    exact inverse_add_rightInverse_gradeNorm_le S X A hγ hgap (hCraw' s)
      (add_nonneg zero_le_one (retainedCoefficientProfile_nonneg K Kimage Kin F initial _))
      hi.1 hi.2 (fun w hw ↦ (hrawBound s w hw).2)
  refine ⟨fun e ↦ ⟨CoerciveInverse.apply_rightInverse A hγ hgap e,
    CoerciveInverse.norm_inverse_apply_le E hγ hnormal e,
    ?_⟩, hfull, ?_⟩
  · rw [CoerciveNormal.rightInverse_exterior_eq]
    exact exteriorChannel_zero_on_core ψ core hcore _
  · intro s e he raw
    have hi := hfull (s + 1) e he
    obtain ⟨hraw₁, hmem, huncut, hcut⟩ := hdensity s raw hi.2.1
    have hnorm : X.gradeNorm (s + 1) raw ≤ C (s + 1) *
        (S.gradeNorm (s + 1) e + (1 + H (s + (2 * (n + 1) + 15))) * ‖e‖) := by
      have hnrm := (le_add_of_nonneg_left (S.gradeNorm_nonneg (s + 1) (E.inverse e))).trans hi.2.2
      simpa only [show s + 1 + (2 * (n + 1) + 14) = s + (2 * (n + 1) + 15) by omega]
        using hnrm
    have hden := mul_le_mul_of_nonneg_left hnorm (hL s)
    refine ⟨hraw₁, hmem, huncut.trans ?_, hcut.trans ?_⟩ <;>
      simpa only [mul_assoc] using hden

/-- Instantiate the full augmented raw estimate and the fixed density
multiplier on the SAME history inverse (`app:ch_background:eq:bg-r-inverse`,
`app:ch_background:eq:bg-density-adjoint`). The raw shift is `2*(n+1)+14`,
and density increases it exactly once to `2*(n+1)+15`. Constants precede
histories, positive initial scalars and source data. The local raw estimates
are the initialized row's proved outputs, not assumptions about its inverse.
The remaining low-baseline and coercivity applications are named above. -/
theorem exists_retained_history_inverse_estimates
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (G : FlatReference n)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    {δ : ℝ} (hδ : 0 < δ)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (Cpdo Craw : ι → ℕ → ℝ)
    (hCpdo : ∀ i p, 0 ≤ Cpdo i p) (hCraw : ∀ i s, 0 ≤ Craw i s)
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    {rMask angle : ι → ℝ} (hrMask : ∀ i, 0 < rMask i) (hangle : ∀ i, 0 < angle i)
    (χinitial : ι → ContDiffBump (0 : CarrierVariable n)) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C D : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ (∀ s, 0 ≤ D s) ∧
      ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm (Metric.closedBall 0 (6 * r)) (j + 2) F)) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) F + cNorm (Kin i) (p + 14) (initial i)))) →
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (d : ι → CarrierData n (embeddingDimension n))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      (∀ i w, (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
      (∀ i s, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s ((V i).adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
        rawSobolevNorm s ((V i).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
          Craw i s * (‖w‖ + (1 + cNorm K (s + 2 * (n + 1) + 14) F +
            cNorm (Kin i) (s + 2 * (n + 1) + 14) (initial i)) *
            ‖PeriodicSobolevSpace.toL2 s w‖)) →
      let χ := FixedCutoffs.periodic hr hcell 1
      let A := augmentedRow (imageChannel c χ (FixedCutoffs.periodic hr hcell 2))
        (fun i ↦ restrictCarrier χ (V i)) (FixedCutoffs.periodic hr hcell 0)
      let E := CoerciveInverse.normalOperator A
      let S := periodicSobolevScale n (Euclidean n)
      let X := augmentedInputSobolevScale n ι
      let H := retainedCoefficientProfile K (Metric.closedBall 0 (6 * r)) Kin F initial
      (∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2) →
        (∀ e, A (CoerciveInverse.rightInverse A e) = e ∧
          ‖E.inverse e‖ ≤ γ⁻¹ * ‖e‖ ∧
          ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ Metric.closedBall 0 r →
            (CoerciveInverse.rightInverse A e).snd x = 0) ∧
        (∀ s e, e ∈ S.level s →
          E.inverse e ∈ S.level s ∧ CoerciveInverse.rightInverse A e ∈ X.level s ∧
          S.gradeNorm s (E.inverse e) + X.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
            C s * (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖)) ∧
        (∀ s e, e ∈ S.level (s + 1) →
          let raw := CoerciveInverse.rightInverse A e
          ∃ hu : ∀ i, MemRawSobolev 1 (raw.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z₀ i) (θ₀ i) (hrMask i) (hangle i) (raw.fst.snd i) (hu i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z₀ i) (θ₀ i) (hrMask i) (hangle i) (χinitial i)
                (raw.fst.snd i) (hu i)))) ∧
            densityUncutFamilySize z₀ θ₀ hrMask hangle s raw ≤
              D s * (S.gradeNorm (s + 1) e + (1 + H (s + (2 * (n + 1) + 15))) * ‖e‖) ∧
            densityFamilySize z₀ θ₀ hrMask hangle χinitial s raw ≤
              D s * (S.gradeNorm (s + 1) e + (1 + H (s + (2 * (n + 1) + 15))) * ‖e‖)) := by
  apply exists_retained_history_inverse_estimates_with_exterior hn hr hcell
    (FixedCutoffs.periodic hr hcell 0) (FixedCutoffs.periodic_smooth hr hcell 0)
    {x | centeredTorusRepresentative x ∈ Metric.closedBall 0 r} ?_
    G K hK Kin hδ P hP Cpdo Craw hCpdo hCraw M hM z₀ θ₀ hrMask hangle χinitial horder hγ
  intro x hx
  change centeredTorusRepresentative x ∈ {y | FixedCutoffs.physical hr 0 y = 1}
  apply interior_subset
  apply FixedCutoffs.physical_plateau hr 0
  simpa only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul, Set.mem_ofPred_eq] using hx

end JanetCartan.ContinuumInverse
