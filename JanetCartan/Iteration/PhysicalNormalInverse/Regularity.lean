module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalSource
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ActualBootstrap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.PrescribedImage
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.SourceHistoryGeometry

/-!
# Actual image and elliptic inputs for physical current normals

For `app:ch_background:prop:bg-inverse` and `app:ch_background:eq:bg-commutator`,
apply the arbitrary-coefficient elliptic theorem to the exact localized image
coefficients of a physical Schwartz prefix.  The coefficient cutoff, carrier
normal, common measurement and exterior are preserved.  The physical history
proves the low image budget and every map neighborhood; no inverse regularity
or elliptic estimate is assumed.

The carrier amplitude/normal inputs have the actual original leading producer
used in `PhysicalNormalInverse.exists_capped_source_history_inverse_from_original_leading`.
These physical adapters alone do not assert that its original leading fields
have already been instantiated by the parent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.PhysicalNormalInverse
open ContinuumInverse ContinuumCommutator ContinuumRow ContinuumRow.CommonMeasurement
open ContinuumRow.ImageGeometry ContinuumRow.ImageGeometry.Periodization
open GeometricProfile AmplitudeBound Pseudodifferential PeriodicLocalL2
open ProjectedStressFrame CanonicalCarrier

private theorem fixed_low_bound {n N : ℕ} (r : ℕ)
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hr : r ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
        cNorm K r (RevisedGlobal.finiteMap G u) ≤ cNorm K r G + 1 := by
  obtain ⟨T, hT, hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := N) hBband horder (by norm_num : (0 : ℝ) < 1)
  refine ⟨T, hT, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hclose := (cNorm_mono_order hr).trans_lt (hnear R₀ hR₀ K G hK j u ell hu)
  have hF : ContDiff ℝ r (RevisedGlobal.finiteMap G u) :=
    (hG.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))).of_le (by simp)
  have hGr : ContDiff ℝ r G := hG.of_le (by simp)
  calc
    _ = cNorm K r ((RevisedGlobal.finiteMap G u - G) + G) := by rw [sub_add_cancel]
    _ ≤ cNorm K r (RevisedGlobal.finiteMap G u - G) + cNorm K r G :=
      cNorm_add_le hK (hF.sub hGr) hGr
    _ ≤ _ := by linarith

/-- The literal image array of every admissible history has reserve-two jet
bounds on the supplied initialized coefficient cutoff. The constants precede
all histories and arrays. Equality of the geometric formula transfers both
smoothness and every derivative estimate to the already constructed array
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-frame-tame`,
`app:ch_background:eq:bg-commutator`, `main:eq:displacement-budget`). -/
theorem exists_prescribed_history_image_coefficient_profiles
    {n : ℕ} (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (hcell : r < 1 / 2)
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ ball 0 r) {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ P : ℕ → ℝ, (∀ m, 0 < P m) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ coeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, coeff j x = χ (AmplitudeBound.centeredTorusRepresentative x) *
          geometricReducedCoefficients F (AmplitudeBound.centeredTorusRepresentative x) j) →
        (∀ j, IsSmoothPeriodic (coeff j)) ∧
        ∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (coeff j)) x‖ ≤
          P m * (1 + cNorm (closedBall (0 : Euclidean n) R) (m + 2) F) := by
  obtain ⟨δ, hδ, _B, _hB, C, hC, hcoeff⟩ :=
    exists_reference_reduced_coefficient_estimates G hr hrR hR
  obtain ⟨T, hT, hnear⟩ :=
    PhysicalGeometry.exists_initialScale_for_c8_neighborhood G.map R hBband hStar horder hδ
  refine ⟨fun m ↦ cutoffDerivativeBound χ r m * C m,
    fun m ↦ mul_pos (cutoffDerivativeBound_pos χ r m) (hC m), T, hT, ?_⟩
  intro R₀ hR₀ stage u ell hu F coeff hformula
  obtain ⟨hreg, _hlow, hjets⟩ := hcoeff F
    (G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))) (hnear R₀ hR₀ stage u ell hu)
  let selected := periodicReducedCoefficients hrR hcell hχ hs
    (geometricReducedCoefficients F) hreg
  have heq : coeff = selected := by
    funext j
    apply ContinuousMap.ext
    intro x
    exact (hformula j x).trans
      (periodicReducedCoefficients_apply hrR hcell hχ hs
        (geometricReducedCoefficients F) hreg j x).symm
  rw [heq]
  refine ⟨fun j ↦ isSmoothPeriodic_cutCoefficient hrR hcell hχ hs hreg j, ?_⟩
  intro m j x
  exact (norm_iteratedFDeriv_periodicReducedCoefficients_le hrR hcell hχ hs
    (geometricReducedCoefficients F) hreg m j x).trans
      ((mul_le_mul_of_nonneg_left (hjets m) (cutoffDerivativeBound_pos χ r m).le).trans_eq
        (mul_assoc _ _ _).symm)


section ImageLow
variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Close the image's fixed C¹ budget from an actual admissible history, and
put every high image derivative into the same retained profile. The image
arrays are the SAME arrays from `Initialized`/`HistoryImage`; their reserve-two
jet theorem is used directly. Thresholds and the low constant precede all
histories and positive initial scalars (`app:ch_background:eq:bg-commutator`,
`main:eq:displacement-budget`). -/
theorem exists_history_imageCoefficient_profile_bounds
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (Kimage : Set (Euclidean n)) (hKimage : IsCompact Kimage)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ L T : ℝ, 0 ≤ L ∧ 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin stage → ℕ),
      RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm Kimage (j + 2) (RevisedGlobal.finiteMap G u))) →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ L) ∧
      ∀ (K : Set (Euclidean n))
        (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
        (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ),
        ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
          P j * (1 + retainedCoefficientProfile K Kimage Kin
            (RevisedGlobal.finiteMap G u) initial (j + 2)) := by
  obtain ⟨T, hT, hhistory⟩ := fixed_low_bound
    3 G hG Kimage hKimage hBband (by omega : 3 ≤ rStar) horder
  let L := (P 0 + P 1) * (2 + cNorm Kimage 3 G)
  refine ⟨L, T, mul_nonneg (add_nonneg (hP 0) (hP 1))
    (add_nonneg (by norm_num) (cNorm_nonneg ..)), hT, ?_⟩
  intro R₀ hR₀ stage u ell hu c hc
  have hlow := hhistory R₀ hR₀ stage u ell hu
  refine ⟨?_, ?_⟩
  · intro a j hj x
    have hjP : P j ≤ P 0 + P 1 := by
      interval_cases j <;> linarith [hP 0, hP 1]
    have hjF : cNorm Kimage (j + 2) (RevisedGlobal.finiteMap G u) ≤ cNorm Kimage 3 G + 1 :=
      (cNorm_mono_order (by omega : j + 2 ≤ 3)).trans hlow
    exact (hc j a x).trans (mul_le_mul hjP (by linarith)
      (add_nonneg zero_le_one (cNorm_nonneg ..)) (add_nonneg (hP 0) (hP 1)))
  · intro K Kin initial a j x
    exact (hc j a x).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (image_profile_le_retainedCoefficientProfile
        K Kimage Kin (RevisedGlobal.finiteMap G u) initial (j + 2))) (hP j))

end ImageLow

section Elliptic
variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Retain the supplied smooth exterior from the actual coercivity constructor.
The common measurement cutoff and history image estimates supply `hreg` and
`hstep` for the SAME retained normal, with fixed shift `2*(n+1)+14`
(`app:ch_background:eq:bg-commutator`, `app:ch_background:eq:bg-r-inverse`).
All constants precede the finite history, initial scalars, amplitudes and row.
The original low baseline and positive gap remain the two named construction
obligations above; no inverse or total commutator estimate is a premise. -/
theorem exists_retained_history_elliptic_estimates_with_exterior
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ)
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K Kimage : Set (Euclidean n)) (hKimage : IsCompact Kimage)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (Cpdo : ι → ℕ → ℝ) (hCpdo : ∀ i p, 0 ≤ Cpdo i p)
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i) {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin stage → ℕ),
      RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm Kimage (j + 2) (RevisedGlobal.finiteMap G u))) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) (RevisedGlobal.finiteMap G u) +
            cNorm (Kin i) (p + 14) (initial i)))) →
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      let χ := FixedCutoffs.periodic hr hcell 1
      let E := augmentedNormal (imageChannel c χ (FixedCutoffs.periodic hr hcell 2))
        (fun i ↦ restrictCarrier χ (V i)) ψ
      let S := periodicSobolevScale n (Euclidean n)
      let H := retainedCoefficientProfile K Kimage Kin (RevisedGlobal.finiteMap G u) initial
      (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v +
              (1 + H (s + 1 + (2 * (n + 1) + 14))) * ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖)) := by
  obtain ⟨L, T, hL, hT, himage⟩ := exists_history_imageCoefficient_profile_bounds (ι := ι)
    G hG Kimage hKimage P hP hBband hStar horder
  obtain ⟨D, hD, hrestrict⟩ := exists_restrictAmplitude_derivative_constants
    (FixedCutoffs.physical (n := n) hr 1) (FixedCutoffs.physical hr 1).contDiff
    (FixedCutoffs.physical hr 1).hasCompactSupport
  obtain ⟨Q, hQ, hhigh⟩ := exists_fixedMeasurement_retained_high_bounds hr Cpdo hCpdo
  let M' := fun i ↦ D (2 * (n + 1) + 1) * M i
  obtain ⟨C, hC, helliptic⟩ := exists_uniform_augmentedNormal_elliptic_estimates
    hn (4 * r) hcell M' (fun i ↦ mul_nonneg (hD _) (hM i)) hL
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2)
    ψ
    (FixedCutoffs.periodic_smooth hr hcell 1) (FixedCutoffs.periodic_smooth hr hcell 2)
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩ P Q hP hQ 14 hγ
  refine ⟨C, hC, T, hT, ?_⟩
  intro R₀ hR₀ stage u ell hu c hc hcjet initial b hb hbudget hlow R B hs hB V hV
  have hi := himage R₀ hR₀ stage u ell hu c hcjet
  let b' := fun i ↦ restrictAmplitude (b i) (FixedCutoffs.physical hr 1)
  have hb' i := contDiff_restrictAmplitude (b i) (hb i) _
    (FixedCutoffs.physical hr 1).contDiff
  have hs' i := supportedInCenteredBox_restrictAmplitude_fixedMeasurement (b i) hr
  have hlow' (i : ι) : ∀ l j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b' i ξ z l j) (2 * (n + 1) + 1) (M' i) :=
    hrestrict (b i) (hb i) _ (M i) (hlow i)
  apply helliptic c hc _
    (retainedCoefficientProfile_nonneg K Kimage Kin (RevisedGlobal.finiteMap G u) initial)
    (retainedCoefficientProfile_monotone K Kimage Kin (RevisedGlobal.finiteMap G u) initial)
    hi.1 (hi.2 K Kin initial) b' hb' hs' hlow'
    (hhigh K Kimage Kin (RevisedGlobal.finiteMap G u) initial b hb hbudget)
    (fun i ↦ restrictCarrier (FixedCutoffs.periodic hr hcell 1) (V i))
  intro i
  exact restricted_carrier_normal_eq hn (R i) (4 * r) (b i) (hb i) (hs i) (B i) (hB i)
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    (FixedCutoffs.periodic_apply hr hcell 1) (hs' i) (M' i)
    (fun l j ξ is his ↦ hlow' i l j ξ is (Nat.le_succ_of_le his)) (V i) (hV i)

end Elliptic

/-- The prescribed geometric image and the supplied retained carrier profiles
give the same-row regularity, one-step elliptic estimate and tame inverse.
Image smoothness and derivative bounds are proved from the literal history,
with no new cutoff or coefficient hypothesis. The original high shift remains
`2*(n+1)+14`. The carrier profiles, normal identity and gap have the concrete
producers described above; this conditional deduction is not the unconditional
embedding theorem (`app:ch_background:eq:bg-commutator`,
`app:ch_background:eq:bg-r-inverse`, `main:eq:displacement-budget`). -/
theorem exists_prescribed_history_elliptic_estimates_with_exterior
    {n : ℕ} {ι : Type*} [Fintype ι] (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ)
    (G : FlatReference n) (K : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    {rCoeff Rimage : ℝ} (hrCoeff : 0 < rCoeff) (hCoeffImage : rCoeff < Rimage)
    (hRimage : Rimage < G.domain.chartRadius) (hCoeffCell : rCoeff < 1 / 2)
    {χcoeff : Euclidean n → ℝ} (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hχsupport : tsupport χcoeff ⊆ Metric.ball 0 rCoeff)
    (Cpdo : ι → ℕ → ℝ) (hCpdo : ∀ i p, 0 ≤ Cpdo i p)
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i) {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, c j x = χcoeff (centeredTorusRepresentative x) *
          GeometricProfile.geometricReducedCoefficients (RevisedGlobal.finiteMap G.map u)
            (centeredTorusRepresentative x) j) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) (RevisedGlobal.finiteMap G.map u) +
            cNorm (Kin i) (p + 14) (initial i)))) →
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      let χ := FixedCutoffs.periodic hr hcell 1
      let E := augmentedNormal (imageChannel c χ (FixedCutoffs.periodic hr hcell 2))
        (fun i ↦ restrictCarrier χ (V i)) ψ
      let S := periodicSobolevScale n (Euclidean n)
      let H := retainedCoefficientProfile K (Metric.closedBall (0 : Euclidean n) Rimage)
        Kin (RevisedGlobal.finiteMap G.map u) initial
      (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v +
              (1 + H (s + 1 + (2 * (n + 1) + 14))) * ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ bootstrapConstant γ C s *
            (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖)) := by
  obtain ⟨P, hP, Timage, hTimage, himage⟩ :=
    exists_prescribed_history_image_coefficient_profiles G hrCoeff hCoeffImage hRimage
      hCoeffCell hχcoeff hχsupport hBband hStar horder
  obtain ⟨C, hC, Telliptic, hTelliptic, helliptic⟩ :=
    exists_retained_history_elliptic_estimates_with_exterior hn hr hcell ψ hψ
      G.map G.contDiff K (Metric.closedBall (0 : Euclidean n) Rimage)
      (isCompact_closedBall _ _) Kin P (fun m ↦ (hP m).le) Cpdo hCpdo M hM hBband hStar horder hγ
  refine ⟨C, hC, max Timage Telliptic, hTimage.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ stage u ell hu c hformula
  obtain ⟨hcsmooth, hcjets⟩ := himage R₀ ((le_max_left _ _).trans hR₀)
    stage u ell hu c hformula
  exact helliptic R₀ ((le_max_right _ _).trans hR₀) stage u ell hu c hcsmooth hcjets

/-- The original source contraction fixes the small cube-frame tolerance before
all physical budgets and histories.  The actual Schwartz prefix then supplies
the full carrier low norm, separate geometric gaps, and image C8 neighborhood.
Consumer: the current inverse built from the original full leading fields. -/
theorem exists_source_history_row_geometry {n : ℕ} (H : FlatReference n)
    {b R : ℝ} (hb : 0 < b) (hbR : b < R) (hR : R < H.domain.chartRadius)
    {δframe : ℝ} (hδframe : 0 < δframe) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap,
      ∀ {Bband : ℝ}, 1 ≤ Bband → ∀ {rStar kMin : ℕ},
        canonicalCarrierLowOrder n ≤ rStar →
        RevisedScales.displacementLoss n +
          bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∀ {δimage : ℝ}, 0 < δimage →
      ∃ κ > (0 : ℝ), ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
        ∀ (stage : ℕ)
          (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap (sourceDilation H.map σ) u
        ContDiff ℝ ∞ F ∧ IsImmersionOn F (ball 0 R) ∧
        HasFullNormalRankOn F (ball 0 R) ∧
        cNorm (closedBall 0 b) (canonicalCarrierLowOrder n) F ≤
          cNorm (closedBall 0 b) (canonicalCarrierLowOrder n)
            (sourceDilation H.map σ) + 1 ∧
        (∀ x ∈ closedBall 0 b, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ closedBall 0 b, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        cNorm (closedBall 0 b) 6 (projectedStress F - fun _ ↦ cubeStress n) < δframe ∧
        ∀ a : ℝ, cNorm (closedBall 0 (6 * a)) 8
          (F - sourceDilation H.map σ) < δimage := by
  obtain ⟨_U, _hU, _hKU, cap₀, hcap₀, hcap₀one, _hsegments, _hsource, hbounds⟩ :=
    exists_projectedStress_dilation_bounds H (isCompact_closedBall (0 : Euclidean n) b)
  obtain ⟨C, hC, hbound⟩ := hbounds 6
  let cap := min cap₀ (δframe / (56 * C))
  have hcap : 0 < cap := lt_min hcap₀ (div_pos hδframe (by positivity))
  have hcapone : cap ≤ 1 := (min_le_left _ _).trans hcap₀one
  refine ⟨cap, hcap, hcapone, ?_⟩
  intro σ hσ Bband hBband rStar kMin hStar horder δimage hδimage
  let G := sourceDilationReference H hσ.1 (hσ.2.trans hcapone)
  have h8 : 8 ≤ rStar := by unfold canonicalCarrierLowOrder at hStar; omega
  have hreference (i : Fin n) :
      cNorm (closedBall (0 : Euclidean n) b) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < (δframe / 14) / 2 := by
    have hsmall : C * σ ≤ δframe / 56 := by
      have hσsmall : σ ≤ δframe / (56 * C) := hσ.2.trans (min_le_right _ _)
      have hmul := (le_div_iff₀ (show 0 < 56 * C by positivity)).mp hσsmall
      nlinarith
    exact (hbound σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ i).trans_lt
      (hsmall.trans_lt (by linarith))
  obtain ⟨Sg, hSg, _C₀, _hC₀, κ, hκ, hgeom⟩ :=
    PhysicalGeometry.exists_cube_frame_neighborhood G hb hbR hR hBband h8 horder
      (div_pos hδframe (by norm_num)) hreference
  obtain ⟨Sm, _hSm, hmap⟩ := fixed_low_bound (canonicalCarrierLowOrder n)
    G.map G.contDiff (closedBall 0 b) (isCompact_closedBall _ _) hBband hStar horder
  obtain ⟨Si, _hSi, hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := embeddingDimension n) hBband horder hδimage
  refine ⟨κ, hκ, max Sg (max Sm Si), hSg.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ stage u ell hu F
  have hRg := (le_max_left Sg (max Sm Si)).trans hR₀
  have hRm := ((le_max_left Sm Si).trans (le_max_right Sg (max Sm Si))).trans hR₀
  have hRi := ((le_max_right Sm Si).trans (le_max_right Sg (max Sm Si))).trans hR₀
  obtain ⟨hi, hrank, _hlow, hmet, hnormal, hframe, hcomponents⟩ := hgeom R₀ hRg stage u ell hu
  have hF : ContDiff ℝ ∞ F :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hBU : closedBall (0 : Euclidean n) b ⊆ ball 0 R := closedBall_subset_ball hbR
  have hframeSmooth : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    contDiffOn_pi.mpr hframe
  refine ⟨hF, hi, hrank, hmap R₀ hRm stage u ell hu,
    fun x hx ↦ hmet x (hBU hx), fun x hx ↦ hnormal x (hBU hx), ?_, ?_⟩
  · apply ActualCarriers.CurrentFullPhase.frame_cNorm_lt_of_componentwise
      (isCompact_closedBall _ _)
      (fun x hx ↦ ((hframeSmooth.contDiffAt (isOpen_ball.mem_nhds (hBU hx))).sub
        contDiffAt_const).of_le (by simp)) hδframe
    simpa only [F, G, sourceDilationReference_map, Pi.sub_apply, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      show (2 : ℝ) * (6 + 1) = 14 by norm_num] using hcomponents
  · intro a
    exact ((cNorm_mono_order h8).trans_lt
      (hnear R₀ hRi (closedBall 0 (6 * a)) G.map (isCompact_closedBall _ _) stage u ell hu)).trans
        (half_lt_self hδimage)

/-- `app:ch_background:eq:bg-r-inverse`: on the uncorrected current row, the
initial amplitude is the fixed constant σ.  Thus the physical prefix supplies
the single high coefficient profile with baseline `rStar - Bcan`, not a new
loss at every Sobolev order.  Every constant precedes the physical history. -/
theorem exists_uncorrected_physical_coefficient_profile
    {n : ℕ} {ι : Type*} [Fintype ι] (G : FlatReference n) (b Rimage : ℝ)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3)) (σ : ℝ)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ}
    (hStar : canonicalCarrierLowOrder n ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∀ R₀, 2 ≤ R₀ →
      ∀ stage (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ s,
        1 + retainedCoefficientProfile (closedBall 0 b) (closedBall 0 Rimage) Kin
          (RevisedGlobal.finiteMap G.map u) (fun _ _ ↦ σ) (s + canonicalCarrierLowOrder n) ≤
        C s * (currentCoefficientScale R₀ stage) ^ (s - (rStar - canonicalCarrierLowOrder n)) := by
  classical
  obtain ⟨A, hA, hfirst⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) b)
    (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  obtain ⟨B, hB, hsecond⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) Rimage)
    (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  let D := fun s ↦ ∑ i, cNorm (Kin i) (s + canonicalCarrierLowOrder n) (fun _ ↦ σ)
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun _ _ ↦ cNorm_nonneg ..
  let C := fun s ↦ 1 + A (s + canonicalCarrierLowOrder n) +
    B (s + canonicalCarrierLowOrder n) + D s
  refine ⟨C, fun s ↦ add_nonneg (add_nonneg (add_nonneg zero_le_one (hA _)) (hB _)) (hD s), ?_⟩
  intro R₀ hR₀ stage u ell hu s
  let T := currentCoefficientScale R₀ stage
  have hT : 1 ≤ T := one_le_currentCoefficientScale (by linarith) stage
  have hpow : 1 ≤ T ^ (s - (rStar - canonicalCarrierLowOrder n)) := one_le_pow₀ hT
  have hexp : s + canonicalCarrierLowOrder n - rStar ≤
      s - (rStar - canonicalCarrierLowOrder n) := by omega
  have hpowle := pow_le_pow_right₀ hT hexp
  have hfirst' := (hfirst R₀ hR₀ stage u ell hu _ Subset.rfl (s + canonicalCarrierLowOrder n)).trans
    (mul_le_mul_of_nonneg_left hpowle (hA _))
  have hsecond' := (hsecond R₀ hR₀ stage u ell hu _ Subset.rfl (s + canonicalCarrierLowOrder n)).trans
    (mul_le_mul_of_nonneg_left hpowle (hB _))
  have hD' := le_mul_of_one_le_right (hD s) hpow
  change 1 + (cNorm (closedBall 0 b) (s + canonicalCarrierLowOrder n) _ +
    cNorm (closedBall 0 Rimage) (s + canonicalCarrierLowOrder n) _ + D s) ≤ _
  calc
    _ ≤ T ^ (s - (rStar - canonicalCarrierLowOrder n)) +
        (A (s + canonicalCarrierLowOrder n) * T ^ (s - (rStar - canonicalCarrierLowOrder n)) +
         B (s + canonicalCarrierLowOrder n) * T ^ (s - (rStar - canonicalCarrierLowOrder n)) +
         D s * T ^ (s - (rStar - canonicalCarrierLowOrder n))) :=
      add_le_add hpow (add_le_add (add_le_add hfirst' hsecond') hD')
    _ = _ := by dsimp only [C, T]; ring

/-- `app:ch_background:prop:bg-current`: if the ACTUAL current positive initial
amplitude has baseline `s0+Bcan`, then the physical current map and that SAME
amplitude have the exact one-high coefficient profile required by the corrected
normal inverse with baseline `s0`.  The initial profile is the positive-density
producer's output, not an inverse estimate.  All constants precede histories. -/
theorem exists_positive_physical_coefficient_profile
    {n : ℕ} {ι : Type*} [Fintype ι] (G : FlatReference n) (b Rimage : ℝ)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3)) (s0 : ℕ)
    (Cinitial : ι → ℕ → ℝ) (hCinitial : ∀ i m, 0 ≤ Cinitial i m)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ}
    (hStar : s0 + canonicalCarrierLowOrder n ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∀ R₀, 2 ≤ R₀ →
      ∀ stage (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
        (∀ i, HasDerivativeProfile (Kin i) (initial i) (s0 + canonicalCarrierLowOrder n)
          (currentCoefficientScale R₀ stage) (Cinitial i)) →
      ∀ s,
        1 + retainedCoefficientProfile (closedBall 0 b) (closedBall 0 Rimage) Kin
          (RevisedGlobal.finiteMap G.map u) initial (s + canonicalCarrierLowOrder n) ≤
        C s * (currentCoefficientScale R₀ stage) ^ (s - s0) := by
  classical
  obtain ⟨A, hA, hfirst⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) b)
    (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  obtain ⟨B, hB, hsecond⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (G := G.map) (isCompact_closedBall (0 : Euclidean n) Rimage)
    (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  let D := fun s ↦ ∑ i, Cinitial i (s + canonicalCarrierLowOrder n)
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun i _ ↦ hCinitial i _
  let C := fun s ↦ 1 + A (s + canonicalCarrierLowOrder n) +
    B (s + canonicalCarrierLowOrder n) + D s
  refine ⟨C, fun s ↦ add_nonneg (add_nonneg (add_nonneg zero_le_one (hA _)) (hB _)) (hD s), ?_⟩
  intro R₀ hR₀ stage u ell hu initial hinitial s
  let T := currentCoefficientScale R₀ stage
  have hT : 1 ≤ T := one_le_currentCoefficientScale (by linarith) stage
  have hpow : 1 ≤ T ^ (s - s0) := one_le_pow₀ hT
  have hexp : s + canonicalCarrierLowOrder n - rStar ≤ s - s0 := by omega
  have hpowle := pow_le_pow_right₀ hT hexp
  have hfirst' := (hfirst R₀ hR₀ stage u ell hu _ Subset.rfl (s + canonicalCarrierLowOrder n)).trans
    (mul_le_mul_of_nonneg_left hpowle (hA _))
  have hsecond' := (hsecond R₀ hR₀ stage u ell hu _ Subset.rfl (s + canonicalCarrierLowOrder n)).trans
    (mul_le_mul_of_nonneg_left hpowle (hB _))
  have hD' : (∑ i, cNorm (Kin i) (s + canonicalCarrierLowOrder n) (initial i)) ≤ D s * T ^ (s - s0) := by
    dsimp only [D]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    simpa only [Nat.add_sub_add_right] using hinitial i (s + canonicalCarrierLowOrder n)
  change 1 + (cNorm (closedBall 0 b) (s + canonicalCarrierLowOrder n) _ +
    cNorm (closedBall 0 Rimage) (s + canonicalCarrierLowOrder n) _ + _) ≤ _
  calc
    _ ≤ T ^ (s - s0) + (A (s + canonicalCarrierLowOrder n) * T ^ (s - s0) +
        B (s + canonicalCarrierLowOrder n) * T ^ (s - s0) + D s * T ^ (s - s0)) :=
      add_le_add hpow (add_le_add (add_le_add hfirst' hsecond') hD')
    _ = _ := by dsimp only [C, T]; ring


end JanetCartan.PhysicalNormalInverse
