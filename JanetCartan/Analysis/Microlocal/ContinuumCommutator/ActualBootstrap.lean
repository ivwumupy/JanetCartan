module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedRegularity
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedProfiles
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ActualBootstrap.NormalizedRow

/-!
# Bootstrap on the retained row's common measurement chart

Apply the actual history image budget, the reserve-fourteen reflected-amplitude
budget and the common measurement restriction to the existing elliptic theorem.
The normal is literally the initialized row's image, restricted carriers and
exterior. No regularity or elliptic estimate is assumed.

Two construction obligations remain explicit: `both-commutator-budget` must
supply the order `2*(n+1)+1` baseline on this same retained selection, and
`both-normal-coercivity` must supply its positive normal gap. The former is
the common-family application of `exists_retained_history_reflected_baselines`;
it cannot be obtained by spending one additional initial-scalar derivative in
the reserve-fourteen high estimate. The other primitive inputs are the outputs
of `ContinuumRow.exists_initialized_retained_continuum_row`.

Consumers: `ContinuumInverse`, `PositiveBackground.SourceInverse` and
`app:ch_background:prop:bg-inverse`. This is a checked assembly from those
precise producer outputs, not the unconditional initialized construction.
Its reference and source scale are fixed arguments; its constants must not be
treated as uniform over a separately varying normalized source scale.

`NormalizedImage` separately instantiates the actual geometric coefficient
producer on a fixed cutoff, proving image-normal translation and auxiliary
adjoint bounds before every scale in one interval. `NormalizedRow` applies
those image inputs to the same-row elliptic bootstrap with uniform carrier
budgets and gap still explicit. These stronger quantifiers do not construct
the missing normalized carrier family or its common coercivity.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator
open ContinuumRow ContinuumRow.CommonMeasurement AmplitudeBound Pseudodifferential
  PeriodicLocalL2

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
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (3 + (n : ℝ) / 2) + 2 < kMin)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean N) (ell : Fin stage → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm Kimage (j + 2) (finiteHistoryMap G u))) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) (finiteHistoryMap G u) +
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
      let H := retainedCoefficientProfile K Kimage Kin (finiteHistoryMap G u) initial
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
    G hG Kimage hKimage P hP horder
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
    (retainedCoefficientProfile_nonneg K Kimage Kin (finiteHistoryMap G u) initial)
    (retainedCoefficientProfile_monotone K Kimage Kin (finiteHistoryMap G u) initial)
    hi.1 (hi.2 K Kin initial) b' hb' hs' hlow'
    (hhigh K Kimage Kin (finiteHistoryMap G u) initial b hb hbudget)
    (fun i ↦ restrictCarrier (FixedCutoffs.periodic hr hcell 1) (V i))
  intro i
  exact restricted_carrier_normal_eq hn (R i) (4 * r) (b i) (hb i) (hs i) (B i) (hB i)
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    (FixedCutoffs.periodic_apply hr hcell 1) (hs' i) (M' i)
    (fun l j ξ is his ↦ hlow' i l j ξ is (Nat.le_succ_of_le his)) (V i) (hV i)


/-- The actual common cutoff and history image estimates supply `hreg` and
`hstep` for the SAME retained normal, with fixed shift `2*(n+1)+14`
(`app:ch_background:eq:bg-commutator`, `app:ch_background:eq:bg-r-inverse`).
All constants precede the finite history, initial scalars, amplitudes and row.
The original low baseline and positive gap remain the two named construction
obligations above; no inverse or total commutator estimate is a premise. -/
theorem exists_retained_history_elliptic_estimates
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K Kimage : Set (Euclidean n)) (hKimage : IsCompact Kimage)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (Cpdo : ι → ℕ → ℝ) (hCpdo : ∀ i p, 0 ≤ Cpdo i p)
    (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (3 + (n : ℝ) / 2) + 2 < kMin)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean N) (ell : Fin stage → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm Kimage (j + 2) (finiteHistoryMap G u))) →
      ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) (finiteHistoryMap G u) +
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
        (fun i ↦ restrictCarrier χ (V i)) (FixedCutoffs.periodic hr hcell 0)
      let S := periodicSobolevScale n (Euclidean n)
      let H := retainedCoefficientProfile K Kimage Kin (finiteHistoryMap G u) initial
      (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v +
              (1 + H (s + 1 + (2 * (n + 1) + 14))) * ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            (S.gradeNorm s e + (1 + H (s + (2 * (n + 1) + 14))) * ‖e‖)) := by
  exact exists_retained_history_elliptic_estimates_with_exterior hn hr hcell
    (FixedCutoffs.periodic hr hcell 0) (FixedCutoffs.periodic_smooth hr hcell 0)
    G hG K Kimage hKimage Kin P hP Cpdo hCpdo M hM horder hγ

end JanetCartan.ContinuumCommutator
