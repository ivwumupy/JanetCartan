module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ActualBootstrap.NormalizedImage
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedRegularity
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedAmplitudes

/-!
# Uniform normalized elliptic bounds with the retained exterior

The coercive normalized row uses an inner exterior cutoff selected after the
measurement geometry. The source cutoff stays fixed independently. Applying the
existing primitive elliptic bootstrap with that supplied exterior preserves the
literal row in the source-to-density inverse of
`app:ch_background:prop:bg-normalized` and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.NormalizedBackground
open ContinuumCommutator ContinuumRow ContinuumRow.CommonMeasurement AmplitudeBound Pseudodifferential
  PeriodicLocalL2

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Uniform primitive elliptic bounds for the literal normalized row, retaining
both its supplied exterior and a varying high-order profile. The low reflected
amplitude budget stays `2*(n+1)+1`; the high profile may depend on the original
nonconstant density. All elliptic constants precede that profile and the source
scale. This applies the existing commutator and first-order inverse producers,
rather than assuming regularity of the inverse
(`app:ch_background:prop:bg-normalized`, `app:ch_background:prop:bg-inverse`).

The concrete wider-density consumer is `CorrectedSourceInverse.hwide`.
`ActualConstruction.exists_finite_seed_source_normal_realizations` supplies
the literal carrier normals and their low/high amplitude bounds on the original
`2*(n+1)+14` density class. Its high density norms must be retained in `aProfile`;
no uniform all-order bound over that finite-low class is asserted here.
The common-row gap comes from the same-family source coercivity construction. -/
theorem exists_normalized_row_elliptic_profile_estimates_with_exterior
    (H : FlatReference n) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hR : 6 * r < 1 / 2)
    {χcoeff : Euclidean n → ℝ} (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hχsupport : tsupport χcoeff ⊆ Metric.ball 0 (5 * r))
    (hχplateau : Metric.closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1})
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ) :
    let hcell : 4 * r < 1 / 2 := by linarith
    let χ := FixedCutoffs.periodic hr hcell 1
    let χsrc := FixedCutoffs.periodic hr hcell 2
    let S := periodicSobolevScale n (Euclidean n)
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∀ (M : ι → ℝ), (∀ i, 0 ≤ M i) →
      ∀ (Q : ℕ → ℝ), (∀ p, 0 ≤ Q p) →
      ∀ (γ : ℝ), 0 < γ →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ a z, c a z = χcoeff (centeredTorusRepresentative z) *
        GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
          (centeredTorusRepresentative z) a) →
      ∀ (aProfile : ℕ → ℝ), (∀ p, 0 ≤ aProfile p) → Monotone aProfile →
      ∀ (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p (Q p * (1 + aProfile p))) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      let A := augmentedRow (imageChannel c χ χsrc)
        (fun i ↦ restrictCarrier χ (V i)) ψ
      let E := CoerciveInverse.normalOperator A
      (∀ v, γ * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v +
              (1 + aProfile (s + 1 + (2 * (n + 1) + 14))) * ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            (S.gradeNorm s e + (1 + aProfile (s + (2 * (n + 1) + 14))) * ‖e‖)) := by
  intro hcell χ χsrc S
  obtain ⟨σ₀, hσ₀, hσ₁, P, _, hP, _, L, _, hL, _, himage⟩ :=
    exists_normalized_image_analytic_bounds H hr hR hχcoeff hχsupport hχplateau
  obtain ⟨D, hD, hrestrict⟩ := exists_restrictAmplitude_derivative_constants
    (FixedCutoffs.physical (n := n) hr 1) (FixedCutoffs.physical hr 1).contDiff
    (FixedCutoffs.physical hr 1).hasCompactSupport
  refine ⟨σ₀, hσ₀, hσ₁, ?_⟩
  intro M hM Q hQ γ hγ
  let M' := fun i ↦ D (2 * (n + 1) + 1) * M i
  let Q' := fun s ↦ D (2 * (n + 1) + (s + 1)) * Q (2 * (n + 1) + (s + 1))
  obtain ⟨C, hC, helliptic⟩ := exists_uniform_augmentedNormal_elliptic_estimates
    hn (4 * r) hcell M' (fun i ↦ mul_nonneg (hD _) (hM i)) hL
    χ χsrc ψ (FixedCutoffs.periodic_smooth hr hcell 1)
    (FixedCutoffs.periodic_smooth hr hcell 2)
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩
    P Q' (fun j ↦ (hP j).le) (fun s ↦ mul_nonneg (hD _) (hQ _)) 14 hγ
  refine ⟨C, hC, ?_⟩
  intro σ hσ c hformula aProfile haProfile hmono b hb hlow hhigh R B hs hB V hV
  obtain ⟨hc, hclow, hchigh, _, _⟩ := (himage σ hσ).2 c hformula
  let b' := fun i ↦ restrictAmplitude (b i) (FixedCutoffs.physical hr 1)
  have hb' i := contDiff_restrictAmplitude (b i) (hb i) _
    (FixedCutoffs.physical hr 1).contDiff
  have hs' i := supportedInCenteredBox_restrictAmplitude_fixedMeasurement (b i) hr
  have hlow' (i : ι) : ∀ l j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b' i ξ z l j) (2 * (n + 1) + 1) (M' i) :=
    hrestrict (b i) (hb i) _ (M i) (hlow i)
  have hhigh' (s : ℕ) (i : ι) : ∀ l j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b' i ξ z l j) (2 * (n + 1) + (s + 1))
      (Q' s * (1 + aProfile (2 * (n + 1) + (s + 1)))) := by
    simpa only [Q', mul_assoc] using
      hrestrict (b i) (hb i) _ _ (hhigh i _ (by omega))
  have hV' (i : ι) := restricted_carrier_normal_eq hn (R i) (4 * r)
    (b i) (hb i) (hs i) (B i) (hB i) χ (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    (FixedCutoffs.periodic_apply hr hcell 1) (hs' i) (M' i)
    (fun l j ξ is his ↦ hlow' i l j ξ is (Nat.le_succ_of_le his)) (V i) (hV i)
  have hclow' : ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
      P j * (1 + aProfile (j + 2)) := by
    intro a j x
    exact (hchigh a j x).trans
      (le_mul_of_one_le_right (hP j).le (by linarith [haProfile (j + 2)]))
  have hbudget : ∀ s i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b' i ξ z l j)
      (2 * (n + 1) + (s + 1))
      (Q' s * (1 + aProfile (s + 1 + (2 * (n + 1) + 14)))) := by
    intro s i l j ξ is his z
    exact (hhigh' s i l j ξ is his z).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (hmono (by omega)))
        (mul_nonneg (hD _) (hQ _)))
  dsimp only
  intro hgap
  simpa only [S, augmentedNormal, CoerciveInverse.normalOperator, add_zero, one_mul] using
    helliptic c hc aProfile haProfile hmono hclow hclow'
      b' hb' hs' hlow' hbudget (fun i ↦ restrictCarrier χ (V i)) hV'
      (CoerciveInverse.normalOperator_gap _ hgap)

/-- The actual normalized geometric image and the supplied reflected carrier
normals give the primitive elliptic estimates for the SAME row with a separately
supplied exterior cutoff (`app:ch_background:prop:bg-normalized`,
`app:ch_background:prop:bg-inverse`). This is the normal-operator signature
consumed by `PositiveBackground.exists_small_uncorrectedDensity_of_normal_estimates_with_exterior`.
The exterior may be the smaller inner cutoff constructed by
`ContinuumNormal.ActualConstruction.exists_initialized_source_family_coercivity`;
no equality with the fixed source cutoff or transfer of its gap is required.
The low amplitude budget remains `2*(n+1)+1`, and the constants precede every
source scale. The literal carrier-normal identities and their uniform amplitude
budgets remain inputs supplied by the normalized normal construction. -/
theorem exists_normalized_row_elliptic_estimates_with_exterior
    (H : FlatReference n) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hR : 6 * r < 1 / 2)
    {χcoeff : Euclidean n → ℝ} (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hχsupport : tsupport χcoeff ⊆ Metric.ball 0 (5 * r))
    (hχplateau : Metric.closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1})
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ) :
    let hcell : 4 * r < 1 / 2 := by linarith
    let χ := FixedCutoffs.periodic hr hcell 1
    let χsrc := FixedCutoffs.periodic hr hcell 2
    let S := periodicSobolevScale n (Euclidean n)
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∀ (M : ι → ℝ), (∀ i, 0 ≤ M i) →
      ∀ (Q : ℕ → ℝ), (∀ p, 0 ≤ Q p) →
      ∀ (γ : ℝ), 0 < γ →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ a z, c a z = χcoeff (centeredTorusRepresentative z) *
        GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
          (centeredTorusRepresentative z) a) →
      ∀ (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))),
      (∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
        (2 * (n + 1) + 1) (M i)) →
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p (Q p)) →
      ∀ (R B : ι → ℝ)
        (hs : ∀ i ξ l j, SupportedInCenteredBox (R i) (fun z ↦ b i ξ z l j))
        (hB : ∀ i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j)
          (2 * (n + 1)) (B i))
        (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn (R i) (b i) (hb i) (hs i) (B i) (hB i)))) →
      let A := augmentedRow (imageChannel c χ χsrc)
        (fun i ↦ restrictCarrier χ (V i)) ψ
      let E := CoerciveInverse.normalOperator A
      (∀ v, γ * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v + ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            (S.gradeNorm s e + ‖e‖)) := by
  intro hcell χ χsrc S
  obtain ⟨σ₀, hσ₀, hσ₁, hfamily⟩ :=
    exists_normalized_row_elliptic_profile_estimates_with_exterior (ι := ι)
      H hn hr hR hχcoeff hχsupport hχplateau ψ hψ
  refine ⟨σ₀, hσ₀, hσ₁, ?_⟩
  intro M hM Q hQ γ hγ
  obtain ⟨C, hC, hbounds⟩ := hfamily M hM Q hQ γ hγ
  refine ⟨C, hC, ?_⟩
  intro σ hσ c hformula b hb hlow hhigh R B hs hB V hV
  have hbudget : ∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
      HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
        (Q p * (1 + (fun _ : ℕ ↦ (0 : ℝ)) p)) := by
    simpa only [add_zero, mul_one] using hhigh
  simpa only [S, add_zero, one_mul] using
    hbounds σ hσ c hformula (fun _ ↦ 0) (fun _ ↦ le_rfl) monotone_const
      b hb hlow hbudget R B hs hB V hV

end JanetCartan.NormalizedBackground
