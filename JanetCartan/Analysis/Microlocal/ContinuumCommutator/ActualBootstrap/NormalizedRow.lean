module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ActualBootstrap.NormalizedImage
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedRegularity
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedAmplitudes

/-!
# Elliptic assembly uniform over the normalized source interval

Instantiate the image inputs using the literal normalized geometric
coefficients on one supplied fixed cutoff. Restrict the SAME carrier operators
and their reflected normal amplitudes to that measurement chart. The existing
translation, difference-quotient and negative-order uniqueness argument then
gives `hreg`, `hstep` and all-order bounds for each row's original L² inverse.
One sequence of constants precedes every source scale in the fixed interval.

This is the uniform analytic deduction consumed by
`PositiveBackground.SourceInverse` for `app:ch_background:prop:bg-normalized`.
The normalized-family construction (`both-normal-coercivity` together with
`both-positive-background` and `both-commutator-budget`) must still supply the
fixed row cutoff, literal carrier realizations, uniform carrier low/high
budgets and positive gap. They are not consequences of separate fixed-scale
existence theorems, and no such quantifier interchange is used here.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator
open ContinuumRow ContinuumRow.CommonMeasurement AmplitudeBound Pseudodifferential
  PeriodicLocalL2

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The actual normalized image supplies all image hypotheses of the
elliptic bootstrap, uniformly BEFORE the varying scale. Its same-row carrier
inputs remain explicit producer obligations
(`app:ch_background:eq:bg-uniform-normalized`,
`app:ch_background:prop:bg-inverse`). The low amplitude order is still
`2*(n+1)+1`; it is kept separate from the all-order normalized seed budgets.
The supplied uncut carriers are restricted by the original common mask on
both physical positions, with their literal real normal and factor four. -/
theorem exists_normalized_row_elliptic_estimates
    (H : FlatReference n) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hR : 6 * r < 1 / 2)
    {χcoeff : Euclidean n → ℝ} (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hχsupport : tsupport χcoeff ⊆ Metric.ball 0 (5 * r))
    (hχplateau : Metric.closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1}) :
    let hcell : 4 * r < 1 / 2 := by linarith
    let χ := FixedCutoffs.periodic hr hcell 1
    let χsrc := FixedCutoffs.periodic hr hcell 2
    let ψ := FixedCutoffs.periodic hr hcell 0
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
      let E := augmentedNormal (imageChannel c χ χsrc)
        (fun i ↦ restrictCarrier χ (V i)) ψ
      (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ s v, v ∈ S.level s → E v ∈ S.level (s + 1) → v ∈ S.level (s + 1)) ∧
        (∀ s v, v ∈ S.level (s + 1) → E v ∈ S.level (s + 1) →
          S.gradeNorm (s + 1) v ≤ C (s + 1) *
            (S.gradeNorm (s + 1) (E v) + S.gradeNorm s v + ‖v‖)) ∧
        (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
          S.gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            (S.gradeNorm s e + ‖e‖)) := by
  intro hcell χ χsrc ψ S
  obtain ⟨σ₀, hσ₀, hσ₁, P, _, hP, _, L, _, hL, _, himage⟩ :=
    exists_normalized_image_analytic_bounds H hr hR hχcoeff hχsupport hχplateau
  obtain ⟨D, hD, hrestrict⟩ := exists_restrictAmplitude_derivative_constants
    (FixedCutoffs.physical (n := n) hr 1) (FixedCutoffs.physical hr 1).contDiff
    (FixedCutoffs.physical hr 1).hasCompactSupport
  refine ⟨σ₀, hσ₀, hσ₁, ?_⟩
  intro M hM Q hQ γ hγ
  let M' := fun i ↦ D (2 * (n + 1) + 1) * M i
  let Q' := fun s ↦ D (2 * (n + 1) + (s + 1)) * Q (2 * (n + 1) + (s + 1))
  have hψ := FixedCutoffs.periodic_smooth (n := n) hr hcell 0
  obtain ⟨C, hC, helliptic⟩ := exists_uniform_augmentedNormal_elliptic_estimates
    hn (4 * r) hcell M' (fun i ↦ mul_nonneg (hD _) (hM i)) hL
    χ χsrc ψ (FixedCutoffs.periodic_smooth hr hcell 1)
    (FixedCutoffs.periodic_smooth hr hcell 2)
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩
    P Q' (fun j ↦ (hP j).le) (fun s ↦ mul_nonneg (hD _) (hQ _)) 14 hγ
  refine ⟨C, hC, ?_⟩
  intro σ hσ c hformula b hb hlow hhigh R B hs hB V hV
  obtain ⟨hc, hclow, hchigh, _, _⟩ := (himage σ hσ).2 c hformula
  let b' := fun i ↦ restrictAmplitude (b i) (FixedCutoffs.physical hr 1)
  have hb' i := contDiff_restrictAmplitude (b i) (hb i) _
    (FixedCutoffs.physical hr 1).contDiff
  have hs' i := supportedInCenteredBox_restrictAmplitude_fixedMeasurement (b i) hr
  have hlow' (i : ι) : ∀ l j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b' i ξ z l j) (2 * (n + 1) + 1) (M' i) :=
    hrestrict (b i) (hb i) _ (M i) (hlow i)
  have hhigh' (s : ℕ) (i : ι) : ∀ l j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b' i ξ z l j) (2 * (n + 1) + (s + 1)) (Q' s) :=
    hrestrict (b i) (hb i) _ _ (hhigh i _ (by omega))
  have hV' (i : ι) := restricted_carrier_normal_eq hn (R i) (4 * r)
    (b i) (hb i) (hs i) (B i) (hB i) χ (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    (FixedCutoffs.periodic_apply hr hcell 1) (hs' i) (M' i)
    (fun l j ξ is his ↦ hlow' i l j ξ is (Nat.le_succ_of_le his)) (V i) (hV i)
  have hclow' : ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
      P j * (1 + (fun _ : ℕ ↦ (0 : ℝ)) (j + 2)) := by
    simpa only [add_zero, mul_one] using hchigh
  have hbudget : ∀ s i l j, HasAmplitudeDerivativeBound (fun ξ z ↦ b' i ξ z l j)
      (2 * (n + 1) + (s + 1))
      (Q' s * (1 + (fun _ : ℕ ↦ (0 : ℝ)) (s + 1 + (2 * (n + 1) + 14)))) := by
    simpa only [add_zero, mul_one] using hhigh'
  simpa only [S, add_zero, one_mul] using
    helliptic c hc (fun _ ↦ 0) (fun _ ↦ le_rfl) monotone_const hclow hclow'
      b' hb' hs' hlow' hbudget (fun i ↦ restrictCarrier χ (V i)) hV'

end JanetCartan.ContinuumCommutator
