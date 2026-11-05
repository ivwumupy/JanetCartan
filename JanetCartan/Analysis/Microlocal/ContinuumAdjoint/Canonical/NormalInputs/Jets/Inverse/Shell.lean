module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Inverse.Scaling

/-!
# Supported shell and normalization factors

Only the closure of the augmented image of the original conic masks is used
in the shell premise. The inverse comparison is derived from the actual
canonical inverse. Consumer: `exists_normalJetRescaling_normalizedPull_bound`.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-Psi`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase rMask aMask : ℝ}

/-- The fixed supported shell controls both frozen dilation factors. The
shell and inverse range are produced by `exists_actual_refined_supported_geometry`;
the positive input-frequency gap is produced by `exists_canonical_coefficient_buffers`.
Only the retained support inclusion remains for the supported-image producer.
Source: `app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`. -/
theorem normalSupport_frozenShell_bounds
    (hηb : ηb ≠ 0) (hr : 0 < r)
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ aOuter,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (p₀ : InputVariables n) (ρ : ℝ) (q₀ : JointVariables n) {τ ℓ ε : ℝ}
    (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlower : ∀ q ∈ closedBall p₀ ρ, ε ≤ ‖q.2.2‖)
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ))
    (hshell : ∀ x : ContinuumNormalReduction.TransportSymbol.Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
        conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ)
    (hsupport : normalSupport T z₀ ηb rMask aMask ⊆
      (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {p : JointVariables n}
    (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).push ''
      normalSupport T z₀ ηb rMask aMask) :
    let R := ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
      ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2‖
    let t := ℓ / ‖p.1.2.2‖
    p ∈ symbolDomain T Q z₀ ηb r aOuter ∧ 1 ≤ R ∧ 0 < t ∧ t ≤ 2 * ℓ ∧
      (scaleFrequency t p.1, p.2) ∈ closedBall q₀ (2 * τ) ∧ ε ≤ R * t := by
  dsimp only
  let R := ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
    ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2‖
  let t := ℓ / ‖p.1.2.2‖
  have hR : 1 ≤ R := normalSupport_image_high_frequency T Q hηb hr hInv htrans hsupport hp
  have hRp : R = ‖(symbolInverse T Q z₀ ηb r aOuter p).2‖ := by
    dsimp [R]
    rw [normalChart_carrier_eq, normalChart_pull_eq]
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, inverseCoordinates]
  have hpΩ : p ∈ symbolDomain T Q z₀ ηb r aOuter := by
    rw [symbolDomain_eq_image T Q hηb hr hInv htrans]
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨jointInputCoordinates T q, (hsupport hq).1, rfl⟩
  have hupper : R ≤ 2 * ‖p.1.2.2‖ := by
    rw [hRp]
    exact symbolInverse_norm_le_two T Q hηb hr hInv htrans hpΩ
  have hfreq : 0 < ‖p.1.2.2‖ := by linarith
  have ht : 0 < t := div_pos hℓ hfreq
  have htupper : t ≤ 2 * ℓ := by
    apply (div_le_iff₀ hfreq).mpr
    nlinarith
  have hscale : t * ‖p.1.2.2‖ = ℓ := div_mul_cancel₀ _ hfreq.ne'
  have hsupported : (scaleFrequency t p.1, p.2) ∈
      closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
        conicMaskSupport z₀ ηb rMask aMask) := by
    apply subset_closure
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨scaleInput t (jointInputCoordinates T q), ?_, ?_⟩
    · refine ⟨hq.1.1, hq.1.2.1, smul_ne_zero ht.ne' hq.1.2.2.1, ?_⟩
      change NormedSpace.normalize (t • (jointInputCoordinates T q).2.2) ∈ _
      rw [NormedSpace.normalize_smul_of_pos ht]
      exact hq.1.2.2.2
    · exact augmentedTransportGradient_scaleInput _ t _
  have hshellmem : (scaleFrequency t p.1, p.2) ∈ closedBall q₀ (2 * τ) := by
    apply closedBall_subset_closedBall (by linarith : τ ≤ 2 * τ)
    apply hshell _ _ _ hsupported
    change ‖t • p.1.2.2‖ = ℓ
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using hscale
  refine ⟨hpΩ, hR, ht, htupper, hshellmem, ?_⟩
  have hl := hlower _ (hrange hshellmem)
  change ε ≤ ‖(symbolInverse T Q z₀ ηb r aOuter (scaleFrequency t p.1, p.2)).2‖ at hl
  rw [symbolInverse_smul T Q hηb hr hInv htrans hpΩ ht] at hl
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← hRp, mul_comm t R] using hl

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
