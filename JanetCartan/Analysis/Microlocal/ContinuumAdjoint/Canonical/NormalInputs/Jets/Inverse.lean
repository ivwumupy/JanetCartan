module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Homogeneity
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.BallBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Inverse.Shell

/-!
# Uniform finite normalized inverse jets on the original supported image

The primitive position bound produces inverse jets on the common output ball.
At each supported output we freeze a positive dilation to the retained shell.
Homogeneity then expresses the same normalized pull through two bounded linear
maps. Both physical positions and the spectator remain in the differentiated
variables. The constant is selected before the transported coefficient `Q`.

The geometric hypotheses are retained outputs of
`CanonicalConic.exists_actual_refined_supported_geometry` and
`CanonicalConic.exists_canonical_coefficient_buffers`. The support inclusion is
supplied by the canonical supported-image construction. The parent supplies
the primitive bound with `exists_projected_normalPosition_finite_bound` and
instantiates the inverse field of `ModifiedNormalSymbol.PrimitiveJetGeometry`.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-Psi`,
`bg-full-complex-amplitude`, and `bg-mixed-input`.
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

/-- The SAME canonical chart and rescaling have a uniform finite normalized
inverse-jet bound on the image of the original support. Only the primitive
position norm, coefficient buffers, and actual inverse geometry are inputs;
no normalized inverse or operator bound is assumed. The shell premise applies
only to the closure of the augmented conic-mask image. In particular `N =
2 * (n + 1)` supplies the inverse jets in `PrimitiveJetGeometry`, with primitive
position order `N + 2` (`app:ch_background:prop:bg-adjoint`, `bg-mixed-input`). -/
theorem exists_normalJetRescaling_normalizedPull_bound
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r aOuter aPhase rMask aMask : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (p₀ : InputVariables n) {ρ : ℝ} (hρ : 0 < ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall p₀ ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {Vphase Lphase : Set (Euclidean n × CarrierParameter)}
    (hVphase : IsOpen Vphase) (hLphase : IsCompact Lphase) (hLVphase : Lphase ⊆ Vphase)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase)
    (A : InputVariables n ≃L[ℝ] ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
    (q₀ : JointVariables n) {τ ℓ ε : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hlower : ∀ q ∈ closedBall p₀ ρ, ε ≤ ‖q.2.2‖)
    (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B > (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      ContDiffOn ℝ ∞ (CanonicalCarrier.transportPosition T Q) Vphase →
      cNorm Lphase (N + 2) (CanonicalCarrier.transportPosition T Q) ≤ M →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      IsOpen V → L ⊆ V →
      (∀ p ∈ physicalParameterSet z₀ aOuter,
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r aOuter →
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) →
      (∀ q ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ x : ContinuumNormalReduction.TransportSymbol.Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
          conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ) →
      normalSupport T z₀ ηb rMask aMask ⊆
        (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain →
      ∀ p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).push ''
        normalSupport T z₀ ηb rMask aMask,
      let R := ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
        ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2‖
      ∀ j, 1 ≤ j → j ≤ N →
        ‖iteratedFDeriv ℝ j
          ((normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull R) p‖ ≤ B := by
  obtain ⟨B₀, hB₀, hjet⟩ := exists_normalChart_commonBall_jet_bound T hηb hr p₀ hρ
    hW hball hK hWK hVphase hLphase hLVphase hI hIT hsegI hseg A
    (isCompact_closedBall q₀ (2 * τ)) N hM
  let C := ‖(jointInputCoordinates T).symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C * (1 + ε⁻¹) * (B₀ * (1 + 2 * ℓ) ^ N), by positivity, ?_⟩
  intro Q hY hYM b cJ V L G hInv hV hLV htrans hOΩ hrange hgap hshell hsupport p hp
  let R := ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
    ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2‖
  let t := ℓ / ‖p.1.2.2‖
  obtain ⟨hpΩ, hR, ht, htupper, hscaled, hRt⟩ := normalSupport_frozenShell_bounds T Q
    hηb hr hInv htrans p₀ ρ q₀ hτ hℓ hlower hrange hshell hsupport hp
  change 1 ≤ R at hR
  change 0 < t at ht
  change t ≤ 2 * ℓ at htupper
  change ε ≤ R * t at hRt
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hinv : (R * t)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ (mul_pos hRpos ht) hε).mpr hRt
  have hi := (hjet Q hY hYM hInv hV hLV htrans hOΩ hrange hgap).1
  dsimp only
  intro j _hj hjN
  apply (norm_iteratedFDeriv_normalizedPull_le_shell T Q hηb hr hInv htrans
    hV hLV hpΩ hRpos ht j).trans
  have hleft : ‖(jointInputCoordinates T).symm.toContinuousLinearMap‖ * (1 + (R * t)⁻¹) ≤
      C * (1 + ε⁻¹) := by
    calc
      _ ≤ ‖(jointInputCoordinates T).symm.toContinuousLinearMap‖ * (1 + ε⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ ≤ C * (1 + ε⁻¹) := mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (by positivity)
  have hpow : (1 + t) ^ j ≤ (1 + 2 * ℓ) ^ N :=
    (pow_le_pow_left₀ (by positivity) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith) hjN)
  exact mul_le_mul hleft (mul_le_mul (hi _ hscaled j hjN) hpow
    (by positivity) hB₀.le) (by positivity) (by positivity)

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
