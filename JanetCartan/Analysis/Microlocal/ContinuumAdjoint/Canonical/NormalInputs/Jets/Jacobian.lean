module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Homogeneity
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.BallBounds

/-!
# Original normalized Jacobian jets on the supported canonical image

The exact matrix homogeneity identity transfers the unit input representative
by the fixed scale `‖ηb‖` into the common input ball. Differentiating this
identity and the fixed linear coordinate maps bounds all joint Jacobian jets
by forward jets of one higher order. The constant is chosen before `Q` from
position order `N + 2` on the fixed coefficient buffer.

The chart, rescaling, physical slice coordinates and column determinant `t⁻¹`
are precisely those already published in `Rescaling`. Neither inverse jets
nor an output-shell hypothesis are needed for this transfer.

Consumer: `PrimitiveJetGeometry.jacobian_jets` for
`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-jacobian`,
`app:ch_background:eq:bg-Psi`, and `app:ch_background:eq:bg-mixed-input`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The fixed-scale matrix identity transfers every joint normalized Jacobian
jet to one higher forward jet, including order zero (`bg-jacobian`). -/
private theorem norm_iteratedFDeriv_normalizedJacobian_le_forward
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)))
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hgradient : ContDiffOn ℝ ∞
      (transportAveragedGradient (CanonicalCarrier.transportPosition T Q)) W)
    {p : JointVariables n}
    (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t)
    (hμp : scaleInput μ (jointInputCoordinates T p) ∈ W) (j : ℕ) :
    let S := (inputCovectorDilation (n := n) μ hμ.ne').toContinuousLinearMap.comp
      (jointInputCoordinates T).toContinuousLinearMap
    let C := (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n) (Euclidean n)).flip
      (normalColumnDilation T μ)
    ‖iteratedFDeriv ℝ j
      ((normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedJacobian t) p‖ ≤
      ‖C‖ * (‖transportDifferentialRestriction (adaptedSliceCoordinates T)‖ *
        ‖iteratedFDeriv ℝ (j + 1)
          (transportAveragedGradient (CanonicalCarrier.transportPosition T Q)) (S p)‖ * ‖S‖ ^ j) := by
  dsimp only
  let S := (inputCovectorDilation (n := n) μ hμ.ne').toContinuousLinearMap.comp
    (jointInputCoordinates T).toContinuousLinearMap
  let C := (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n) (Euclidean n)).flip
    (normalColumnDilation T μ)
  have hsp : S p ∈ W := hμp
  have hdiff : ContDiffOn ℝ ∞ (symbolDifferential T Q) W := by
    intro q hq
    exact ((transportDifferentialRestriction (adaptedSliceCoordinates T)).contDiff.contDiffAt.comp q
      ((hgradient.contDiffAt (hW.mem_nhds hq)).fderiv_right
        (m := ∞) (by simp))).contDiffWithinAt
  have he : symbolDifferential T Q ∘ jointInputCoordinates T =ᶠ[𝓝 p]
      C ∘ (symbolDifferential T Q ∘ S) :=
    ((normalChart_inputDomain_open T Q z₀ ηb r aOuter aPhase).eventually_mem hp).mono
      (fun q hq ↦ (symbolDifferential_comp_normalColumnDilation T Q hηb hr hf hq.1 hμ).symm)
  rw [normalJetRescaling_iteratedFDeriv_normalizedJacobian T Q hηb hr hf hp ht,
    (he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (C.norm_iteratedFDeriv_comp_left
    ((hdiff.contDiffAt (hW.mem_nhds hsp)).comp p S.contDiff.contDiffAt)
      (by simp : (j : ℕ∞ω) ≤ ∞)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
  apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le S hW hdiff hsp j).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg S) j)
  have hb := (transportDifferentialRestriction (adaptedSliceCoordinates T)).norm_iteratedFDeriv_comp_left
    ((hgradient.contDiffAt (hW.mem_nhds hsp)).fderiv_right (m := ∞) (by simp))
    (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j
    (transportDifferentialRestriction (adaptedSliceCoordinates T) ∘
      fderiv ℝ (transportAveragedGradient (CanonicalCarrier.transportPosition T Q))) (S p)‖ ≤ _
  rw [norm_iteratedFDeriv_fderiv] at hb
  exact hb

/-- Uniform finite jets of the ORIGINAL normalized Jacobian, at the normalized
pull of the actual high-frequency support. The constant precedes `Q`; only
position derivatives through `N + 2` and fixed coefficient buffers are used.

The common ball and positive mask radii come from
`exists_actual_refined_supported_geometry`, the segment buffers from
`exists_canonical_coefficient_buffers`, and the position reserve from
`exists_projected_normalPosition_finite_bound`. The sole support inclusion is
produced by `normalSupport_subset_inputDomain`. Consumer: the Jacobian field
of `PrimitiveJetGeometry` (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-jacobian`, `bg-Psi`, and `bg-mixed-input`). -/
theorem exists_normalJetRescaling_normalizedJacobian_jet_bound
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r aOuter aPhase rMask aMask ρ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hrMask : 0 < rMask) (haMask : 0 < aMask)
    (hphysical : 4 * aMask < ρ) (hradial : rMask ≤ ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ ⊆ W)
    (hK : IsCompact K) (hWK : W ⊆ K)
    {Vphase Lphase : Set (Euclidean n × CarrierParameter)}
    (hVphase : IsOpen Vphase) (hLphase : IsCompact Lphase) (hLVphase : Lphase ⊆ Vphase)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase)
    (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B > (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      ContDiffOn ℝ ∞ (CanonicalCarrier.transportPosition T Q) Vphase →
      cNorm Lphase (N + 2) (CanonicalCarrier.transportPosition T Q) ≤ M →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ aOuter,
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      normalSupport T z₀ ηb rMask aMask ⊆
        (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain →
      ∀ p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).push ''
          normalSupport T z₀ ηb rMask aMask, ∀ j ≤ N,
        let g := normalChart T Q z₀ ηb r aOuter aPhase
        let σ := normalJetRescaling T Q z₀ ηb r aOuter aPhase
        let R := ‖(g.carrier (g.pull p)).2‖
        ‖iteratedFDeriv ℝ j (σ.normalizedJacobian R) (σ.normalizedPull R p)‖ ≤ B := by
  let a : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  have hμ : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
  let S := (inputCovectorDilation (n := n) ‖ηb‖ hμ.ne').toContinuousLinearMap.comp
    (jointInputCoordinates T).toContinuousLinearMap
  let C := (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n) (Euclidean n)).flip
    (normalColumnDilation T ‖ηb‖)
  obtain ⟨A, hA, hforward⟩ := exists_transportForward_cNorm_bound
    (isCompact_closedBall a ρ) hball hW hK hWK hVphase hLphase hLVphase hI hIT hsegI hseg
  let D := ‖transportDifferentialRestriction (adaptedSliceCoordinates T)‖ *
    (A (N + 1) * (1 + M))
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg (transportDifferentialRestriction (adaptedSliceCoordinates T)))
    (mul_nonneg (hA _).le (by linarith))
  let B := ‖C‖ * (D * (1 + ‖S‖) ^ N)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg C) (mul_nonneg hD (by positivity))
  refine ⟨1 + B, by linarith, ?_⟩
  intro Q hY hYM hf b cJ V L G hInv htrans hsupport p hp j hj
  have hgradient := transportAveragedGradient_contDiffOn hW hVphase hI hIT hsegI hY
  have hhigh : cNorm (closedBall a ρ) (N + 1)
      (transportAveragedGradient (CanonicalCarrier.transportPosition T Q)) ≤
        A (N + 1) * (1 + M) := by
    apply ((hforward _ hY (N + 1)).1).trans
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hYM) (hA (N + 1)).le
  obtain ⟨q, hq, rfl⟩ := hp
  let R := ‖(jointInputCoordinates T q).2.2‖
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq.2
  have hqp := hsupport hq
  have hpull :
      (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull R
        ((normalChart T Q z₀ ηb r aOuter aPhase).push q) = scaleJointInput T R⁻¹ q := by
    change (normalInputDilation T R).symm
      ((normalChart T Q z₀ ηb r aOuter aPhase).pull
        ((normalChart T Q z₀ ηb r aOuter aPhase).push q)) = _
    rw [normalChart_pull_push T Q hηb hr hInv htrans hqp,
      normalInputDilation_symm_apply T hR.ne']
  have hradius : ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
      ((normalChart T Q z₀ ηb r aOuter aPhase).pull
        ((normalChart T Q z₀ ηb r aOuter aPhase).push q))).2‖ = R := by
    rw [normalChart_pull_push T Q hηb hr hInv htrans hqp]
    rfl
  dsimp only
  rw [hradius, hpull]
  have hunit := normalChart_scaleJointInput_mem T Q z₀ ηb r aOuter aPhase hqp (inv_pos.mpr hR)
  have hsection : S (scaleJointInput T R⁻¹ q) ∈ closedBall a ρ := by
    have hb := conicMaskSupport_radial_section_mem_ball hηb hrMask haMask hphysical hradial hq.1
    apply ball_subset_closedBall
    change scaleInput ‖ηb‖ (jointInputCoordinates T (scaleJointInput T R⁻¹ q)) ∈ ball a ρ
    rw [scaleJointInput, ContinuousLinearEquiv.apply_symm_apply]
    simpa only [scaleInput, smul_smul, div_eq_mul_inv, R, a] using hb
  have hjet := norm_iteratedFDeriv_normalizedJacobian_le_forward T Q hηb hr hf hW
    hgradient hunit hμ hR (hball hsection) j
  apply hjet.trans
  have hjforward := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
    (fun u hu ↦ (hgradient.contDiffAt (hW.mem_nhds (hball hu))).of_le
      (by simp : ((N + 1 : ℕ) : ℕ∞ω) ≤ ∞)) hsection (Nat.add_le_add_right hj 1)
  have hjD : ‖transportDifferentialRestriction (adaptedSliceCoordinates T)‖ *
      ‖iteratedFDeriv ℝ (j + 1)
        (transportAveragedGradient (CanonicalCarrier.transportPosition T Q))
          (S (scaleJointInput T R⁻¹ q))‖ ≤ D :=
    mul_le_mul_of_nonneg_left (hjforward.trans hhigh)
      (norm_nonneg (transportDifferentialRestriction (adaptedSliceCoordinates T)))
  have hpowers : ‖S‖ ^ j ≤ (1 + ‖S‖) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg S) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg S]) hj)
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul hjD hpowers (pow_nonneg (norm_nonneg S) j) hD) (norm_nonneg C)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
