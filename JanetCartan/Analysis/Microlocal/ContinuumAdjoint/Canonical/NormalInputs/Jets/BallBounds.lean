module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Phase

/-!
# Finite primitive bounds on the canonical common balls

These deductions consume precisely the coefficient buffers, inverse range, and
augmented half-gap retained by the canonical producers. The budget is chosen
before the transported position and its inverse. No inverse or Jacobian jet is
assumed. The Jacobian reserve of order `N` uses position order `N + 2`, hence
immersion order `N + 6` by the sharp projected-position producer.

Consumer: normalized jets in `PrimitiveJetGeometry` for
`app:ch_background:prop:bg-adjoint` and `bg-mixed-input`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- A finite primitive position bound gives both inverse and ORIGINAL slice
differential bounds on the common balls. The differential estimate costs one
additional forward derivative, so position order `N + 2` suffices. All
constants precede `Y` and `u`; the half-gap and inverse identities are geometric
outputs of `exists_actual_refined_supported_geometry` (`bg-Psi`, `bg-jacobian`). -/
theorem exists_commonBall_primitive_jet_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {V L : Set (Euclidean n × CarrierParameter)}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {O : Set (Variables n × Euclidean 2)} (hO : IsCompact O)
    (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B > (0 : ℝ), ∀
      (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (Ω : Set (Variables n × Euclidean 2)),
      ContDiffOn ℝ ∞ Y V → cNorm L (N + 2) Y ≤ M →
      IsOpen Ω → O ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) O (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      (∀ p ∈ O, ∀ j ≤ N, ‖iteratedFDeriv ℝ j (inverseCoordinates u) p‖ ≤ B) ∧
      (∀ p ∈ closedBall a ρ, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (transportSliceDifferential c Y) p‖ ≤ B) := by
  obtain ⟨C, hC, hf⟩ := exists_transportForward_cNorm_bound
    (isCompact_closedBall a ρ) hball hW hK hWK hV hL hLV hI hIT hsegI hseg
  have hlow : 0 ≤ C 1 * (1 + M) := mul_nonneg (hC 1).le (by linarith)
  obtain ⟨D, hD, hi⟩ := exists_inverseCoordinates_oneHigh_bound
    a hρ hW hball A hO hlow N
  let Bi := D * (1 + C N * (1 + M))
  let Bj := ‖transportDifferentialRestriction c‖ * (C (N + 1) * (1 + M))
  have hBi : 0 < Bi := mul_pos hD (by
    have := mul_pos (hC N) (by linarith : 0 < 1 + M)
    linarith)
  have hBj : 0 ≤ Bj := mul_nonneg (norm_nonneg (transportDifferentialRestriction c))
    (mul_nonneg (hC (N + 1)).le (by linarith))
  refine ⟨Bi + Bj, by linarith, ?_⟩
  intro Y u Ω hY hYM hΩ hOΩ hu hrange hgap heq
  have hYM' (j : ℕ) (hj : j ≤ N + 2) : cNorm L j Y ≤ M :=
    (cNorm_mono_order hj).trans hYM
  have hforward := augmentedTransportGradient_contDiffOn hW hV hI hIT hsegI hY
  have hgradient := transportAveragedGradient_contDiffOn hW hV hI hIT hsegI hY
  have hlowY : cNorm (closedBall a ρ) 1 (augmentedTransportGradient Y) ≤
      C 1 * (1 + M) :=
    ((hf Y hY 1).2).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hYM' 2 (by omega))) (hC 1).le)
  have hhighY : cNorm (closedBall a ρ) N (augmentedTransportGradient Y) ≤
      C N * (1 + M) :=
    ((hf Y hY N).2).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hYM' (N + 1) (by omega))) (hC N).le)
  have hinverse : cNorm O N (inverseCoordinates u) ≤ Bi := by
    have hh := hi Y u Ω hΩ hOΩ hforward hu hlowY hrange hgap heq
    exact (le_add_of_nonneg_right (cNorm_nonneg O N u)).trans
      (hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hhighY) hD.le))
  have hdiff : cNorm (closedBall a ρ) (N + 1) (transportAveragedGradient Y) ≤
      C (N + 1) * (1 + M) :=
    ((hf Y hY (N + 1)).1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hYM' (N + 1 + 1) (by omega))) (hC (N + 1)).le)
  constructor
  · intro p hp j hj
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hO
      (fun q hq ↦ ((inverseCoordinates_contDiffOn hu).contDiffAt
        (hΩ.mem_nhds (hOΩ hq))).of_le (by simp)) hp hj).trans
          (hinverse.trans (le_add_of_nonneg_right hBj))
  · intro p hp j hj
    apply (norm_iteratedFDeriv_transportSliceDifferential_le c Y hW hgradient
      (hball hp) j).trans
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun q hq ↦ (hgradient.contDiffAt (hW.mem_nhds (hball hq))).of_le
        (by simp : ((N + 1 : ℕ) : ℕ∞ω) ≤ ∞)) hp (Nat.add_le_add_right hj 1)
    exact (mul_le_mul_of_nonneg_left (hb.trans hdiff)
      (norm_nonneg (transportDifferentialRestriction c))).trans
      (le_add_of_nonneg_left hBi.le)

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Specialization to the SAME canonical inverse and measurable original
Jacobian field. The hypotheses are retained signatures of the refined
geometry and coefficient-buffer producers; the inverse identity and all jet
bounds are discharged here. Constants precede `Q`. The consuming normalized
jet estimates only need this on the common input and output balls
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-mixed-input`). -/
theorem exists_normalChart_commonBall_jet_bound
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (a : InputVariables n) {ρ : ℝ} (hρ : 0 < ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {Vphase Lphase : Set (Euclidean n × CarrierParameter)}
    (hVphase : IsOpen Vphase) (hLphase : IsCompact Lphase) (hLVphase : Lphase ⊆ Vphase)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {O : Set (Variables n × Euclidean 2)} (hO : IsCompact O)
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
      O ⊆ symbolDomain T Q z₀ ηb r aOuter →
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)) O (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ O, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)) p‖ ≤ B) ∧
      (∀ p ∈ closedBall a ρ, ∀ j ≤ N, ‖iteratedFDeriv ℝ j (symbolDifferential T Q) p‖ ≤ B) := by
  obtain ⟨B, hB, hb⟩ := exists_commonBall_primitive_jet_bound
    (adaptedSliceCoordinates T) a hρ hW hball hK hWK hVphase hLphase hLVphase
    hI hIT hsegI hseg A hO N hM
  refine ⟨B, hB, ?_⟩
  intro Q hY hYM b cJ V L G hInv hV hLV htrans hOΩ hrange hgap
  obtain ⟨hi, hj⟩ := hb (CanonicalCarrier.transportPosition T Q)
    (symbolInverse T Q z₀ ηb r aOuter) (symbolDomain T Q z₀ ηb r aOuter) hY hYM
    (symbolDomain_open T Q hηb hr hInv htrans hV hLV) hOΩ
    (symbolInverse_smooth T Q hηb hr hInv htrans hLV) hrange hgap
    (fun _ hp ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp)
  refine ⟨hi, ?_⟩
  intro p hp j hjN
  have hs := transportAveragedGradient_contDiffOn hW hVphase hI hIT hsegI hY
  have he : symbolDifferential T Q =ᶠ[nhds p]
      transportSliceDifferential (adaptedSliceCoordinates T) (CanonicalCarrier.transportPosition T Q) :=
    (hW.eventually_mem (hball hp)).mono (fun q hq ↦
      (transportSliceDifferential_eq_restriction (adaptedSliceCoordinates T) _
        ((hs.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp))).symm)
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hj p hp j hjN

/-- The explicit finite immersion reserve for the adjoint normalized jets.
Position order `2*(n+1)+2` costs four more immersion derivatives in the actual
projected-position producer. Thus order `2*(n+1)+6` fixes the position budget
BEFORE `F` varies (`app:ch_background:eq:bg-mixed-input`). -/
theorem exists_projected_normalPosition_finite_bound {d : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLO : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B > (0 : ℝ), ∀ (F : Euclidean n → Euclidean d)
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 6) F ≤ M →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨ProjectedStressFrame.projectedStress F,
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      cNorm L (2 * (n + 1) + 2) (CanonicalCarrier.transportPosition T Q) ≤ B := by
  obtain ⟨A, hA, hbound⟩ := CanonicalCarrier.exists_projected_transportPosition_bound
    T (N := d) hP hL hLO hK hKU hball M hκmet hκ
  refine ⟨A (2 * (n + 1) + 2) * (1 + M), mul_pos (hA _) (by linarith), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  have hfour : cNorm K 4 F ≤ M :=
    (cNorm_mono_order (by omega : 4 ≤ 2 * (n + 1) + 6)).trans hFM
  apply (hbound F hF hi hrank hfour hmet hnormal hlow (2 * (n + 1) + 2)).trans
  have hb : cNorm K (2 * (n + 1) + 2 + 4) F ≤ M := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hFM
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hb) (hA _).le

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
