module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.JacobianRegularity

/-!
# The conic inverse for the actual zero-scale transport

The inverse identities and literal Jacobian for the frozen step of
`app:ch_background:prop:bg-frame`. The local buffered inverse is the output
of `CanonicalConic.exists_actual_local_charts`; its transverse comparison is
produced by `CanonicalConic.exists_supported_transverse_threshold`. These
geometric inputs still need to be instantiated together for the finite family;
no positive symbol or coercivity assumption occurs here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (hηb : ηb ≠ 0) (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

include hP hr har hcarrier

/-- Exact forward-map matching throughout the actual supported frozen cone
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). -/
theorem frozenForward_eq_origin {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    transportAveragedGradient (normalizedTransportPosition T Q 0) p =
      transportAveragedGradient (transportPosition T Q) (originInput p) :=
  transportAveragedGradient_zero_eq_origin T Q p
    (phaseBuffer_of_frozenInputDomain T hr hP har hcarrier hp)

/-- Literal Jacobian matching on the actual supported frozen cone
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenJacobian_eq_origin (c : TransportSliceCoordinates n) {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    transportAbsoluteJacobian c (normalizedTransportPosition T Q 0) p =
      transportAbsoluteJacobian c (transportPosition T Q) (originInput p) :=
  transportAbsoluteJacobian_zero_eq_origin T Q hP c p
    (carrierInterior_of_frozenInputDomain hr har hcarrier hp)

/-- Both position variables drop out of the literal frozen determinant on
its original carrier buffer (`new:lem:scaling`, `bg-jacobian`). -/
theorem frozenJacobian_position (c : TransportSliceCoordinates n) {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    transportAbsoluteJacobian c (normalizedTransportPosition T Q 0) p =
      transportAbsoluteJacobian c (normalizedTransportPosition T Q 0) (originInput p) := by
  rw [frozenJacobian_eq_origin T Q hP hr har hcarrier c hp,
    frozenJacobian_eq_origin T Q hP hr har hcarrier c (p := originInput p) hp]
  rfl

variable
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
include hηb hInv htrans

/-- The retained inverse solves the ACTUAL normalized zero-scale transport
frequency equation (`app:ch_background:eq:bg-Psi`). -/
theorem frozenTransportGradient_inverse {p : Variables n × Euclidean 2}
    (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a) :
    transportAveragedGradient (normalizedTransportPosition T Q 0)
      (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p) = p.1.2.2 := by
  rw [frozenForward_eq_origin T Q hP hr har hcarrier
    (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp)]
  exact transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp

/-- The complete augmented right inverse retains both physical positions and
the original spectator (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem augmentedFrozenGradient_inverse :
    EqOn (augmentedTransportGradient (normalizedTransportPosition T Q 0) ∘
      inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a)) id
        (frozenSymbolDomain T Q z₀ ηb r a) :=
  augmentedTransportGradient_inverseCoordinates _ _
    (fun _ hp ↦ frozenTransportGradient_inverse T Q hP hηb hr har hcarrier hInv htrans hp)

/-- The normalized forward map followed by the SAME inverse recovers the
original input, including incidence and covector (`app:ch_background:eq:bg-Psi`). -/
theorem frozenInverse_augmentedGradient {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a)
      (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p := by
  have he : originOutput (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) =
      augmentedTransportGradient (transportPosition T Q) (originInput p) := by
    simp only [originOutput, augmentedTransportGradient, originInput]
    rw [frozenForward_eq_origin T Q hP hr har hcarrier hp]
    rfl
  have hi := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans hp
  have hu := congrArg (fun q : InputVariables n ↦ (q.2.1.1, q.2.2)) hi
  change symbolInverse T Q z₀ ηb r a
    (augmentedTransportGradient (transportPosition T Q) (originInput p)) = (p.2.1.1, p.2.2) at hu
  have huf : frozenSymbolInverse T Q z₀ ηb r a
      (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = (p.2.1.1, p.2.2) := by
    change symbolInverse T Q z₀ ηb r a
      (originOutput (augmentedTransportGradient (normalizedTransportPosition T Q 0) p)) = _
    rw [he, hu]
  simp only [augmentedTransportGradient] at huf
  simp only [inverseCoordinates, augmentedTransportGradient, huf]

/-- The frozen output domain is the genuine image of the normalized forward
map, rather than an independently postulated chart (`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolDomain_eq_image :
    frozenSymbolDomain T Q z₀ ηb r a =
      augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        frozenInputDomain z₀ ηb r a := by
  apply Subset.antisymm
  · intro p hp
    exact ⟨inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p,
      frozenSymbolInverse_maps T Q hηb hr hInv htrans hp,
      augmentedFrozenGradient_inverse T Q hP hηb hr har hcarrier hInv htrans hp⟩
  · rintro _ ⟨p, hp, rfl⟩
    change originOutput (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈
      symbolDomain T Q z₀ ηb r a
    have he : originOutput (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) =
        augmentedTransportGradient (transportPosition T Q) (originInput p) := by
      simp only [originOutput, augmentedTransportGradient, originInput]
      rw [frozenForward_eq_origin T Q hP hr har hcarrier hp]
      rfl
    rw [he, symbolDomain_eq_image T Q hηb hr hInv htrans]
    exact ⟨originInput p, hp, rfl⟩

variable
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))

include hf in
/-- Strict positivity of the literal frozen Jacobian follows from the retained
buffered inverse's determinant gap (`app:ch_background:eq:bg-jacobian`). -/
theorem frozenJacobian_pos (hcJ : 0 < cJ) {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    0 < transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q 0) p := by
  rw [frozenJacobian_eq_origin T Q hP hr har hcarrier _ hp]
  exact CanonicalConic.transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ hp

include hf in
/-- Smoothness of the actual frozen absolute determinant on its input cone
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenJacobian_smooth (hcJ : 0 < cJ) :
    ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q 0)) (frozenInputDomain z₀ ηb r a) := by
  apply ((CanonicalConic.transportAbsoluteJacobian_smooth T Q hηb hr hf hInv htrans hcJ).comp
    originInput_smooth.contDiffOn (fun _ hp ↦ hp)).congr
  intro p hp
  exact frozenJacobian_eq_origin T Q hP hr har hcarrier _ hp

end JanetCartan.ContinuumNormal.FrozenModel
