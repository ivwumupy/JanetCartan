module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry.Tangent
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence

/-!
# Exact frozen inverse at a characteristic tangent root

This leaf converts the original plateau geometry into the `hp` and `hmask`
inputs of `exists_canonicalFrozen_weight_threshold`, preserving the buffered
inverse produced by `exists_frozen_conic_inputs`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- For every positive dilation, the explicit adapted projection solves the
actual normalized frozen frequency equation, belongs to its input cone, and is
recovered by the SAME published inverse on the EXACT `6*a` frozen symbol domain.
The geometric plateau bounds, rather than mask positivity or domain membership,
are the inputs (`app:ch_background:prop:bg-frame`, `bg-Psi`). -/
theorem frozen_tangent_plateau_inverse {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {z₀ z : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hz : z ∈ parameterCube (3 * P.radius / 2))
    (hpivot : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z)
      T.data.adapted.normal ≠ 0)
    {κ : Euclidean n}
    (hκ : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z) κ = 0)
    (hη : T.data.adapted.embedding.toContinuousLinearMap.adjoint κ ≠ 0)
    (hs : z 0 ∈ closedBall (z₀ 0) (a / 4))
    (hv : spectatorCenter z = spectatorCenter z₀)
    (hθ : NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ) ∈
      closedBall (NormedSpace.normalize ηb) (angularWidth ηb r / 4))
    {t : ℝ} (ht : 0 < t) :
    let η := t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ
    let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
    transportAveragedGradient (normalizedTransportPosition T Q 0) p = t • κ ∧
    p ∈ frozenInputDomain z₀ ηb r (6 * a) ∧
    ((0, 0, t • κ), spectatorCenter z₀) ∈ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
    frozenSymbolInverse T Q z₀ ηb r (6 * a) ((0, 0, t • κ), spectatorCenter z₀) = (z 0, η) ∧
    angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      (z 0, spectatorCenter z₀) (‖η‖⁻¹ • η) = 1 := by
  dsimp only
  let η := t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ
  let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
  have hnorm : ‖η‖⁻¹ • η =
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ) :=
    NormedSpace.normalize_smul_of_pos ht _
  have hmask : angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      (z 0, spectatorCenter z₀) (‖η‖⁻¹ • η) = 1 := by
    rw [hnorm]
    exact angularMask_one z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      hs (mem_closedBall_self (by positivity)) hθ
  have hpin : p ∈ frozenInputDomain z₀ ηb r (6 * a) :=
    canonicalAngularMask_mem_frozenInputDomain z₀ hηb hr ha (by linarith)
      (smul_ne_zero ht.ne' hη) (by rw [hmask]; exact one_ne_zero)
  have hez : parameter (z 0, spectatorCenter z₀) = z := by
    rw [← hv, parameter_apply, carrierParameters_spectatorCenter]
  have hforward : transportAveragedGradient (normalizedTransportPosition T Q 0) p = t • κ := by
    rw [transportAveragedGradient_zero T Q p
      (phaseBuffer_of_frozenInputDomain T hr hP har hcarrier hpin)]
    change fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch (parameter (z 0, spectatorCenter z₀)))
      (t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ) = t • κ
    rw [hez, map_smul, seedCovector_differential_adjoint_of_tangent T Q hP hz hpivot hκ]
  have haug : augmentedTransportGradient (normalizedTransportPosition T Q 0) p =
      ((0, 0, t • κ), spectatorCenter z₀) := by
    simp only [augmentedTransportGradient, hforward]
    rfl
  have hout : ((0, 0, t • κ), spectatorCenter z₀) ∈
      frozenSymbolDomain T Q z₀ ηb r (6 * a) := by
    rw [frozenSymbolDomain_eq_image T Q hP hηb hr har hcarrier hInv htrans]
    exact ⟨p, hpin, haug⟩
  have hinv := frozenInverse_augmentedGradient T Q hP hηb hr har hcarrier hInv htrans hpin
  rw [haug] at hinv
  have heq := congrArg (fun q : InputVariables n ↦ (q.2.1.1, q.2.2)) hinv
  exact ⟨hforward, hpin, hout, heq, hmask⟩
end JanetCartan.ContinuumNormal.FrozenModel
