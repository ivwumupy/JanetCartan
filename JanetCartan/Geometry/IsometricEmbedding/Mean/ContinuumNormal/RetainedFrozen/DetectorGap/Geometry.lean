module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry.Tangent
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Support

/-!
# Retained inner masks in the literal outer frozen inverse

The consumer is the frozen gap on `ContinuumRow.Initialized`'s supplied row.
`LeadingCarrier.exists_covering_retained_forward_adjoint_row_before_geometry`
retains the inner mask radii independently of the outer inverse radii. This
leaf uses its actual plateau and the primitive buffered inverse retained by
`jc-retained-frozen-unit-realization`. It neither changes masks nor extracts
a new frequency cover (`app:ch_background:prop:bg-frame`, Step 2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The SAME tangent root, on the supplied inner angular plateau, belongs to
and is recovered by the outer inverse at `r, 6*a`. Only `a' ≤ r'` is used for
the inner radii. The tangent equation and pivot come from the matched cube seed;
the actual mask plateau is exported by `RetainedAdjointRow`. This is the local
root obligation in `app:ch_background:prop:bg-frame`, Step 2. -/
theorem retained_tangent_mask_inverse {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {z₀ z : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (har : 6 * a ≤ 3 * r)
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
    (hv : spectatorCenter z = spectatorCenter z₀)
    (hplateau : angularMask z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 (z 0, spectatorCenter z)
      (NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ)) = 1)
    {t : ℝ} (ht : 0 < t) :
    let η := t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ
    let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
    transportAveragedGradient (normalizedTransportPosition T Q 0) p = t • κ ∧
    p ∈ frozenInputDomain z₀ ηb r (6 * a) ∧
    ((0, 0, t • κ), spectatorCenter z₀) ∈ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
    frozenSymbolInverse T Q z₀ ηb r (6 * a) ((0, 0, t • κ), spectatorCenter z₀) = (z 0, η) ∧
    angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
      (z 0, spectatorCenter z₀) (‖η‖⁻¹ • η) = 1 := by
  dsimp only
  let η := t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ
  let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
  have hnorm : ‖η‖⁻¹ • η =
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ) :=
    NormedSpace.normalize_smul_of_pos ht _
  have hmask : angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
      (z 0, spectatorCenter z₀) (‖η‖⁻¹ • η) = 1 := by
    rw [hnorm, ← hv]
    exact hplateau
  have hsmall : p ∈ frozenInputDomain z₀ ηb r' (6 * a') :=
    canonicalAngularMask_mem_frozenInputDomain z₀ hηb hr' ha' har'
      (smul_ne_zero ht.ne' hη) (by rw [hmask]; exact one_ne_zero)
  have hpin : p ∈ frozenInputDomain z₀ ηb r (6 * a) :=
    symbolInputDomain_mono z₀ ηb hrr
      (mul_le_mul_of_nonneg_left haa (by norm_num)) hsmall
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

/-- At a matched cube seed, the original frozen incidence point solves the
literal outer inverse equation, with the SAME supplied angular plateau.
`SourceMatching` and `CommonCharts.SeedCovector.exists_retained_seed_covector_buffer`
produce `hQzero` and `hseed`; `CoverData.IsValid` supplies `hz` and `hinc`.
No fresh roots, minors, or frequency neighborhoods are selected
(`app:ch_seed:eq:seed-frozen-detection`, `new:lem:scaling`). -/
theorem retained_cube_incidence_inverse {c C : ℝ} (hP : P.IsValid c C)
    (hQzero : Q.1 0 = cubeStress n)
    {z₀ z : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hz : z ∈ parameterInterior P.radius)
    (hseed : T.carrierGradient Q 0 z = P.toFun z)
    {κ : Euclidean n} (hκ : κ ≠ 0) (hinc : incidence κ (P.toFun z) = 0)
    (hv : spectatorCenter z = spectatorCenter z₀)
    (hplateau : angularMask z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 (z 0, spectatorCenter z)
      (NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ)) = 1)
    {t : ℝ} (ht : 0 < t) :
    let η := t • T.data.adapted.embedding.toContinuousLinearMap.adjoint κ
    let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
    transportAveragedGradient (normalizedTransportPosition T Q 0) p = t • κ ∧
    p ∈ frozenInputDomain z₀ ηb r (6 * a) ∧
    ((0, 0, t • κ), spectatorCenter z₀) ∈ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
    frozenSymbolInverse T Q z₀ ηb r (6 * a) ((0, 0, t • κ), spectatorCenter z₀) = (z 0, η) ∧
    angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
      (z 0, spectatorCenter z₀) (‖η‖⁻¹ • η) = 1 := by
  have hzC : z ∈ parameterCube P.radius := fun i ↦ (hz i).le
  have hzD := parameterCube_subset_doubledInterior hP.1 hzC
  have hpivot : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z)
      T.data.adapted.normal ≠ 0 := by
    rw [hQzero, hseed, (funext fun ξ ↦ determinant_cubeStress ξ)]
    exact (T.data.buffered_transverse_pos (fun i ↦ (hzD i).le)).ne'
  have htangent : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z) κ = 0 := by
    rw [hQzero, hseed, (funext fun ξ ↦ determinant_cubeStress ξ),
      FrozenIncidence.determinant_incidence_eq T hzD,
      FrozenIncidence.dispersion_incidence T hP hz hinc, sub_self, mul_zero]
  exact retained_tangent_mask_inverse T Q hP hηb hr hr' ha' hrr haa har' har hcarrier
    hInv htrans (fun i ↦ (hz i).le.trans (by linarith [hP.1])) hpivot htangent
    (FrozenIncidence.tangential_direction_ne_zero T hP hz hκ hinc) hv hplateau ht

end JanetCartan.ContinuumNormal.RetainedFrozen
