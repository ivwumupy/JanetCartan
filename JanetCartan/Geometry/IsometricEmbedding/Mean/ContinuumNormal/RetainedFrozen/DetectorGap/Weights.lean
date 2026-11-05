module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Normal

/-!
# Positive weights for the retained selected null column

The primitive selected-column null relation and nonvanishing from
`LeadingWave.FullModulation.exists_finite_actual_leading_family`, restricted
by `FullModulation.nullvector_on_carrier`, give a nonzero actual normal.
The retained outer Jacobian gap and inner angular plateau then give positive
weight. The consumer is `retained_incidence_spectral_bounds`
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ) (hV : IsOpen V) (hLV : L ⊆ V)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a' / 2)

open NullTransport ProjectedStressFrame AmbientResponse LeadingWave

/-- The unit-initial frozen normal is nonzero for the retained nonzero null
column. `FullModulation.exists_finite_actual_leading_family` supplies the SAME column's nonvanishing and null
relation; the actual principal-normal equation supplies nonvanishing of its
completion (`new:lem:scaling`). No lower normal bound is assumed. -/
theorem retainedFrozenNormal_ne_zero
    (hF : ContDiffAt ℝ 2 F 0)
    (hrank : Set.range (normalMap F 0) = (normalSpace F 0 : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F 0 i)
    (z : CarrierParameter)
    (hnull : pencil (projectedStress F 0) (T.carrierGradient Q 0 (parameter z)) *ᵥ
      (fun j ↦ carrierNullvector T Q col (0, parameter z) j) = 0)
    (hξ : T.carrierGradient Q 0 (parameter z) ≠ 0)
    (hcol : carrierNullvector T Q col (0, parameter z) ≠ 0) :
    normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z ≠ 0 := by
  simpa only [normalField, carrierScalarAmplitude_origin_unit, one_smul] using
    NormalizedBackground.SourceGeometry.principalNormal_ne_zero_of_pencil_null
      hF hrank hframe hnull hξ hcol

include hP hηb hr har hcarrier hf hInv htrans hcJ

/-- The literal weight is strictly positive at a retained plateau inverse
point above the geometric threshold. The actual normal formula, selected
nonzero null column, positive Jacobian and original high mask prove every
factor positive (`app:ch_background:prop:bg-frame`, Step 2). The primitive
geometry is retained by `jc-retained-frozen-unit-realization`; no new masks
or minors are chosen. -/
theorem retainedFrozenWeight_pos_of_selected_column
    (hgap : ∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hF : ContDiffAt ℝ 2 F 0)
    (hrank : Set.range (normalMap F 0) = (normalSpace F 0 : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F 0 i)
    {p : Variables n × Euclidean 2} (hp : p ∈ Ω₀)
    (hk : frozenHighFrequencyRadius T G ≤ ‖p.1.2.2‖)
    (hmask : angular₀ ((u₀ p).1, p.2) (‖(u₀ p).2‖⁻¹ • (u₀ p).2) = 1)
    (hnull : pencil (projectedStress F 0)
      (T.carrierGradient Q 0 (parameter ((u₀ p).1, p.2))) *ᵥ
        (fun j ↦ carrierNullvector T Q col (0, parameter ((u₀ p).1, p.2)) j) = 0)
    (hξ : T.carrierGradient Q 0 (parameter ((u₀ p).1, p.2)) ≠ 0)
    (hcol : carrierNullvector T Q col (0, parameter ((u₀ p).1, p.2)) ≠ 0) :
    0 < inputWeight a₀ J₀ (inverseCoordinates u₀ p) := by
  have hpin := frozenSymbolInverse_maps T Q hηb hr hInv htrans hp
  have hn := norm_pos_iff.mpr (retainedFrozenNormal_ne_zero T Q F row col Φ Y
    hF hrank hframe ((u₀ p).1, p.2) hnull hξ hcol)
  have hJ := frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hpin
  have hhigh := frozenInverse_highFrequency_one T G Q hηb hr hf hInv htrans hgap hp hk
  have hη : 0 < ‖(u₀ p).2‖ := norm_pos_iff.mpr hpin.2.2.1
  change 0 < 1 * 1 * angular₀ ((u₀ p).1, p.2) (‖(u₀ p).2‖⁻¹ • (u₀ p).2) ^ 2 *
    FixedCutoffs.highFrequency ‖(u₀ p).2‖ ^ 2 * ‖(u₀ p).2‖ / J₀ (inverseCoordinates u₀ p) *
      ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 ((u₀ p).1, p.2)‖ ^ 2 *
      ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 ((u₀ p).1, p.2)‖ ^ 2
  rw [hmask, hhigh]
  positivity


include hrr haa in
/-- The original cube incidence root has positive literal weight on the
retained masks. This combines outer inverse recovery with the actual selected
column normal formula. Its inputs are the original plateau, exact seed match,
and the retained `FullModulation` column's null relation and nonvanishing;
positive weights and detector annihilation are conclusions, never premises
(`app:ch_seed:eq:seed-frozen-detection`, `app:ch_background:prop:bg-frame`). -/
theorem retained_cube_incidence_positive_weight
    (har' : a' ≤ r') (hQzero : Q.1 0 = cubeStress n)
    (hgap : ∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hF : ContDiffAt ℝ 2 F 0)
    (hrank : Set.range (normalMap F 0) = (normalSpace F 0 : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F 0 i)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    (hseed : T.carrierGradient Q 0 z = P.toFun z)
    {κ : Euclidean n} (hκ : κ ≠ 0) (hinc : incidence κ (P.toFun z) = 0)
    (hv : spectatorCenter z = spectatorCenter z₀)
    (hplateau : angular₀ (z 0, spectatorCenter z)
      (NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint κ)) = 1)
    (hnull : pencil (projectedStress F 0) (T.carrierGradient Q 0 z) *ᵥ
      (fun j ↦ carrierNullvector T Q col (0, z) j) = 0)
    (hcol : carrierNullvector T Q col (0, z) ≠ 0)
    {t : ℝ} (ht : 0 < t) (hk : frozenHighFrequencyRadius T G ≤ ‖t • κ‖) :
    ((0, 0, t • κ), spectatorCenter z₀) ∈ Ω₀ ∧
    parameter ((u₀ ((0, 0, t • κ), spectatorCenter z₀)).1, spectatorCenter z₀) = z ∧
    0 < inputWeight a₀ J₀ (inverseCoordinates u₀ ((0, 0, t • κ), spectatorCenter z₀)) := by
  have hroot := retained_cube_incidence_inverse T Q hP hQzero hηb hr hr' ha'
    hrr haa har' har hcarrier hInv htrans hz hseed hκ hinc hv hplateau ht
  dsimp only at hroot
  obtain ⟨_, _, hp, hinv, hmask⟩ := hroot
  have hez : parameter ((u₀ ((0, 0, t • κ), spectatorCenter z₀)).1,
      spectatorCenter z₀) = z := by
    rw [hinv, ← hv, parameter_apply, carrierParameters_spectatorCenter]
  have hξ : T.carrierGradient Q 0 z ≠ 0 := by
    rw [hseed]
    exact T.data.localReference.covectorSet_nonzero _ (T.data.buffered_mem z
      (fun i ↦ (hz i).le.trans (by linarith [hP.1])))
  refine ⟨hp, hez, ?_⟩
  apply retainedFrozenWeight_pos_of_selected_column T Q F row col Φ Y hP hηb hr hr' ha'
    har hcarrier hf hInv htrans hcJ hgap hF hrank hframe hp hk
  · simpa only [hinv] using hmask
  · simpa only [hez] using hnull
  · simpa only [hez] using hξ
  · simpa only [hez] using hcol

end JanetCartan.ContinuumNormal.RetainedFrozen
