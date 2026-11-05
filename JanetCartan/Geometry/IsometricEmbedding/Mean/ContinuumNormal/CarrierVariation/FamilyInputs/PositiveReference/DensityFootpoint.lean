module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.CanonicalDensity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# The actual density footpoint and its fixed compact range

The density in `app:ch_background:eq:bg-full-complex-amplitude` evaluates
the initial scalar at the inverse ODE label, at both physical positions.
This is distinct from the covector derivative defining `transportPosition`.
The actual positive null-transport constructor below gives a fixed compact
range before the immersion or initial scalar varies. No small-density
restriction is imposed for this range statement.

Consumer: finite-order initial-density composition in
`FamilyInputs.PositiveReference`, for `paper-v2.tex`,
`app:ch_background:prop:bg-frame`. Finite-order dependence of the ODE maps
on the primitive coefficients remains a separate comparison obligation.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ContinuumRow ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The fixed coordinate change used by the literal ODE density in
`app:ch_background:eq:bg-full-complex-amplitude`, including the original
carrier-label relabeling. It does not involve the Hamilton transport map. -/
def densityCoordinates : (Euclidean n × CarrierParameter) →L[ℝ]
    ℝ × (Euclidean (n - 1) × Euclidean 3) :=
  (FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ (Euclidean n)).prodMap parameter)

/-- The actual ODE footpoint, with its carrier parameter retained, in
`app:ch_background:eq:bg-full-complex-amplitude`. The map `Y` is the inverse
constructed by `exists_projected_local_positive_amplitude`. -/
def densityFootpoint
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : Euclidean n × CarrierParameter) : Euclidean (n - 1) × Euclidean 3 :=
  Y (densityCoordinates T p)

/-- Literal agreement with the ODE argument in
`canonical_inputDensity_initial` (`app:ch_background:eq:bg-T`). -/
theorem densityFootpoint_eq
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : Euclidean n × CarrierParameter) :
    densityFootpoint T Y p = Y (FlowAmplitude.coordinates
      (ActualFlow.adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) := rfl

/-- An actual flow-tube range yields a fixed compact range for the literal
density footpoint. The range premise is produced by
`exists_projected_local_positive_amplitude`, and instantiated below; it is
not a continuity assumption. Source: `app:ch_waves:thm:leading` and
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem densityFootpoint_mapsTo_closedBall
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    {K : Set (Euclidean n × CarrierParameter)} {I : Set ℝ}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {r : ℝ}
    (hK : MapsTo (densityCoordinates T) K D)
    (hY : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ ball p₀ r)) :
    MapsTo (densityFootpoint T Y) K (closedBall p₀ r) :=
  fun _ hp ↦ ball_subset_closedBall (hY (hK hp)).2

/-- The fixed physical/carrier coordinate change loses no derivative in the
difference of the actual ODE footpoints. This is the precise final pullback
needed after ODE comparison on the adapted compact cylinder, and applies in
particular to `CoefficientNormCharts.field.carrier`.
The smoothness and range inputs come from the actual positive transport
constructor. Source: `app:ch_background:prop:bg-frame`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_densityFootpoint_sub_bound
    {K : Set (Euclidean n × CarrierParameter)}
    {L : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hK : IsCompact K) (hL : IsCompact L) (hmaps : MapsTo (densityCoordinates T) K L) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ Y Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        (∀ q ∈ L, ContDiffAt ℝ ∞ Y q) → (∀ q ∈ L, ContDiffAt ℝ ∞ Y₀ q) →
        ∀ m, cNorm K m (densityFootpoint T Y - densityFootpoint T Y₀) ≤
          B m * cNorm L m (Y - Y₀) := by
  obtain ⟨B, hB, hb⟩ := ActualCarriers.ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Euclidean (n - 1) × Euclidean 3) hK hL
    (fun _ _ ↦ (densityCoordinates T).contDiff.contDiffAt) hmaps
  exact ⟨B, hB, fun Y Y₀ hY hY₀ m ↦ hb (Y - Y₀)
    (fun q hq ↦ (hY q hq).sub (hY₀ q hq)) m⟩

/-- The primitive hypotheses of the positive-null-transport construction
produce the SAME inverse ODE footpoint with a fixed compact range and smooth
buffer. The minor, radii, threshold and range precede the immersion and initial
scalar. The forward ODE, inverse identities, parameter preservation, and
positive transported initial value are retained for subsequent comparisons.
No finite-order continuity conclusion is asserted here.
Source: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`.
The larger original positive-density class remains allowed for this result. -/
theorem exists_positive_densityFootpoint_range {N : ℕ} (hn : 2 ≤ n)
    {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ R η τ : ℝ,
      0 < R ∧ 0 < η ∧ 0 < τ ∧
      IsCompact (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let C := FlowAmplitude.coordinates (Z := Euclidean 3)
          (ActualFlow.adaptedCoordinates T.data.adapted)
        let I := Ioo (-τ) τ
        let B := ball ((0 : Euclidean (n - 1)), z) (R / 8)
        let W := densityCoordinates T ⁻¹'
          (I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32))
        ∃ (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
          IsOpen D ∧ I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          ContDiffOn ℝ ∞ Φ (I ×ˢ B) ∧ ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ B) ∧
          (∀ p ∈ B, Φ (0, p) = p) ∧
          (∀ p ∈ B, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
            (((ActualFlow.adaptedCoordinates T.data.adapted)
              (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ (densityFootpoint T Y) W ∧
          MapsTo (densityFootpoint T Y) W
            (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          (∀ p ∈ W, (densityFootpoint T Y p).2 = parameter p.2) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            ContDiffOn ℝ ∞ initial B → (∀ p ∈ B, 0 < initial p) →
            let α := carrierScalarAmplitude T Q F row col Φ Y initial
            ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
              (∀ p ∈ B, α (T.data.adapted.embedding p.1, p.2) = initial p) ∧
              (∀ p ∈ W, 0 < α (p.1, parameter p.2)) := by
  obtain ⟨row, col, ρ, R, η, τ, g, A, H, _hρ, hR, hη, hτ, _hg, _hA, _hH,
      _hbuffer, _hτR, hlocal⟩ :=
    exists_projected_local_positive_amplitude (N := N) hn hP T hK hKU hball
      C₀ hκmet hκnormal z hz
  refine ⟨row, col, R, η, τ, hR, hη, hτ, isCompact_closedBall _ _, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, D, Φ, Y, hD, hsmall, _hbig, _hphys, hΦ, hY, _hΦD, hYU,
      hinit, hYΦ, hΦY, _hcarrier, hYcarrier, hode, _hnull, _hcoeff, _hflow,
      _hregular, _hΦbuffer, _hYbuffer, _hbuffer, _hτR, _hgap, hscalar⟩ :=
    hlocal F hF hi hrank hlowF hmet hnormal hclose
  refine ⟨hlow, D, Φ, Y, hD, hsmall, hΦ, hY, hYU, hinit, hYΦ, hΦY, hode,
    ?_, ?_, ?_, ?_⟩
  · exact hY.comp (densityCoordinates T).contDiff.contDiffOn (fun _ hp ↦ hsmall hp)
  · exact densityFootpoint_mapsTo_closedBall T (fun _ hp ↦ hsmall hp) hYU
  · intro p hp
    exact hYcarrier _ (hsmall hp)
  · intro initial hinitial hpos
    obtain ⟨hα, _hαk, hαinit, hαpos, _hcompact, _hpde, _hsymbol, _hreduce, _hlower⟩ :=
      hscalar initial hinitial hpos
    exact ⟨hα, hαinit, fun _ hp ↦ hαpos _ (hsmall hp)⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
