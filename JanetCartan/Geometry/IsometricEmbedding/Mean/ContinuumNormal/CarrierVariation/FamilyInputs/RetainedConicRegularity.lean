module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.RadialNormalization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedInputs

/-!
# Original-density regularity on the full retained conic inverse image

The normalized inverse range preserves both original carrier labels. It
therefore controls the normal and reduced coefficients at every point of
the full inverse image, even though the finite norm chart is bounded in
frequency. The actual canonical geometry supplies Jacobian smoothness and
nonvanishing; the original positive density class supplies the square root.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CanonicalConic PositiveReference PositiveReference.FlowConstruction
open FullPhaseCharts ActualComparison ContinuumNormalReduction TransportSymbol WideDensity RetainedRowGeometry

/-- Instantiate the full primitive regularity of the actual square-root
weighted scalar on EVERY point in the retained inverse image. The conic root
`zRoot` and original scalar center `z₀` are independent. Normalized frequency
range transfers the two endpoint ranges to the complete cone; the original
`R/8` initial-density class and `R/16` label buffer remain unchanged.

The canonical buffered inverse supplies the literal measure-normalized
Jacobian regularity and gap. The normal and reduced coefficient regularity
is derived from the retained scalar equation, not assumed. Consumer:
`AmplitudeDifference.exists_fullAmplitude_sub_bounds_of_supported_shell`;
sources: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`,
`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_osc:prop:osc-normal`.
-/
theorem retained_originalDensity_primitiveRegularity_on_full_inverse_image
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hRc : 0 < Rc) (hτ : 0 < τ)
    (hKΩ : K ⊆ Ω) (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (him : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (D : CoefficientNormCharts n)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      D.field.region K)
    (hSflow : MapsTo (densityCoordinates T) D.field.region
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot : MapsTo (densityFootpoint T c.inverse) D.field.region
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T c.Q))
      (physicalParameterSet zRoot (6 * a) ×ˢ dataSet zRoot ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T c.Q) (physicalParameterSet zRoot (6 * a))
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot (6 * a),
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T c.Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ)
    {Ωi : Set (Variables n × Euclidean 2)} {Ki : Set (InputVariables n)}
    (hΩi : Ωi ⊆ symbolDomain T c.Q zRoot ηb r (6 * a))
    (hne : ∀ q ∈ Ωi, q.1.2.2 ≠ 0)
    {radius : ℝ} (hRadius : 0 < radius)
    (hnorm : MapsTo (fun q ↦ inverseCoordinates (symbolInverse T c.Q zRoot ηb r (6 * a))
      (normalizeOutputRadius radius q)) Ωi Ki)
    (hcontains : ∀ p ∈ Ki, D.Contains p)
    {rm : ℝ} (hrm : 0 < rm) (hcell : 4 * rm < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2)) (hh : ContDiff ℝ ∞ high)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ∀ y ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8), ContDiffAt ℝ ∞ v y)
    (hpos : ∀ y ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8),
      (1 / 2 : ℝ) ≤ 1 + v y) :
    PrimitiveRegularity
      (TransportKernel.coefficientsOfCarrier
        (data T c.Q F row col c.forward c.inverse
          (fun y ↦ initial y * Real.sqrt (1 + v y)) hrm hcell angular high)
        (FixedCutoffs.physical hrm 1))
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T c.Q))
      (inverseCoordinates (symbolInverse T c.Q zRoot ηb r (6 * a)) '' Ωi) := by
  let u := symbolInverse T c.Q zRoot ηb r (6 * a)
  have hend : ∀ side, MapsTo (densityEndpoint side) Ki D.field.region := by
    intro side p hp
    apply D.field.ball_subset
    cases side
    · exact (hcontains p hp).2.2.2.2.1
    · exact (hcontains p hp).2.2.2.2.2
  have hendFull := densityEndpoint_inverse_mapsTo_of_normalized_range hRadius hne
    (fun t ht q _ ↦ symbolInverse_scale_all T c.Q hηb hr hInv htrans t ht q) hnorm hend
  have hinput : inverseCoordinates u '' Ωi ⊆ symbolInputDomain zRoot ηb r (6 * a) := by
    rintro _ ⟨q, hq, rfl⟩
    exact symbolInverse_maps T c.Q hηb hr hInv htrans (hΩi hq)
  have hvon : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)) :=
    fun y hy ↦ (hv y (ball_subset_closedBall hy)).contDiffWithinAt
  have hvpos (y) (hy : y ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8)) : 0 < 1 + v y :=
    lt_of_lt_of_le (by norm_num) (hpos y (ball_subset_closedBall hy))
  have hweight : ContDiffOn ℝ ∞ (fun y ↦ initial y * Real.sqrt (1 + v y))
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)) :=
    hi.mul ((contDiffOn_const.add hvon).sqrt (fun y hy ↦ (hvpos y hy).ne'))
  have hs := retained_originalScalar_coefficients_contDiffOn c hP hRc hτ hKΩ hKU
    hF him hrank hSK hSflow hR (fun y ↦ initial y * Real.sqrt (1 + v y)) hweight
    (fun y hy ↦ mul_pos (hipos y hy) (Real.sqrt_pos.2 (hvpos y hy))) hfoot
  rw [c.coefficients_eq]
  refine ⟨?_, ?_, ha, hh, ?_, ?_, ?_, ?_,
    (transportAbsoluteJacobian_smooth T c.Q hηb hr hf hInv htrans hcJ).mono hinput,
    fun p hp ↦ (transportAbsoluteJacobian_pos T c.Q hηb hr hf hInv htrans hcJ (hinput hp)).ne',
    fun p hp ↦ (hinput hp).2.2.1⟩
  · exact (FixedCutoffs.physical hrm 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
  · exact (FixedCutoffs.physical hrm 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
  · exact hs.1.comp (densityEndpoint_contDiff false).contDiffOn (hendFull false)
  · exact hs.1.comp (densityEndpoint_contDiff true).contDiffOn (hendFull true)
  · intro i
    exact (contDiffOn_pi.mp hs.2 i).comp (densityEndpoint_contDiff false).contDiffOn (hendFull false)
  · intro i
    exact (contDiffOn_pi.mp hs.2 i).comp (densityEndpoint_contDiff true).contDiffOn (hendFull true)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
