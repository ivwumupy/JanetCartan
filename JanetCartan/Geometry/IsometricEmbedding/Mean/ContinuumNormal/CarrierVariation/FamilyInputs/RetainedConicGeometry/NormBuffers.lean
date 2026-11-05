module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ComparisonBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MaskNormDomains
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicDensity

/-!
# Original scalar and segment buffers on the retained charts

Construct a primitive norm chart inside the retained coefficient cylinder and
the original scalar buffer. The radius `R` of the prescribed scalar is independent
of the radius `Rc` used for the retained null flow. The actual ODE footpoints
remain separate from the Hamilton transport.

Consumers: `exists_retained_originalScalar_coefficient_controls`,
`exists_retained_conic_primitives_sub_tolerance`, and
`exists_retained_conic_densityPair_comparison`. Sources:
`app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`,
and `app:ch_background:eq:bg-Psi`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open ContinuumNormalReduction.TransportSymbol ContinuumAdjoint.Canonical.PhaseExtension
open FullPhaseCharts.ActualComparison WideDensity

/-- Choose a genuine field norm chart on the supplied retained menu. Its open
region lies in the retained coefficient and flow buffers, and every retained
ODE chart with the supplied forward low bound has its labels in the ORIGINAL
scalar ball. The low bound is the one retained by the leading producer; it
is not a bound on the Hamilton transport. `H` may further restrict the field
to the open Hamilton smoothness domain before any conic masks are fixed.
Sources: `bg-frame`, `bg-normalized`, and `bg-full-complex-amplitude`. -/
theorem exists_retained_field_norm_buffers
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)} (z₀ : Euclidean 3)
    {R Rc B τ Mc : ℝ} (hR : 0 < R) (hRc : 0 < Rc) (hτ : 0 < τ)
    (hMc : 0 < Mc) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    {H : Set (Euclidean n × CarrierParameter)} (hH : IsOpen H)
    (hcenter : ((0, (z₀ 0, spectatorCenter z₀)) :
      Euclidean n × CarrierParameter) ∈ H) :
    ∃ D : PrimitiveNormChart (Euclidean n × CarrierParameter),
      D.center = (0, (z₀ 0, spectatorCenter z₀)) ∧ D.region ⊆ H ∧
      MapsTo (densityCoordinates T) D.region
        (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.region K ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
          1 c.forward ≤ Mc →
        MapsTo (densityFootpoint T c.inverse) D.region
          (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) := by
  obtain ⟨cap, hcap, hb⟩ := RetainedLeading.exists_supported_originalScalar_comparison_buffers
    (N := N) (Ω := Ω) (B := B) T z₀ hR hRc hτ hMc hτR hbuffer
  obtain ⟨d, hd, hdH⟩ := Metric.isOpen_iff.mp hH _ hcenter
  let a := min cap d / 2
  have ha : 0 < a := half_pos (lt_min hcap hd)
  have hacap : a < cap := (half_lt_self (lt_min hcap hd)).trans_le (min_le_left _ _)
  have had : a < d := (half_lt_self (lt_min hcap hd)).trans_le (min_le_right _ _)
  let p₀ : Euclidean n × CarrierParameter := (0, (z₀ 0, spectatorCenter z₀))
  let D : PrimitiveNormChart (Euclidean n × CarrierParameter) :=
    ⟨p₀, a / 2, half_pos ha, ball p₀ a, isOpen_ball,
      closedBall_subset_ball (half_lt_self ha)⟩
  have hsupport : D.region ⊆ supportedChart z₀ (2 * a) := by
    intro p hp
    have hh : dist p.1 0 < a ∧
        dist p.2.1 (z₀ 0) < a ∧ dist p.2.2 (spectatorCenter z₀) < a := by
      simpa only [D, p₀, mem_ball, Prod.dist_eq, max_lt_iff] using hp
    change p.1 ∈ closedBall 0 (4 * (2 * a)) ∧
      p.2.1 ∈ closedBall (z₀ 0) (2 * a / 2) ∧
      p.2.2 ∈ closedBall (spectatorCenter z₀) (2 * a / 2)
    exact ⟨by rw [mem_closedBall]; linarith [hh.1],
      by rw [mem_closedBall]; linarith [hh.2.1],
      by rw [mem_closedBall]; linarith [hh.2.2]⟩
  obtain ⟨hflow, hcoef, hfoot⟩ := hb ha hacap
  exact ⟨D, rfl, (ball_subset_ball had.le).trans hdH,
    fun _ hp ↦ hflow (hsupport hp), fun _ hp ↦ hcoef (hsupport hp),
    fun F row col c hc _ hp ↦ hfoot F row col c hc (hsupport hp)⟩

/-- A bounded open input buffer with a positive frequency margin, both
endpoint ranges, and an OPEN segment-parameter buffer. This is chosen inside
the prescribed field chart before refining the inverse domain. It supplies
the exact segment hypotheses of `exists_retained_conic_primitives_sub_tolerance`
and the endpoint hypotheses of `exists_retained_conic_densityPair_comparison`
(`app:ch_background:eq:bg-Psi`). -/
theorem exists_retained_segment_buffer {n : ℕ}
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    {z : CarrierParameter} (hcenter : D.center = (0, z))
    {η : Euclidean (n - 1)} (hη : η ≠ 0) :
    ∃ ρ > (0 : ℝ),
      (∀ p ∈ ball (((0, 0), z, η) : InputVariables n) ρ, ‖η‖ / 2 < ‖p.2.2‖) ∧
      (∀ side, MapsTo (densityEndpoint side)
        (ball (((0, 0), z, η) : InputVariables n) ρ) D.carrier) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t)
        (ball (((0, 0), z, η) : InputVariables n) ρ) D.carrier) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, MapsTo (transportSegmentInput n t)
        (ball (((0, 0), z, η) : InputVariables n) ρ) D.region) := by
  let ρ := min (D.radius / 8) (‖η‖ / 4)
  have hD := D.radius_pos
  have hηpos := norm_pos_iff.mpr hη
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρD : ρ ≤ D.radius / 8 := min_le_left _ _
  have hρη : ρ ≤ ‖η‖ / 4 := min_le_right _ _
  have hparts (p : InputVariables n) (hp : p ∈ ball (((0, 0), z, η) : InputVariables n) ρ) :
      (‖p.1.1‖ < ρ ∧ ‖p.1.2‖ < ρ) ∧ dist p.2.1 z < ρ ∧ dist p.2.2 η < ρ := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] using hp
  have hend (p : InputVariables n) (hp : p ∈ ball (((0, 0), z, η) : InputVariables n) ρ) :
      (p.1.1, p.2.1) ∈ D.carrier ∧ (p.1.2, p.2.1) ∈ D.carrier := by
    have hh := hparts p hp
    constructor
    · rw [PrimitiveNormChart.carrier, hcenter, mem_closedBall, Prod.dist_eq,
        dist_zero_right, max_le_iff]
      exact ⟨by linarith [hh.1.1], by linarith [hh.2.1]⟩
    · rw [PrimitiveNormChart.carrier, hcenter, mem_closedBall, Prod.dist_eq,
        dist_zero_right, max_le_iff]
      exact ⟨by linarith [hh.1.2], by linarith [hh.2.1]⟩
  have hseg (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2)
      (p : InputVariables n) (hp : p ∈ ball (((0, 0), z, η) : InputVariables n) ρ) :
      transportSegmentInput n t p ∈ D.carrier := by
    have hh := hparts p hp
    have ht' : ‖t‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hnorm : ‖p.1.2 + t • (p.1.1 - p.1.2)‖ ≤ 5 * ρ := by
      calc
        _ ≤ ‖p.1.2‖ + ‖t‖ * ‖p.1.1 - p.1.2‖ := by
          simpa only [norm_smul] using norm_add_le p.1.2 (t • (p.1.1 - p.1.2))
        _ ≤ ρ + 2 * (ρ + ρ) := add_le_add hh.1.2.le
          (mul_le_mul ht' ((norm_sub_le _ _).trans (add_le_add hh.1.1.le hh.1.2.le))
            (norm_nonneg _) (by norm_num))
        _ = 5 * ρ := by ring
    rw [transportSegmentInput_apply]
    change (p.1.2 + t • (p.1.1 - p.1.2), p.2.1) ∈ closedBall D.center D.radius
    rw [hcenter, mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right]
    exact ⟨by linarith [D.radius_pos], by linarith [hh.2.1, D.radius_pos]⟩
  refine ⟨ρ, hρ, ?_, ?_, ?_, fun t ht p hp ↦ D.ball_subset (hseg t ht p hp)⟩
  · intro p hp
    have hh := (hparts p hp).2.2
    have hn := norm_sub_norm_le η p.2.2
    rw [dist_eq_norm, norm_sub_rev] at hh
    linarith [norm_pos_iff.mpr hη]
  · intro side p hp
    cases side
    · exact (hend p hp).1
    · exact (hend p hp).2
  · intro t ht p hp
    exact hseg t ⟨by linarith [ht.1], by linarith [ht.2]⟩ p hp

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
