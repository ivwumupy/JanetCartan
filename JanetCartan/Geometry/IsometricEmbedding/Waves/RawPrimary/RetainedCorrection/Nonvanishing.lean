module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LeadingInputs
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.AdaptedReduction

/-!
# Full-phase transversality on the retained Hamilton witnesses

The common initializer's `exists_positive_geometry_retained_seed_family`
retains an inner state ball, containment of the SAME Hamilton flow in that
ball, and transversality there for every admitted frame. These primitive
conclusions also survive in
`exists_common_normalized_history_reference_retained_leading`.
Here they imply transversality at the full phase gradient, before any
reciprocal estimate is used. The two nonzero selected nullvectors exported
by the retained leading family then give nonvanishing of its literal adapted
denominator. Neither the covector nor the selected indices are replaced.

Consumer: the quantitative correction on the retained working domains in
`app:ch_waves:eq:primary-algebraic-correction` and
`app:ch_waves:eq:WKB-grading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.RetainedCorrection
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase
open LeadingWave.FullModulation NullTransport

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The full phase gradient lies in the SAME inner state ball retained by
`NormalizedHistory.exists_positive_geometry_retained_seed_family`.
This holds for every independent full covector in the original phase domain,
without a carrier-graph restriction (`app:ch_waves:thm:individual`). -/
theorem fullPhase_state_mem_retained_ball {Rinner : ℝ}
    (hstate : ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) Rinner)
    {w : Euclidean n × Euclidean (n - 1)} (hw : w ∈ phaseDomain T) :
    (w.1, phaseGradient T Q w.1 w.2) ∈ closedBall (0, T.data.center) Rinner := by
  have ht : (w.1, (0, w.2)) ∈ (T.currentChart Q).target :=
    (inclusion_mem_ball T).mpr hw
  have ha := (T.currentChart Q).source_admissible _
    ((T.currentChart Q).maps_to_source _ ht)
  have hs := hstate _ ha
  rw [(T.currentChart Q).right_inverse _ ht] at hs
  rwa [phaseGradient_eq_chartMomentum T Q hw]

/-- The retained inner-ball Hamilton geometry implies a nonzero determinant
derivative at the actual full phase gradient. Both premises are literal outputs
of `NormalizedHistory.exists_positive_geometry_retained_seed_family`, retained
unchanged by the common initializer. No minor or reciprocal-denominator gap
is assumed (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullPhase_root_ne_zero_of_retained_geometry {Rinner : ℝ}
    (hstate : ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) Rinner)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) Rinner,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {w : Euclidean n × Euclidean (n - 1)} (hw : w ∈ phaseDomain T) :
    fderiv ℝ (determinant (Q.1 w.1)) (phaseGradient T Q w.1 w.2)
      T.data.adapted.normal ≠ 0 := by
  let ξ := phaseGradient T Q w.1 w.2
  have ht : (w.1, (0, w.2)) ∈ (T.currentChart Q).target :=
    (inclusion_mem_ball T).mpr hw
  have hm : (w.1, ξ) ∈ normalizedSymbolDomain U :=
    carrierPhase_gradient_mem_domain (T.currentChart Q) id ht
  have hc : determinant (Q.1 w.1) ξ = 0 := phase_characteristic T Q hw
  have hp : (normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp (w.1, ξ) =
      determinantNormalization ξ • gradient (determinant (Q.1 w.1)) ξ := by
    change NormalizedSymbol.covectorGradient (normalizedSymbol Q.1) (w.1, ξ) = _
    rw [NormalizedSymbol.covectorGradient_eq_gradient
      ((contDiffAt_normalizedSymbol (Q.2.1.contDiffAt (hU.mem_nhds hm.1)) hm.2).differentiableAt
        (by simp))]
    simp only [gradient, fderiv_covector_normalizedSymbol_of_determinant_eq_zero Q.1 w.1 hm.2 hc,
      map_smul]
  have hne := htrans _ (fullPhase_state_mem_retained_ball T Q hstate hw)
  change ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp (w.1, ξ),
    T.data.adapted.normal⟫_ℝ ≠ 0 at hne
  rw [hp, inner_smul_left, inner_gradient_left] at hne
  exact fun hz ↦ hne (by rw [hz, mul_zero])

/-- Recover the SAME selected denominator on the full-covector working domain.
The inner state geometry comes from the common initializer and the nonzero
nullvectors from `exists_finite_retained_leading_family_before_geometry`.
This supplies nonvanishing before invoking any reciprocal budget
(`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-grading`). -/
theorem fullPhase_denominator_ne_zero_of_retained_geometry {Rinner : ℝ}
    (hstate : ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) Rinner)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) Rinner,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (row col : Fin n) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hsymm : ∀ i, (Q.1 w.1 i).IsSymm)
    (hk : nullvector T Q col w ≠ 0) (hl : conullvector T Q row w ≠ 0) :
    adaptedDenominator T Q row col w ≠ 0 := by
  have hm := fullPhase_minor_ne_zero_of_nullvectors T Q row col hw hk hl
  change adaptedTimeCoefficient _ _ _ _ _ ≠ 0
  rw [adaptedTimeCoefficient_eq_minor_mul_fderiv _ hsymm _
    (phase_characteristic T Q hw) hm, reducedDeterminant_eq_determinant]
  exact mul_ne_zero hm (fullPhase_root_ne_zero_of_retained_geometry T Q hstate htrans hw)

end JanetCartan.RawPrimary.RetainedCorrection
