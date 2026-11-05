module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates

/-!
# The normalized null direction is a Hamilton velocity

Use the actual adjugate row and column and the normalized determinant symbol.
The nullvector nonvanishing inputs below are exactly those exported on the
whole flow tube by `NullTransport.exists_projected_local_positive_amplitude`.
Frame symmetry is supplied by `projectedStress_mem_stressSpace`.
The consumer is conservation of the Hamilton spatial coordinate in
`Canonical.Footpoint` (`app:ch_background:prop:bg-adjoint`,
`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.Footpoint
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase NullTransport

/-- Nonzero selected row and column imply that their crossing entry is
nonzero on the characteristic set. This recovers the minor from the precise
outputs retained by `LocalConstruction` (`app:ch_waves:thm:leading`). -/
theorem selected_minor_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.det = 0) {row col : Fin n}
    (hk : rightNullvector A col ≠ 0) (hl : leftNullvector A row ≠ 0) :
    A.adjugate row col ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, A.adjugate i col ≠ 0 := by
    by_contra! h
    exact hk (funext h)
  obtain ⟨j, hj⟩ : ∃ j, A.adjugate row j ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  have he := minor_mul_adjugate hA hi row j
  intro hz
  change A.adjugate i col * A.adjugate row j = A.adjugate row col * A.adjugate i j at he
  rw [hz, zero_mul] at he
  exact mul_ne_zero hi hj he

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The SAME adapted null direction is a scalar multiple of the actual
Hamilton base velocity. The scalar is explicit; no replacement characteristic
or conservation law is assumed (`app:ch_waves:thm:leading`). -/
theorem carrierTransportDirection_eq_smul_hamiltonVelocity
    (row col : Fin n) {x : Euclidean n} {z : Euclidean 3}
    (ht : (x, (0, T.reference.spatialPatch z)) ∈ (T.currentChart Q).target)
    (hs : ∀ i, (Q.1 x i).IsSymm)
    (hk : carrierNullvector T Q col (x, z) ≠ 0)
    (hl : carrierConullvector T Q row (x, z) ≠ 0) :
    carrierTransportDirection T Q row col (x, z) =
      ((reducedSymbol (Q.1 x) (T.carrierGradient Q x z)).adjugate row col /
        carrierAdaptedDenominator T Q row col (x, z) /
        determinantNormalization (T.carrierGradient Q x z)) •
      (normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp
        (x, T.carrierGradient Q x z) := by
  let ξ := T.carrierGradient Q x z
  have hm : (x, ξ) ∈ normalizedSymbolDomain U :=
    carrierPhase_gradient_mem_domain (T.currentChart Q) T.reference.spatialPatch ht
  have hc : determinant (Q.1 x) ξ = 0 :=
    carrierPhase_normalizedSymbol_determinant_eq_zero hU Q.1 Q.2.1
      (T.currentChart Q) T.reference.spatialPatch ht
  have hk' : rightNullvector (reducedSymbol (Q.1 x) ξ) col ≠ 0 := by
    intro h
    apply hk
    exact (WithLp.toLp_injective 2).eq_iff.mpr h
  have hminor := selected_minor_ne_zero hc hk' hl
  have hnorm : determinantNormalization ξ ≠ 0 := (determinantNormalization_pos hm.2).ne'
  have hhp : (normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp (x, ξ) =
      determinantNormalization ξ • gradient (determinant (Q.1 x)) ξ := by
    change NormalizedSymbol.covectorGradient (normalizedSymbol Q.1) (x, ξ) = _
    rw [NormalizedSymbol.covectorGradient_eq_gradient
      ((contDiffAt_normalizedSymbol (Q.2.1.contDiffAt (hU.mem_nhds hm.1)) hm.2).differentiableAt
        (by simp))]
    simp only [gradient, fderiv_covector_normalizedSymbol_of_determinant_eq_zero Q.1 x hm.2 hc,
      map_smul]
  change carrierTransportDirection T Q row col (x, z) = _ •
    (normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp (x, ξ)
  rw [hhp, smul_smul, div_mul_cancel₀ _ hnorm]
  ext a
  have hg : gradient (determinant (Q.1 x)) ξ a = partialDeriv (determinant (Q.1 x)) ξ a := by
    rw [partialDeriv, ← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp
  change transportField (Q.1 x) (leftNullvector (reducedSymbol (Q.1 x) ξ) row)
      (rightNullvector (reducedSymbol (Q.1 x) ξ) col) a /
      carrierAdaptedDenominator T Q row col (x, z) = _
  rw [transportField_eq_minor_mul_partialDeriv (Q.1 x) hs ξ hc hminor]
  simp only [PiLp.smul_apply, smul_eq_mul, hg, reducedDeterminant_eq_determinant, ξ]
  ring

end JanetCartan.ContinuumAdjoint.Canonical.Footpoint
