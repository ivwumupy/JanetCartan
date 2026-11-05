module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds

/-!
# Original coefficient budgets for the retained conic phase

`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes` publishes
`hbuffer`, `hs`, and `hphase` for the same `C`. We apply the normalized compact
jet theorem to these exact outputs. Constants use only the fixed section,
buffers and original `phaseCost`, so precede the varying coefficient field.
The shift is one, and the fixed low coefficient order also reserves the ten
derivatives required by the amplitude producer.

Consumers: the low and single-high phase inputs in
`EvolutionIntegral.exists_retardedOperator_signed_integer_bounds_of_primitive_data`,
for `app:ch_regular_base:lem:retarded-kernel` and `energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase FourierIntegral EvolutionIntegral SymbolBudgets
open WholeImageGeometry FullLowBounds
variable {d : ℕ}
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- One finite original coefficient order for both signed retarded factors.
It precedes every requested Sobolev order and accuracy. The amplitude reserves
are ten in `Q` and nine in `B` (`app:ch_regular_base:lem:retarded-kernel`). -/
def retardedCoefficientOrder (d : ℕ) : ℕ :=
  max (wholeImagePhaseReserve (d + 1) + 1) (fullLowReserve (d + 1) + 11)

/-- The fixed order covers the original constructor and both low symbol orders. -/
theorem retardedCoefficientOrder_bounds {o : ℕ} (ho : o = 0 ∨ o = 1) :
    10 ≤ retardedCoefficientOrder d ∧ 9 ≤ retardedCoefficientOrder d ∧
    fullLowReserve (d + 1) + o + 10 ≤ retardedCoefficientOrder d ∧
    max (wholeImagePhaseReserve (d + 1)) (fullLowReserve (d + 1) + o + 2) + 1 ≤
      retardedCoefficientOrder d := by
  unfold retardedCoefficientOrder
  rcases ho with rfl | rfl <;> omega

/-- The constant for the retained phase uses the original uniform phase cost,
with no dependence on the varying coefficient field (`retarded-kernel`). -/
def retainedPhaseCost (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε ra rb : ℝ)
    (phaseCost : ℕ → ℝ) (m : ℕ) : ℝ :=
  jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε ra rb) m * phaseCost m

/-- Positivity of the same fixed phase constants. -/
theorem retainedPhaseCost_pos (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε ra rb : ℝ)
    {phaseCost : ℕ → ℝ} (hphaseCost : ∀ m, 0 < phaseCost m) (m : ℕ) :
    0 < retainedPhaseCost ℓ z ε ra rb phaseCost m :=
  mul_pos (jetBoundConstant_pos _ _ _) (hphaseCost m)

/-- Normalized phase budgets from the literal coefficient-to-chart estimate
retained by `UniformAmplitudes.ConicConstruction`. The normalization uses the
same `ℓ`, every radial scale, and derivative shift one (`retarded-kernel`). -/
theorem normalized_retained_phase_coefficient_bound
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : Z} {ε ra rb b : ℝ}
    (hε : 0 ≤ ε) (hra : 0 < ra) (hεb : 2 * ε ≤ b)
    {C : OpenPartialHomeomorph T T}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (KQ : Set E) (Q : E → Fin (d + 1) → Mat) (phaseCost : ℕ → ℝ)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m + 1) Q))
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    cNorm (bufferedJetSet ℓ z ε ra rb) m
      (jointPhase (normalizedTwoTimePhase R (curriedPhase ℓ C))) ≤
        retainedPhaseCost ℓ z ε ra rb phaseCost m * (1 + cNorm KQ (m + 1) Q) := by
  have hn := bufferedJetSet_normalizes ℓ (z := z) (b := rb) hε hra
  have hmap : MapsTo (ConicPhase.normalize ℓ ∘ budgetCoordinates)
      (bufferedJetSet ℓ z ε ra rb) (closedBall (z.1, z) b) :=
    fun _ hp ↦ closedBall_subset_closedBall hεb (hn.2 hp)
  exact (cNorm_normalizedTwoTimePhase_phase_le ℓ C hs
    (isCompact_bufferedJetSet ℓ z ε ra rb) (isCompact_closedBall _ _) hbuffer
    hn.1 hmap hR m).trans (by
      simpa only [retainedPhaseCost, mul_assoc] using
        mul_le_mul_of_nonneg_left (hphase m) (jetBoundConstant_pos ℓ
          (budgetCoordinates '' bufferedJetSet ℓ z ε ra rb) m).le)

/-- The unnormalized phase has the same coefficient bound. This is exactly
the high phase seminorm in the positive and negative integer estimates
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem retained_phase_coefficient_bound
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : Z} {ε ra rb b : ℝ}
    (hε : 0 ≤ ε) (hra : 0 < ra) (hεb : 2 * ε ≤ b)
    {C : OpenPartialHomeomorph T T}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (KQ : Set E) (Q : E → Fin (d + 1) → Mat) (phaseCost : ℕ → ℝ)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m + 1) Q)) (m : ℕ) :
    cNorm (bufferedJetSet ℓ z ε ra rb) m (jointPhase (curriedPhase ℓ C)) ≤
      retainedPhaseCost ℓ z ε ra rb phaseCost m * (1 + cNorm KQ (m + 1) Q) := by
  have h := normalized_retained_phase_coefficient_bound ℓ hε hra hεb hbuffer hs
    KQ Q phaseCost hphase (rb := rb) (R := 1) zero_lt_one m
  simpa only [show curriedPhase ℓ C = curriedExtend ℓ (twoTimePhase C) from rfl,
    normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) zero_lt_one] using h

/-- One fixed original coefficient norm supplies the entire low phase reserve
for both order-zero solver and order-minus-one residual. There is no all-order
low norm assumption (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem retained_phase_low_bound
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : Z} {ε ra rb b : ℝ}
    (hε : 0 ≤ ε) (hra : 0 < ra) (hεb : 2 * ε ≤ b)
    {C : OpenPartialHomeomorph T T}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (KQ : Set E) (Q : E → Fin (d + 1) → Mat) (phaseCost : ℕ → ℝ)
    (hphaseCost : ∀ m, 0 < phaseCost m)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m + 1) Q))
    {M : ℝ} (hQ : cNorm KQ (retardedCoefficientOrder d) Q ≤ M)
    {o : ℕ} (ho : o = 0 ∨ o = 1) :
    let n := max (wholeImagePhaseReserve (d + 1)) (fullLowReserve (d + 1) + o + 2)
    cNorm (bufferedJetSet ℓ z ε ra rb) n (jointPhase (curriedPhase ℓ C)) ≤
      retainedPhaseCost ℓ z ε ra rb phaseCost n * (1 + M) := by
  dsimp only
  apply (retained_phase_coefficient_bound ℓ hε hra hεb hbuffer hs KQ Q phaseCost
    hphase _).trans
  apply mul_le_mul_of_nonneg_left _ (retainedPhaseCost_pos ℓ z ε ra rb hphaseCost _).le
  exact add_le_add le_rfl ((cNorm_mono_order
    (retardedCoefficientOrder_bounds ho).2.2.2).trans hQ)

/-- The degree-zero mixed derivative has a coefficient bound on a FIXED
unit section band, before choosing the whole-image source annulus. Its only
coefficient order is three. This supplies the separate `Bmix` input of
`exists_elapsedGraphFamily_of_primitive_phase` without a circular choice of
annulus and phase jet budget (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem retained_mixed_coefficient_bound
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : Z} {ε b : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b)
    {C : OpenPartialHomeomorph T T}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (KQ : Set E) (Q : E → Fin (d + 1) → Mat) (phaseCost : ℕ → ℝ)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m + 1) Q))
    {r : ℝ} (hr : r ∈ Icc 0 ε) {x : E} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 (ε / 2)) :
    ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
      (fun p : ℝ × ℝ × Euclidean d ↦ curriedPhase ℓ C p.1 p.2.1 p.2.2 ζ)
      (x 0, x 0 - r, spatialPart x)) η‖ ≤
        retainedPhaseCost ℓ z ε (1 / 2) 2 phaseCost 2 * (1 + cNorm KQ 3 Q) := by
  let J := bufferedJetSet ℓ z ε (1 / 2) 2
  let U := budgetCoordinates ⁻¹' domain ℓ C.target
  have hU : IsOpen U := (isOpen_domain ℓ C.open_target).preimage budgetCoordinates.continuous
  have hn := bufferedJetSet_normalizes ℓ (z := z) (b := (2 : ℝ)) hε.le
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hJU : J ⊆ U := fun p hp ↦
    ⟨hn.1 p hp, hbuffer (closedBall_subset_closedBall hεb (hn.2 hp))⟩
  have hphaseU : ContDiffOn ℝ ∞ (jointPhase (curriedPhase ℓ C)) U :=
    contDiffOn_jointPhase_curriedExtend ℓ C.open_target hs
  have hbound := norm_twoTimePhase_mixed_le_of_normalized_cover (curriedPhase ℓ C)
    (show IsOpen (bufferedBase z ε) from isOpen_ball)
    (isOpen_angularCone ℓ z.2.2 ε)
    (fun t ht η hη ↦ smul_mem_angularCone hη ht)
    (contDiffOn_retained_product ℓ hε hεb hbuffer hs)
    (fun t ht p _ η _ ↦ extend_smul ℓ (twoTimePhase C)
      (p.1, (p.2.1, (p.2.2, η))) ht)
    (isCompact_bufferedJetSet ℓ z ε (1 / 2) 2) hU hJU hphaseU
    (elapsed_mem_bufferedBase hε hr hx)
    (retained_normalized_representative ℓ hε (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 2) hr hx hη) (le_refl 2)
  exact hbound.trans (retained_phase_coefficient_bound ℓ hε.le
    (by norm_num : (0 : ℝ) < 1 / 2) hεb hbuffer hs KQ Q phaseCost hphase 2)

end JanetCartan.RegularSector.Characteristic.UniformEvolution
