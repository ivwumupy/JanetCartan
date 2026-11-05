module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.DirectOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Fourier

/-!
# Absorption of the original output mask

The common output of `RetardedSums` lies in the actual family's plateau.
Dense test realization identifies its composition with each algebraic PDO.
Consumer: the algebraic terms of `selectedFiniteDirectSolver` and
`selectedFiniteDirectResidual` (`energy-complete-residual`, `measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral FullLowBounds LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ

/-- The actual normal-amplitude certificate gives the literal compact-test
realization, used below to identify output multiplication
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem maskedPhysicalPDO_graphTest_realizes
    (χout χsource : E → ℂ) (c : E → E → CMat) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (u : graphTestSpace (d+1) q) :
    maskedPhysicalPDO χout χsource c (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (fun x η ↦ inner ℝ x η)
        (fun x z η ↦ (χout x * χsource z) • c x η) u := by
  rw [maskedPhysicalPDO_eq_vectorTwoPositionL2Operator χout χsource c R M hb]
  refine (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator (Nat.succ_pos d) R _
    hb.smooth hb.support M hb.entry_bound u.val (graphTest_memLp u)
    (fun j ↦ (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) j).restrictScalars ℝ).contDiff.comp
      u.property.1).of_le (by simp))
    (fun j ↦ u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin q) ↦ v j) rfl)).trans ?_
  exact Eventually.of_forall fun x ↦ congrArg (WithLp.toLp 2)
    (canonicalGraph_eq_matrixFullAmplitudeOperator _ hb.smooth M hb.entry_bound u x).symm

/-- Literal output multiplication follows from the source-first graph integral
and uniqueness on dense compact tests. The normal-amplitude certificate is
produced by the algebraic or source budget constructor
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem sourceCutMultiplier_comp_maskedPhysicalPDO
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χout χsource : E → ℂ) (c : E → E → CMat) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M) :
    (sourceCutMultiplier output ho hob).comp (maskedPhysicalPDO χout χsource c) =
      maskedPhysicalPDO (fun y ↦ (output y : ℂ) * χout y) χsource c := by
  symm
  apply fullGraphOperator_eq_of_realizes
  intro u
  filter_upwards [sourceCutMultiplier_coeFn output ho hob
    (maskedPhysicalPDO χout χsource c (graphTestToLp u)),
    maskedPhysicalPDO_graphTest_realizes χout χsource c R M hb u] with y hy ht
  refine hy.trans ?_
  rw [ht]
  change WithLp.toLp 2 ((output y : ℂ) • _) = _
  apply congrArg (WithLp.toLp 2)
  change (output y : ℂ) • graphOperator (fun x η : E ↦ inner ℝ x η)
    (fun x z η ↦ (χout x * χsource z) • c x η) (fun z ↦ (u.val z).ofLp) y = _
  rw [← graphOperator_target_mul _ _ (fun y ↦ (output y : ℂ))]
  congr 1
  funext y z η
  simp only [smul_smul, mul_assoc]

/-- Multiplication pulls back through the actual volume-preserving coordinate
map on Lebesgue L² classes. This is position multiplication only
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem physicalPullbackL2_sourceCutMultiplier
    (i : Fin (d+1)) (a : E → ℝ) (ha : Continuous a) (hab : ∀ y, ‖a y‖ ≤ 1) (u : H) :
    physicalPullbackL2 i (sourceCutMultiplier a ha hab u) =
      sourceCutMultiplier (a ∘ physicalCoordinates i)
        (ha.comp (physicalCoordinates i).continuous) (fun _ ↦ hab _) (physicalPullbackL2 i u) := by
  apply Lp.ext
  have hm := (measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (sourceCutMultiplier_coeFn a ha hab u)
  filter_upwards [physicalPullbackL2_coeFn i (sourceCutMultiplier a ha hab u), hm,
    physicalPullbackL2_coeFn i u,
    sourceCutMultiplier_coeFn (a ∘ physicalCoordinates i) _ _ (physicalPullbackL2 i u)]
    with y hy hm hu hv
  exact hy.trans (hm.trans (by simpa only [Function.comp_apply, hu] using hv.symm))

/-- Conjugation of a chart's output multiplier keeps it on the output side.
Consumer: common-mask absorption in both finite algebraic terms
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem sourceCutMultiplier_comp_physicalOperator
    (i : Fin (d+1)) (a : E → ℝ) (ha : Continuous a) (hab : ∀ y, ‖a y‖ ≤ 1)
    (T : H →L[ℂ] H) :
    (sourceCutMultiplier a ha hab).comp (physicalOperator i T) =
      physicalOperator i ((sourceCutMultiplier (a ∘ physicalCoordinates i)
        (ha.comp (physicalCoordinates i).continuous) (fun _ ↦ hab _)).comp T) := by
  ext1 u
  apply (physicalPullbackL2 i).injective
  simp only [ContinuousLinearMap.comp_apply, physicalOperator_apply,
    physicalPullbackL2_sourceCutMultiplier, LinearIsometryEquiv.apply_symm_apply]

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The original output is one throughout the common smaller output support;
this is the actual plateau field of `ActualMaskFamily`, not an extra premise
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem commonOutput_mul_originalOutput
    (f : ActualMaskFamily Ω x RQ A₀ K M) (output : E → ℝ)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) (y : E) :
    output y * f.outputMask y = output y := by
  by_cases hy : output y = 0
  · rw [hy, zero_mul]
  · rw [show f.outputMask y = 1 from
      (show y ∈ {z : E | f.outputMask z = 1} from
        interior_subset (f.outputMask_plateau (ball_subset_closedBall (hsupp (subset_tsupport _ hy))))),
      mul_one]

/-- Absorb the actual old output after physical conjugation, using its proved
realization. Consumer: each summand of the algebraic solver and residual
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem commonOutput_comp_chartPDO
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (c : E → E → CMat) (R C : ℝ)
    (hb : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) c) R C) :
    (sourceCutMultiplier output ho hob).comp
      (physicalOperator (f.chart p).index
        (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) c)) =
      physicalOperator (f.chart p).index
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) c) := by
  rw [sourceCutMultiplier_comp_physicalOperator,
    sourceCutMultiplier_comp_maskedPhysicalPDO _ _ _ _ _ _ R C hb]
  congr 2
  funext y
  change (output (physicalCoordinates (f.chart p).index y) : ℂ) *
    (f.outputMask (physicalCoordinates (f.chart p).index y) : ℂ) =
      (output (physicalCoordinates (f.chart p).index y) : ℂ)
  exact_mod_cast commonOutput_mul_originalOutput f output hsupp
    (physicalCoordinates (f.chart p).index y)

/-- Both literal algebraic terms use the common output, the original input,
and the identical enlarged threshold. The per-chart certificates are exactly
those returned by `exists_finite_algebraic_pdo_sums`; the parent instantiates
them for its retained Q and B. Consumers: `selectedFiniteDirectSolver` and
`selectedFiniteDirectResidual` (`energy-complete-residual`). -/
theorem selectedFiniteAlgebraicPDO_commonOutput
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1)) (o : Fin 2)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (R p) (C p)) :
    (sourceCutMultiplier output ho hob).comp (selectedFiniteAlgebraicPDO f (2*L) Q B o) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*L) Q B o)) := by
  classical
  ext1 u
  simp only [selectedFiniteAlgebraicPDO, finitePhysicalOperator, ContinuousLinearMap.comp_apply,
    sum_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ ↦
    DFunLike.congr_fun (commonOutput_comp_chartPDO f p output ho hob hsupp _ (R p) (C p) (hb p)) u

end JanetCartan.RegularSector.FiniteAssembly
