module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorFirstDerivative
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakLimits

/-!
# Weak derivative of the normalized physical pair

The actual half-sum constructor supplies order-one membership on compact
smooth tests. Pair its two genuine weak derivatives, keeping literal physical
conjugation and the original Lebesgue class (`energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.NormalizedSolver
open FourierIntegral Pseudodifferential LocalSobolev
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Construct the weak derivative of the literal physical pair from the
half-sum's proved order-one estimate on graph tests. This is consumed by
the same-family weak equation, with `T` the actual normalized half-sum
(`sector-theorem-identity`, `energy-complete-residual`). -/
theorem exists_physicalPair_firstWeakDerivative
    (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace (d+1) q,
      MemVectorFourierSobolev 1 (T (graphTestToLp u)))
    (u : graphTestSpace (d+1) q) :
    ∃ D : E → E →L[ℝ] (Fin q → ℂ),
      Mollification.HasWeakFDerivOn volume
        (fun y ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ T) (graphTestToLp u) y).ofLp)
        D univ ∧ MemLp D 2 volume := by
  let uc : graphTestSpace (d+1) q :=
    ⟨fun y ↦ star (u.val y), (starL' ℝ : F ≃L[ℝ] F).contDiff.comp u.property.1,
      u.property.2.comp_left (map_zero (starL' ℝ : F ≃L[ℝ] F))⟩
  have he : graphTestToLp uc = star (graphTestToLp u) := by
    apply Lp.ext
    filter_upwards [(graphTest_memLp uc).coeFn_toLp,
      (graphTest_memLp u).coeFn_toLp, Lp.coeFn_star (graphTestToLp u)] with y hc hu hs
    exact hc.trans ((congrArg star hu).symm.trans hs.symm)
  have hc := hT uc
  rw [he] at hc
  obtain ⟨Dv, hvD, hvm, _⟩ := exists_vector_firstWeakDerivative _ (hT u)
  obtain ⟨Dw, hwD, hwm, _⟩ := exists_vector_firstWeakDerivative _ hc
  let C : F →L[ℝ] F := (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap
  let P : F →L[ℝ] (Fin q → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).toContinuousLinearMap
  have hd := (hvD.add_univ (hwD.comp_clm_univ C)).comp_clm_univ P
  refine ⟨fun y ↦ P.comp (Dv y + C.comp (Dw y)), ?_, ?_⟩
  · apply hd.congr_ae _ Filter.EventuallyEq.rfl
    rw [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_add (T (graphTestToLp u)) (star (T (star (graphTestToLp u)))),
      Lp.coeFn_star (T (star (graphTestToLp u)))] with y ha hs
    change (T (graphTestToLp u) y + star (T (star (graphTestToLp u)) y)).ofLp = _
    simp only [physicalPairedSectorSum, Finset.sum_singleton]
    change _ = (((T (graphTestToLp u) + star (T (star (graphTestToLp u)))) : H) y).ofLp
    rw [ha]
    simp only [Pi.add_apply, hs, Pi.star_apply]
  · exact ((ContinuousLinearMap.compL ℝ E F (Fin q → ℂ)) P).comp_memLp'
      (hvm.add (((ContinuousLinearMap.compL ℝ E F F) C).comp_memLp' hwm))

end JanetCartan.RegularSector.NormalizedSolver
