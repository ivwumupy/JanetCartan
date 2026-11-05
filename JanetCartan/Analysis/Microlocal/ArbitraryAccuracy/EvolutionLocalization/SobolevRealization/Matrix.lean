module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Identification
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic

/-!
# Actual spacetime realization of the completed matrix operator

The Hilbert channel norms in `app:ch_regular:eq:chain-tail` are preserved.
This module constructs the bounded L² operator and proves its exact dense test
action and uniqueness. Higher Fourier regularity is a separate analytic step.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces FourierIntegral FiniteChain.Graph.KernelLimits
open Pseudodifferential AmplitudeBound RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- The actual Hilbert vector of completed Cartesian test channels, used in
`exists_buffered_elapsed_graph_sobolev_bound` (`app:ch_regular:eq:chain-tail`). -/
def completedTestVector (m : ℕ) (f : Fin q → Test d) :
    PiLp 2 (fun _ : Fin q => Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :=
  WithLp.toLp 2 (fun b => ofTest m volume (f b))

/-- The finite family of actual test channels is dense with the Hilbert norm
(`app:ch_regular:lem:finite-chain`). -/
theorem denseRange_completedTestVector (m : ℕ) :
    DenseRange (completedTestVector (d := d) (q := q) m) := by
  exact (PiLp.continuousLinearEquiv 2 ℂ _).symm.surjective.denseRange.comp
    (DenseRange.piMap (fun _ : Fin q => denseRange_ofTest (d := d) m volume))
    (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous

variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

/-- Exact Hilbert input identification from physical spacetime L² to the
completed Cartesian test channels (`app:ch_regular:eq:chain-tail`). -/
def inputEquiv : SpacetimeL2 d q ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Fin q => Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ))) :=
  (finiteL2CoordinateIsometry volume).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => scalarInputEquiv J hJ))

/-- The physical test datum in spacetime L², with exactly the convention of
`physicalTestField` (`app:ch_regular:eq:chain-tail`). -/
def physicalTestToL2 (f : Fin q → Test d) : SpacetimeL2 d q :=
  (inputEquiv J hJ).symm (completedTestVector 0 f)

/-- The physical test datum maps to the precise vector used by the Cartesian
matrix extension (`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem inputEquiv_physicalTestToL2 (f : Fin q → Test d) :
    inputEquiv J hJ (physicalTestToL2 J hJ f) = completedTestVector 0 f :=
  (inputEquiv J hJ).apply_symm_apply _

/-- The input test convention agrees almost everywhere with the literal
`physicalTestField J f`; the channel norm remains Hilbert
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalTestToL2_ae (f : Fin q → Test d) :
    physicalTestToL2 J hJ f =ᵐ[volume] fun y => WithLp.toLp 2 (physicalTestField J f y) := by
  apply (finiteL2CoordinateIsometry_ae_iff _ _ _).mpr
  intro a
  have he : finiteL2CoordinateIsometry volume (physicalTestToL2 J hJ f) a =
      physicalZeroJet J hJ 0 (ofTest 0 volume (f a)) := by
    change (finiteL2CoordinateIsometry volume
      ((finiteL2CoordinateIsometry volume).symm _)) a = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [he]
  exact physicalZeroJet_ofTest_ae J hJ 0 (f a)

/-- The same physical datum in the dense graph test space used by the actual
`EvolutionIntegral` realization (`app:ch_regular:eq:chain-tail`). -/
def physicalGraphTest (f : Fin q → Test d) : graphTestSpace (d + 1) q :=
  ⟨fun y => WithLp.toLp 2 (physicalTestField J f y),
    (contDiff_piLp 2).mpr (fun a => (f a).property.1.comp J.symm.contDiff),
    (hasCompactSupport_physicalTestField J f).comp_left rfl⟩

/-- The input used by the completion bridge is exactly the existing graph
test L² class, allowing the parent's actual test-action theorem to apply
directly (`app:ch_regular:eq:chain-tail`). -/
theorem physicalTestToL2_eq_graphTestToLp (f : Fin q → Test d) :
    physicalTestToL2 J hJ f = graphTestToLp (physicalGraphTest J f) := by
  apply Lp.ext
  exact (physicalTestToL2_ae J hJ f).trans
    (graphTest_memLp (physicalGraphTest J f)).coeFn_toLp.symm

/-- The exact physical test convention is dense in actual spacetime L²
(`app:ch_regular:lem:finite-chain`). -/
theorem denseRange_physicalTestToL2 :
    DenseRange (physicalTestToL2 (q := q) J hJ) :=
  (inputEquiv J hJ).symm.surjective.denseRange.comp (denseRange_completedTestVector 0)
    (inputEquiv J hJ).symm.continuous

/-- Realization of the vector of zeroth jets in the actual spacetime Hilbert
space (`app:ch_regular:eq:chain-tail`). -/
def vectorZeroJet (m : ℕ) :
    PiLp 2 (fun _ : Fin q => Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) →L[ℂ]
      SpacetimeL2 d q :=
  (finiteL2CoordinateIsometry volume).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.piMap (fun _ : Fin q => physicalZeroJet J hJ m)).comp
        (PiLp.continuousLinearEquiv 2 ℂ _).toContinuousLinearMap))

/-- Each coordinate is exactly the scalar zeroth jet, as needed for
`MemVectorFourierSobolev` in `app:ch_regular:eq:chain-tail`. -/
@[simp] theorem vectorZeroJet_coordinates (m : ℕ)
    (u : PiLp 2 (fun _ : Fin q => Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))) :
    finiteL2CoordinateIsometry volume (vectorZeroJet J hJ m u) =
      WithLp.toLp 2 (fun a => physicalZeroJet J hJ m (u a)) :=
  (finiteL2CoordinateIsometry volume).apply_symm_apply _

/-- Extracting all zeroth jets is a contraction for the Hilbert channel norms,
with no dimension factor in `app:ch_regular:eq:chain-tail`. -/
theorem norm_vectorZeroJet_le (m : ℕ)
    (u : PiLp 2 (fun _ : Fin q => Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))) :
    ‖vectorZeroJet J hJ m u‖ ≤ ‖u‖ := by
  rw [← (finiteL2CoordinateIsometry volume).norm_map, vectorZeroJet_coordinates]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (norm_nonneg _)
    (norm_physicalZeroJet_le J hJ m (u a)) 2)

/-- The concrete spacetime realization of the completed matrix extension in
`app:ch_regular:eq:chain-tail`. This definition assumes no Fourier bound. -/
def matrixRealization {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q :=
  (vectorZeroJet J hJ m).comp ((matrixOperator Op).comp
    (inputEquiv J hJ).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The actual L² realization retains the full matrix operator bound, without
entrywise or channel losses (`app:ch_regular:eq:chain-tail`). -/
theorem norm_matrixRealization_apply_le {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) (u : SpacetimeL2 d q) :
    ‖matrixRealization J hJ Op u‖ ≤ ‖matrixOperator Op‖ * ‖u‖ := by
  change ‖vectorZeroJet J hJ m (matrixOperator Op (inputEquiv J hJ u))‖ ≤ _
  exact (norm_vectorZeroJet_le J hJ m _).trans (by
    simpa only [LinearIsometryEquiv.norm_map] using
      (matrixOperator Op).le_opNorm (inputEquiv J hJ u))

/-- Operator norm version of the lossless L² realization estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_matrixRealization_le {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖matrixRealization J hJ Op‖ ≤ ‖matrixOperator Op‖ :=
  (matrixRealization J hJ Op).opNorm_le_bound (norm_nonneg _)
    (norm_matrixRealization_apply_le J hJ Op)

/-- Exact vector of zeroth jets on the dense physical tests, before choosing
representatives (`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem matrixRealization_physicalTestToL2 {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) (f : Fin q → Test d) :
    matrixRealization J hJ Op (physicalTestToL2 J hJ f) =
      vectorZeroJet J hJ m (matrixOperator Op (completedTestVector 0 f)) := by
  change vectorZeroJet J hJ m (matrixOperator Op (inputEquiv J hJ _)) = _
  rw [inputEquiv_physicalTestToL2]

/-- The physical test action of the actual spacetime realization, with the
literal zeroth-jet representatives from the Cartesian constructor
(`app:ch_regular:eq:chain-tail`). -/
theorem matrixRealization_test_action {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) (f : Fin q → Test d) (a : Fin q) :
    finiteL2CoordinateIsometry volume
        (matrixRealization J hJ Op (physicalTestToL2 J hJ f)) a =ᵐ[volume]
      ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) ∘
        (graphInputCoordinates J).symm := by
  rw [matrixRealization_physicalTestToL2, vectorZeroJet_coordinates]
  exact physicalZeroJet_apply_ae J hJ m _

/-- Any bounded spacetime operator with the exact dense test action is the
constructed realization. The actual graph/test-action constructor supplies
`hT`; no regularity or Fourier estimate of `T` is a hypothesis
(`app:ch_regular:eq:chain-tail`). -/
theorem eq_matrixRealization_of_test_action {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ (f : Fin q → Test d) (a : Fin q),
      finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
        ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) ∘
          (graphInputCoordinates J).symm) : T = matrixRealization J hJ Op := by
  apply DFunLike.coe_injective
  apply (denseRange_physicalTestToL2 J hJ).equalizer T.continuous
    (matrixRealization J hJ Op).continuous
  funext f
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro a
  exact Lp.ext ((hT f a).trans (matrixRealization_test_action J hJ Op f a).symm)

/-- Pulling the realized test output back to Cartesian coordinates recovers
exactly the zeroth completed jet from `exists_buffered_elapsed_graph_sobolev_bound`
(`app:ch_regular:eq:chain-tail`). -/
theorem matrixRealization_test_action_cartesian {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) (f : Fin q → Test d) (a : Fin q) :
    (fun p : (Fin d → ℝ) × ℝ =>
      finiteL2CoordinateIsometry volume
        (matrixRealization J hJ Op (physicalTestToL2 J hJ f)) a (J (p.2, p.1))) =ᵐ[volume]
      (matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m) := by
  have h := hJ.quasiMeasurePreserving.ae_eq_comp (matrixRealization_test_action J hJ Op f a)
  simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] at h
  simpa only [graphInputCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodComm_apply, Prod.swap] using h

/-- Cartesian a.e. test identities suffice to identify any bounded actual
spacetime operator. These are the exact identities supplied by the parent's
physical graph construction; no Fourier bound is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem eq_matrixRealization_of_cartesian_test_action {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ (f : Fin q → Test d) (a : Fin q),
      (fun p : (Fin d → ℝ) × ℝ =>
        finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a (J (p.2, p.1))) =ᵐ[volume]
        (matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) :
    T = matrixRealization J hJ Op := by
  apply eq_matrixRealization_of_test_action J hJ Op T
  intro f a
  have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae_eq_comp
    (hT f a)
  have he (p : (Fin d → ℝ) × ℝ) : J (p.2, p.1) = graphInputCoordinates J p := rfl
  simpa only [Function.comp_def, he, ContinuousLinearEquiv.apply_symm_apply] using h

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
