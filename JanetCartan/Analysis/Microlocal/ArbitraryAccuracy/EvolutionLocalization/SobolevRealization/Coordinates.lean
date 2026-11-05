module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Input
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Coordinates

/-!
# Measure-preserving realization of completed Cartesian jets

The fixed coordinate map in `app:ch_regular:lem:finite-chain` transports the
actual L² classes, retaining the space/time swap of the kernel construction.
The only hypothesis is preservation of the specified Lebesgue measures.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces FourierIntegral FiniteChain.Graph.KernelLimits

variable {d : ℕ}
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

include hJ

/-- The inverse of the fixed Cartesian coordinate map also preserves the
specified volumes (`app:ch_regular:eq:chain-tail`). -/
theorem graphInputCoordinates_symm_measurePreserving :
    MeasurePreserving (graphInputCoordinates J).symm volume volume :=
  hJ.symm (graphInputCoordinates J).toHomeomorph.toMeasurableEquiv

/-- Pullback from physical scalar L² to the space-first Cartesian L² of
`app:ch_regular:eq:chain-tail`, as an exact isometric equivalence. -/
def scalarCoordinateEquiv :
    Lp ℂ 2 (volume : Measure (Euclidean (d + 1))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (graphInputCoordinates J) hJ) (by
      intro u
      refine ⟨Lp.compMeasurePreserving (graphInputCoordinates J).symm
        (graphInputCoordinates_symm_measurePreserving J hJ) u, ?_⟩
      change Lp.compMeasurePreserving (graphInputCoordinates J) hJ
        (Lp.compMeasurePreserving (graphInputCoordinates J).symm _ u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      simpa only [ContinuousLinearEquiv.symm_comp_self] using
        Lp.compMeasurePreserving_id_apply u)

/-- Pullback has the actual representative required by the graph test identity
in `app:ch_regular:eq:chain-tail`. -/
theorem scalarCoordinateEquiv_apply_ae
    (u : Lp ℂ 2 (volume : Measure (Euclidean (d + 1)))) :
    scalarCoordinateEquiv J hJ u =ᵐ[volume] u ∘ graphInputCoordinates J :=
  Lp.coeFn_compMeasurePreserving u hJ

/-- The inverse coordinate identification has the literal inverse-coordinate
representative (`app:ch_regular:eq:chain-tail`). -/
theorem scalarCoordinateEquiv_symm_apply_ae
    (u : Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ))) :
    (scalarCoordinateEquiv J hJ).symm u =ᵐ[volume] u ∘ (graphInputCoordinates J).symm := by
  have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae_eq_comp
    (scalarCoordinateEquiv_apply_ae J hJ ((scalarCoordinateEquiv J hJ).symm u))
  simpa only [LinearIsometryEquiv.apply_symm_apply, Function.comp_def,
    ContinuousLinearEquiv.apply_symm_apply] using h.symm

/-- The bounded zeroth-jet realization of the classical completion, consumed
by the physical matrix realization in `app:ch_regular:eq:chain-tail`. -/
def physicalZeroJet (m : ℕ) :
    Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean (d + 1))) :=
  (scalarCoordinateEquiv J hJ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (completedJet m (zeroIndex d m))

/-- Zeroth-jet realization is a contraction, with no coordinate or channel
norm loss in `app:ch_regular:eq:chain-tail`. -/
theorem norm_physicalZeroJet_le (m : ℕ)
    (u : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖physicalZeroJet J hJ m u‖ ≤ ‖u‖ := by
  simpa only [physicalZeroJet, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map] using norm_completedJet_le m (zeroIndex d m) u

/-- Exact zeroth-jet representative, including its coordinate swap, in
`app:ch_regular:eq:chain-tail`. -/
theorem physicalZeroJet_apply_ae (m : ℕ)
    (u : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    physicalZeroJet J hJ m u =ᵐ[volume]
      (u.val (zeroIndex d m)) ∘ (graphInputCoordinates J).symm :=
  scalarCoordinateEquiv_symm_apply_ae J hJ _

/-- Test realization uses precisely `f (J.symm y)`, the scalar convention of
`physicalTestField` in `app:ch_regular:eq:chain-tail`. -/
theorem physicalZeroJet_ofTest_ae (m : ℕ) (f : Test d) :
    physicalZeroJet J hJ m (ofTest m volume f) =ᵐ[volume] fun y => f.val (J.symm y) := by
  have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae_eq_comp
    (completedJet_ofTest_ae m (zeroIndex d m) f)
  apply (physicalZeroJet_apply_ae J hJ m _).trans
  filter_upwards [h] with y hy
  have he : Prod.swap ((graphInputCoordinates J).symm y) = J.symm y := by
    apply J.injective
    change graphInputCoordinates J ((graphInputCoordinates J).symm y) = J (J.symm y)
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  change (((graphInputCoordinates J).symm y).2,
    ((graphInputCoordinates J).symm y).1) = J.symm y at he
  simpa [completedJet, jet_zeroIndex, Function.comp_def, he] using hy

/-- The physical L² input is isometrically identified with the actual
order-zero completion (`app:ch_regular:lem:finite-chain`). -/
def scalarInputEquiv :
    Lp ℂ 2 (volume : Measure (Euclidean (d + 1))) ≃ₗᵢ[ℂ]
      Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  (scalarCoordinateEquiv J hJ).trans zeroJetEquiv.symm

/-- The physical input identification inverts the actual zeroth jet
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem scalarInputEquiv_physicalZeroJet
    (u : Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ))) :
    scalarInputEquiv J hJ (physicalZeroJet J hJ 0 u) = u := by
  change zeroJetEquiv.symm (scalarCoordinateEquiv J hJ
    ((scalarCoordinateEquiv J hJ).symm (zeroJetEquiv u))) = u
  simp only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The inverse input identification is the bounded zeroth-jet realization
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem scalarInputEquiv_symm_apply
    (u : Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ))) :
    (scalarInputEquiv J hJ).symm u = physicalZeroJet J hJ 0 u := rfl

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
