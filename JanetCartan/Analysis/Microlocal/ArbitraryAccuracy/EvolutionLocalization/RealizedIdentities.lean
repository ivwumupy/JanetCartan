module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

/-!
# Physical identities for the realized elapsed graph estimate

The Cartesian completion in `Construction` already identifies both the summed
kernel and its regularized compositions. These identities are transported to
the actual spacetime L² realization, without a new operator estimate or phase
regularity assumption. The consumer is `exists_buffered_elapsed_graph_fourier_bound`,
for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization

open FourierIntegral FiniteChain.Graph.KernelLimits RetardedSobolev.Spaces
open Pseudodifferential AmplitudeBound RegularSector.Characteristic.EvolutionIntegral
open SobolevRealization

variable {d q m : ℕ}
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

/-- The constructed matrix extension has the SAME physical summed-kernel
test action after realization in spacetime L². Consumer: the literal elapsed
kernel estimate in `app:ch_regular:eq:chain-tail`. -/
theorem matrixRealization_physical_test_action
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (F : (Fin q → Test d) → Euclidean (d + 1) → Fin q → ℂ)
    (hF : ∀ f a, (matrixOperator Op (completedTestVector 0 f) a).val
      (zeroIndex d m) =ᵐ[volume] fun p => F f (J (p.2, p.1)) a)
    (f : Fin q → Test d) (a : Fin q) :
    finiteL2CoordinateIsometry volume
      (matrixRealization J hJ Op (physicalTestToL2 J hJ f)) a =ᵐ[volume]
        fun x => F f x a := by
  apply (matrixRealization_test_action J hJ Op f a).trans
  have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae_eq_comp
    (hF f a)
  have he (p : (Fin d → ℝ) × ℝ) : J (p.2, p.1) = graphInputCoordinates J p := rfl
  simpa only [Function.comp_def, he, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The physical regularization limit identifies the SAME spacetime operator
as the summed-kernel action, including both independent frequency cutoffs.
Consumer: the original-phase limit in `app:ch_regular:eq:chain-tail`. -/
theorem matrixRealization_physical_regularization_limit
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (R : (Fin q → Test d) → (Finset ℕ × Finset ℕ) → Euclidean (d + 1) → Fin q → ℂ)
    (hR : ∀ f a, ∀ᵐ p ∂volume,
      Tendsto (fun j => R f j (J (p.2, p.1)) a) atTop
        (𝓝 ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m) p)))
    (f : Fin q → Test d) (a : Fin q) :
    ∀ᵐ x ∂volume, Tendsto (fun j => R f j x a) atTop
      (𝓝 (finiteL2CoordinateIsometry volume
        (matrixRealization J hJ Op (physicalTestToL2 J hJ f)) a x)) := by
  have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae
    (hR f a)
  have he (p : (Fin d → ℝ) × ℝ) : J (p.2, p.1) = graphInputCoordinates J p := rfl
  simp only [he, ContinuousLinearEquiv.apply_symm_apply] at h
  filter_upwards [h, matrixRealization_test_action J hJ Op f a] with x hx htest
  simpa only [htest, Function.comp_def] using hx

/-- Dense physical test action determines the bounded spacetime operator
uniquely. In particular the fixed-elapsed operator cannot change with the
Sobolev order or requested accuracy (`app:ch_regular:lem:finite-chain`). -/
theorem eq_of_physical_test_action
    (T U : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (h : ∀ (f : Fin q → Test d) (a : Fin q),
      finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
        finiteL2CoordinateIsometry volume (U (physicalTestToL2 J hJ f)) a) : T = U := by
  apply DFunLike.coe_injective
  apply (denseRange_physicalTestToL2 J hJ).equalizer T.continuous U.continuous
  funext f
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  exact fun a => Lp.ext (h f a)

/-- Strong convergence on physical tests and the independently proved a.e.
regularization limit identify the same bounded operator. The two frequency
cutoffs remain independent in the physical limit; only its cofinal diagonal
is needed for the L² uniqueness argument (`app:ch_regular:eq:chain-tail`).
The finite physical realizations and strong limit are supplied by the actual
graph/localizer identification, without any Fourier Sobolev estimate. -/
theorem eq_of_physical_regularization_limits
    (T U : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (R : (Fin q → Test d) → (Finset ℕ × Finset ℕ) → SpacetimeL2 d q)
    (hT : ∀ f, Tendsto (fun j => R f (Finset.range j, Finset.range j)) atTop
      (𝓝 (T (physicalTestToL2 J hJ f))))
    (hU : ∀ (f : Fin q → Test d) (a : Fin q), ∀ᵐ x ∂volume,
      Tendsto (fun j => finiteL2CoordinateIsometry volume (R f j) a x) atTop
        (𝓝 (finiteL2CoordinateIsometry volume (U (physicalTestToL2 J hJ f)) a x))) :
    T = U := by
  apply eq_of_physical_test_action J hJ T U
  intro f a
  let coord := (PiLp.proj (𝕜 := ℂ) 2
    (fun _ : Fin q => Lp ℂ 2 (volume : Measure (Euclidean (d + 1)))) a).comp
      (finiteL2Coordinates volume)
  have hc := (coord.continuous.tendsto (T (physicalTestToL2 J hJ f))).comp (hT f)
  obtain ⟨σ, hσ, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hc).exists_seq_tendsto_ae
  have hdiag : Tendsto (fun j => (Finset.range j, Finset.range j)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_finset_range.prodMk tendsto_finset_range
  filter_upwards [hsub, hU f a] with x hx hu
  exact tendsto_nhds_unique hx ((hu.comp hdiag).comp hσ.tendsto_atTop)

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
