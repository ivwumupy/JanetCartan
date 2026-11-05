module

public import JanetCartan.Iteration.PhysicalSamplingShells.Samples

/-!
# Compatible metric on the literal original refined-shell labels

Native kernel theorems require a metric label space. This concrete metric
retains the ORIGINAL discrete topology, measurable space and shell measure;
it does not alter any sample or introduce a norm constant. Its sole purpose is
to apply the checked native moment and grouped-current theorems to the literal
`RefinedIndex` of `app:ch_mean_pairs:eq:block-bilinear`.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalMean
open RawInputPartition

/-- A metric on the literal retained-label set with its original topology
preserved definitionally. Scoped to mean-kernel applications. -/
scoped instance refinedIndexMetricSpace (J : ℕ) : MetricSpace (RefinedIndex J) := by
  let t : TopologicalSpace (RefinedIndex J) := inferInstance
  let f : RefinedIndex J → ℝ := fun j ↦ ((Fintype.equivFin (RefinedIndex J) j).val : ℝ)
  have hf : Function.Injective f := by
    intro j k h
    apply (Fintype.equivFin (RefinedIndex J)).injective
    apply Fin.ext
    change ((Fintype.equivFin (RefinedIndex J) j).val : ℝ) =
      ((Fintype.equivFin (RefinedIndex J) k).val : ℝ) at h
    exact_mod_cast h
  let mt : MetricSpace (RefinedIndex J) := MetricSpace.induced f hf inferInstance
  have hmt : t = mt.toUniformSpace.toTopologicalSpace := by
    have ht : t = ⊥ := DiscreteTopology.eq_bot
    have hm : mt.toUniformSpace.toTopologicalSpace = ⊥ := by
      let : MetricSpace (RefinedIndex J) := mt
      exact DiscreteTopology.eq_bot
    exact ht.trans hm.symm
  exact mt.replaceTopology hmt

end JanetCartan.PhysicalMean
