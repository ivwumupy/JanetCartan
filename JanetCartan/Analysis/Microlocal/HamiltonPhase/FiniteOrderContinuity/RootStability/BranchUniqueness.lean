module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Stability

/-!
# Identifying independently constructed root branches

The finite-order comparison in `app:lem:common-hamilton-phase` applies to any
actual smooth branch remaining in the common transverse interval. Scalar
uniqueness identifies it, including every ambient derivative, with the branch
produced by `exists_uniform_C1_stable_sectionRoot`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Independently constructed roots on the same transverse interval agree on
the parameter domain (`app:lem:common-hamilton-phase`). -/
theorem root_eqOn_of_gap {f : P × ℝ → ℝ} {g g' : P → ℝ} {U : Set P}
    {l u c : ℝ} (hc : 0 < c)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc l u, DifferentiableAt ℝ f (p, t))
    (hgap : ∀ p ∈ U, ∀ t ∈ Icc l u, c ≤ |scalarDerivative f (p, t)|)
    (hg : ∀ p ∈ U, g p ∈ Icc l u ∧ f (p, g p) = 0)
    (hg' : ∀ p ∈ U, g' p ∈ Icc l u ∧ f (p, g' p) = 0) : EqOn g g' U := by
  intro p hp
  exact scalar_root_unique_of_gap hc (hf p hp) (hgap p hp)
    (hg p hp).1 (hg' p hp).1 (hg p hp).2 (hg' p hp).2

/-- Scalar uniqueness identifies all ambient jets of independently constructed
branches on an open parameter domain. This transports the finite-order estimates
to the actual section-root producer (`app:lem:common-hamilton-phase`). -/
theorem root_jets_eqOn_of_gap {f : P × ℝ → ℝ} {g g' : P → ℝ} {U : Set P}
    (hU : IsOpen U) {l u c : ℝ} (hc : 0 < c)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc l u, DifferentiableAt ℝ f (p, t))
    (hgap : ∀ p ∈ U, ∀ t ∈ Icc l u, c ≤ |scalarDerivative f (p, t)|)
    (hg : ∀ p ∈ U, g p ∈ Icc l u ∧ f (p, g p) = 0)
    (hg' : ∀ p ∈ U, g' p ∈ Icc l u ∧ f (p, g' p) = 0) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n g) (iteratedFDeriv ℝ n g') U := by
  have hEq := root_eqOn_of_gap hc hf hgap hg hg'
  intro p hp
  have he : g =ᶠ[𝓝 p] g' := by
    filter_upwards [hU.mem_nhds hp] with q hq using hEq hq
  exact (he.iteratedFDeriv ℝ n).eq_of_nhds

end JanetCartan.CharacteristicRoot
