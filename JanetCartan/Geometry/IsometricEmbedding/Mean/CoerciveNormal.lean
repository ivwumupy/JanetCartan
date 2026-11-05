module

public import JanetCartan.Analysis.Operator.CoerciveInverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs

/-!
# The canonical inverse on the continuum row's physical core

Identify the exterior component of the existing `CoerciveInverse.rightInverse`
and realize its physical equation on the original core. These statements use
the literal augmented row, so no second inverse or independent choice of masks
is introduced. The positive gap in the physical equation must be supplied by
the same-row coercivity producer; it is not constructed here.

Consumers: `PositiveBackground.PhysicalCorrection`, `AuxiliaryRealization`
and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.CoerciveNormal
open ContinuumRow PeriodicLocalL2 AmplitudeBound

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The exterior component of the canonical inverse is exactly the original
exterior multiplier applied to the SAME normal inverse
(`app:ch_background:prop:bg-inverse`). -/
theorem rightInverse_exterior_eq (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (e : OutputL2 n) :
    (CoerciveInverse.rightInverse (augmentedRow image V ψ) e).snd =
      exteriorChannel ψ ((augmentedNormal image V ψ).inverse e) := by
  change ((augmentedRow image V ψ).adjoint ((augmentedNormal image V ψ).inverse e)).snd = _
  rw [augmentedRow_adjoint_apply]
  rfl

/-- The exterior input itself vanishes on the fixed physical core; no gap or
regularity assumption is needed for this support assertion
(`app:ch_background:prop:bg-inverse`). -/
theorem rightInverse_exterior_zero_on_core (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) (e : OutputL2 n) :
    ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ Metric.closedBall 0 r →
      (CoerciveInverse.rightInverse
        (augmentedRow image V (FixedCutoffs.periodic hr hcell 0)) e).snd x = 0 := by
  rw [rightInverse_exterior_eq]
  exact FixedCutoffs.exterior_zero_on_core hr hcell _

/-- The canonical input solves the physical row equation on the SAME core.
The displayed adjoint gap is precisely the remaining `both-normal-coercivity`
output, not a separate physical solvability hypothesis
(`app:ch_background:prop:bg-inverse`). -/
theorem rightInverse_physicalRow_on_core (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ w, γ * ‖w‖ ^ 2 ≤
      ‖(augmentedRow image V (FixedCutoffs.periodic hr hcell 0)).adjoint w‖ ^ 2)
    (e : OutputL2 n) :
    ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ Metric.closedBall 0 r →
      physicalRow image V (CoerciveInverse.rightInverse
        (augmentedRow image V (FixedCutoffs.periodic hr hcell 0)) e).fst x = e x := by
  let ψ := FixedCutoffs.periodic (n := n) hr hcell 0
  let raw := CoerciveInverse.rightInverse (augmentedRow image V ψ) e
  have heq : physicalRow image V raw.fst + exteriorChannel ψ raw.snd = e := by
    simpa only [augmentedRow_apply] using
      CoerciveInverse.apply_rightInverse (augmentedRow image V ψ) hγ hgap e
  have hae := Lp.coeFn_add (physicalRow image V raw.fst) (exteriorChannel ψ raw.snd)
  rw [heq] at hae
  filter_upwards [hae, FixedCutoffs.exterior_zero_on_core hr hcell raw.snd] with x hx hext
  intro hcore
  change e x = physicalRow image V raw.fst x + exteriorChannel ψ raw.snd x at hx
  have hz : exteriorChannel ψ raw.snd x = 0 := hext hcore
  rw [hz, add_zero] at hx
  exact hx.symm

end JanetCartan.CoerciveNormal
