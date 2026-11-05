module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothRealization
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# Smooth physical plus pairing

For `real-sector-normalization` and `sector-theorem-identity`, realize the
literal physical S+cSc on the same compact smooth sources. This preserves
complex linearity and the actual L² class; no anti-real P/i normalization is
used. The concrete application is `SmoothConstruction`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open FourierIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

private def conjugateGraphTest (u : graphTestSpace (d+1) q) : graphTestSpace (d+1) q :=
  ⟨fun y ↦ star (u.val y), (starL' ℝ : F ≃L[ℝ] F).contDiff.comp u.property.1,
    u.property.2.comp_left (map_zero (starL' ℝ : F ≃L[ℝ] F))⟩

private theorem conjugateGraphTest_add (u v : graphTestSpace (d+1) q) :
    conjugateGraphTest (u+v) = conjugateGraphTest u + conjugateGraphTest v := by
  apply Subtype.ext
  funext y
  exact star_add _ _

private theorem conjugateGraphTest_smul (c : ℂ) (u : graphTestSpace (d+1) q) :
    conjugateGraphTest (c • u) = star c • conjugateGraphTest u := by
  apply Subtype.ext
  funext y
  change star (c • u.val y) = star c • star (u.val y)
  exact star_smul c (u.val y)

private theorem graphTestToLp_conjugateGraphTest (u : graphTestSpace (d+1) q) :
    graphTestToLp (conjugateGraphTest u) = star (graphTestToLp u) := by
  apply Lp.ext
  filter_upwards [(graphTest_memLp (conjugateGraphTest u)).coeFn_toLp,
    (graphTest_memLp u).coeFn_toLp, Lp.coeFn_star (graphTestToLp u)] with y hy hu hs
  exact hy.trans ((congrArg star hu).symm.trans hs.symm)

/-- The unique smooth representatives realize the literal physical S+cSc as
one complex linear map, retaining its exact ambient L² implementation
(`real-sector-normalization`, `sector-theorem-solution`). -/
theorem exists_smooth_physical_pair_realization (T : H →L[ℂ] H)
    (S : graphTestSpace (d+1) q →ₗ[ℂ] (E → F))
    (hS : ∀ u, ContDiff ℝ ∞ (S u) ∧ S u =ᵐ[volume] T (graphTestToLp u)) :
    ∃ P : graphTestSpace (d+1) q →ₗ[ℂ] (E → F),
      ∀ u, ContDiff ℝ ∞ (P u) ∧ P u =ᵐ[volume]
        physicalPairedSectorSum {()} (fun _ : Unit ↦ T) (graphTestToLp u) := by
  let P : graphTestSpace (d+1) q →ₗ[ℂ] (E → F) := {
    toFun u := S u + fun y ↦ star (S (conjugateGraphTest u) y)
    map_add' := by
      intro u v
      funext y
      simp only [conjugateGraphTest_add, map_add, Pi.add_apply, star_add]
      abel
    map_smul' := by
      intro c u
      funext y
      simp only [conjugateGraphTest_smul, map_smul, Pi.add_apply, Pi.smul_apply,
        star_smul, star_star, smul_add]
      rfl }
  refine ⟨P, ?_⟩
  intro u
  refine ⟨(hS u).1.add ((starL' ℝ : F ≃L[ℝ] F).contDiff.comp (hS _).1), ?_⟩
  have hc := graphTestToLp_conjugateGraphTest u
  have hs := (hS (conjugateGraphTest u)).2
  rw [hc] at hs
  simp only [physicalPairedSectorSum, Finset.sum_singleton]
  change ∀ᵐ y ∂volume, S u y + star (S (conjugateGraphTest u) y) =
    (T (graphTestToLp u) + star (T (star (graphTestToLp u))) : H) y
  filter_upwards [(hS u).2, hs, Lp.coeFn_star (T (star (graphTestToLp u))),
    Lp.coeFn_add (T (graphTestToLp u)) (star (T (star (graphTestToLp u))))]
    with y hy hz hw ha
  exact (congrArg₂ (· + ·) hy ((congrArg star hz).trans hw.symm)).trans ha.symm

end JanetCartan.RegularSector.FiniteAssembly
