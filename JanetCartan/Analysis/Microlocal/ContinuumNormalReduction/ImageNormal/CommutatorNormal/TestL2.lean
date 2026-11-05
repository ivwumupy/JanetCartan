module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.TestOperator
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.CompactSchwartz
/-!
# Vector Schwartz tests in Euclidean Lebesgue L²

The actual test inclusion, pairing, and density used to identify the literal
Hilbert adjoint of the source commutator in
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)
local notation "S" => 𝓢(E, ℂ)

/-- Coordinatewise inclusion of the actual Schwartz tests into vector Lebesgue
L² (`app:ch_background:prop:bg-frame`, Step 1). -/
def imageSchwartzFamilyToLp : (Fin d → S) →L[ℂ] V² :=
  (finiteL2CoordinateIsometry (volume : Measure E)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦ (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)).comp (ContinuousLinearMap.proj i)))

/-- The test inclusion uses the existing finite-coordinate isometry exactly
(`app:ch_background:prop:bg-frame`, Step 1). -/
@[simp] theorem imageSchwartzFamilyToLp_coordinates (v : Fin d → S) :
    finiteL2CoordinateIsometry (volume : Measure E) (imageSchwartzFamilyToLp v) =
      WithLp.toLp 2 (fun i ↦ (v i).toLp 2) :=
  (finiteL2CoordinateIsometry volume).apply_symm_apply _

/-- The vector representative is the original family of tests
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSchwartzFamilyToLp_ae (v : Fin d → S) :
    imageSchwartzFamilyToLp v =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦ v i x) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  rw [imageSchwartzFamilyToLp_coordinates]
  exact (v i).coeFn_toLp 2

/-- The vector inner product is exactly the sum of the literal scalar
Lebesgue pairings (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSchwartzFamilyToLp_inner (u v : Fin d → S) :
    inner ℂ (imageSchwartzFamilyToLp u) (imageSchwartzFamilyToLp v) =
      ∑ i, imageSchwartzPairing (u i) (v i) := by
  rw [← (finiteL2CoordinateIsometry (volume : Measure E)).inner_map_map,
    imageSchwartzFamilyToLp_coordinates, imageSchwartzFamilyToLp_coordinates, PiLp.inner_apply]
  rfl

/-- Schwartz families are dense in the actual vector L² space, for the
literal adjoint identification (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem denseRange_imageSchwartzFamilyToLp : DenseRange (imageSchwartzFamilyToLp (d := d)) := by
  have hs : DenseRange (fun v : Fin d → S ↦ fun i ↦ (v i).toLp 2 (volume : Measure E)) :=
    DenseRange.piMap (fun _ ↦ SchwartzMap.denseRange_toLpCLM (by norm_num))
  have hp := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d ↦ Lp ℂ 2 (volume : Measure E))).symm.surjective.denseRange
  have hv := (finiteL2CoordinateIsometry (volume : Measure E) (I := Fin d)).symm.surjective.denseRange
  exact hv.comp (hp.comp hs (by fun_prop)) (by fun_prop)

/-- A compact-test identity of continuous Schwartz operators extends to all
Schwartz tests by the proved expanding truncations. This is consumed by the
full commutator realization (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSchwartzFamilyToLp_extend_compact
    (T : V² →L[ℂ] V²) (F : (Fin d → S) →L[ℂ] (Fin d → S))
    (hT : ∀ v : Fin d → S, (∀ i, HasCompactSupport (v i : E → ℂ)) →
      T (imageSchwartzFamilyToLp v) = imageSchwartzFamilyToLp (F v)) (v : Fin d → S) :
    T (imageSchwartzFamilyToLp v) = imageSchwartzFamilyToLp (F v) := by
  have ht : Tendsto (fun k i ↦ CompactSchwartz.truncate (v i) k) atTop (𝓝 v) :=
    tendsto_pi_nhds.mpr (fun i ↦ CompactSchwartz.tendsto_truncate (v i))
  have hl := (T.continuous.comp imageSchwartzFamilyToLp.continuous).continuousAt.tendsto.comp ht
  have hr := (imageSchwartzFamilyToLp.continuous.comp F.continuous).continuousAt.tendsto.comp ht
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun k ↦
    (hT _ (fun i ↦ CompactSchwartz.truncate_hasCompactSupport (v i) k)).symm)

end JanetCartan.ContinuumNormalReduction.ImageNormal
