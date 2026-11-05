module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.KernelAction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestSpace
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestEnergy.Pairing

/-!
# The fixed source-square energy on compact smooth tests

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the actual bounded
source-tail quadratic form is the difference between the uncut adjoint energy
and the energy with the original source mask. The compact tests lie in the
open auxiliary plateau, permitting removal of its differential factors.
Consumer: `fixedEuclideanChannel_energy_defect_eq_kernel`; extension from
these tests to supported L² inputs is a separate density argument.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison
open SourceTailTestEnergy
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => 𝓢(E, ℂ)
local notation "R²" => EuclideanL2 n E

private theorem inclusion_norm (u : R²) : ‖l2ComplexInclusion volume u‖ = ‖u‖ := by
  apply le_antisymm
  · simpa using (l2ComplexInclusion volume).le_of_opNorm_le
      (l2ComplexInclusion_norm_le volume) u
  · have h := (l2RealPart volume).le_of_opNorm_le (l2RealPart_norm_le volume)
      (l2ComplexInclusion volume u)
    simpa only [JanetCartan.RegularSector.Realization.realPart_inclusion, one_mul] using h

private theorem inclusion_mask_family (hR : 0 < R) (u : R²) (v : Fin n → S)
    (hu : l2ComplexInclusion volume u = imageSchwartzFamilyToLp v) :
    l2ComplexInclusion volume (fixedPhysicalMask hR 2 u) =
      imageSchwartzFamilyToLp (fun j ↦ sourceMask hR (v j)) := by
  have ht := (FixedCutoffs.physical (n := n) hR 2).hasCompactSupport.hasTemperateGrowth
    (FixedCutoffs.physical hR 2).contDiff
  have hc : (fun x : E ↦ (FixedCutoffs.physical hR 2 x : ℂ)).HasTemperateGrowth := by fun_prop
  have hv : l2ComplexInclusion volume u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x) := by
    rw [hu]
    exact imageSchwartzFamilyToLp_ae v
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (fixedPhysicalMask hR 2 u),
    fixedPhysicalMask_coe hR 2 u, euclideanComplexInclusion.coeFn_compLpL u,
    hv, imageSchwartzFamilyToLp_ae (fun j ↦ sourceMask hR (v j))]
    with x hx hm hi hv hw
  change l2ComplexInclusion volume (fixedPhysicalMask hR 2 u) x = _ at hx
  change l2ComplexInclusion volume u x = _ at hi
  rw [hx, hm, map_smul, ← hi, hv, hw]
  ext j
  simp [sourceMask, SchwartzMap.smulLeftCLM_apply_apply hc, Complex.real_smul]

set_option maxHeartbeats 800000 in
/-- On the published compact smooth test space, the fixed bounded source-tail
form equals the literal adjoint energy defect, retaining the original source
square (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). No dimension
positivity or additional analytic assumption is required. -/
theorem fixedSourceTail_energy_eq_inner_of_test (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : u ∈ fixedSourceTailTestInputs hR) :
    ‖(uncutRealChannel A).adjoint u‖ ^ 2 -
      ‖fixedPhysicalMask hR 2 ((uncutRealChannel A).adjoint u)‖ ^ 2 =
        inner ℝ u (fixedSourceTailOperator hR A u) := by
  obtain ⟨g, hg, hgc, hgp, hug⟩ := hu
  have hc (i : Fin n) : HasCompactSupport (fun x : E ↦ (g x i : ℂ)) :=
    hgc.comp_left (g := fun w : E ↦ (w i : ℂ)) (by simp)
  have hs (i : Fin n) : ContDiff ℝ ∞ (fun x : E ↦ (g x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hg)
  let v : Fin n → S := fun i ↦ (hc i).toSchwartzMap (hs i)
  have hv (i : Fin n) : tsupport (v i : E → ℂ) ⊆
      interior {x | FixedCutoffs.physical hR 0 x = 1} :=
    (tsupport_comp_subset (g := fun w : E ↦ (w i : ℂ)) (by simp) g).trans hgp
  have huv : l2ComplexInclusion volume u = imageSchwartzFamilyToLp v := by
    apply Lp.ext
    filter_upwards [euclideanComplexInclusion.coeFn_compLpL u, hug,
      imageSchwartzFamilyToLp_ae v] with x hx hgx hvx
    change l2ComplexInclusion volume u x = _ at hx
    rw [hx, hgx, hvx]
    rfl
  let w : Fin n → S := fun j ↦ imageBesselSchwartzCLM (adjointFactor hR A v j)
  have hw : l2ComplexInclusion volume ((uncutRealChannel A).adjoint u) =
      imageSchwartzFamilyToLp w := by
    rw [uncutRealChannel_adjoint_complexInclusion, huv]
    apply SourceTailTestEnergy.uncutComplexChannel_adjoint_toLp
    intro i x hx
    have hp : x ∈ {y : E | FixedCutoffs.physical hR 0 y = 1} :=
      interior_subset (hv i (subset_tsupport (v i) hx))
    exact hp
  have hwm := inclusion_mask_family hR ((uncutRealChannel A).adjoint u) w hw
  have he := congrArg Complex.re (complexTail_inner hR A v hv)
  change (inner ℂ (complexTail hR A (imageSchwartzFamilyToLp v))
      (imageSchwartzFamilyToLp v)).re =
    (inner ℂ (imageSchwartzFamilyToLp w) (imageSchwartzFamilyToLp w) -
      inner ℂ (imageSchwartzFamilyToLp (fun j ↦ sourceMask hR (w j)))
        (imageSchwartzFamilyToLp (fun j ↦ sourceMask hR (w j)))).re at he
  rw [Complex.sub_re] at he
  simp only [← RCLike.re_to_complex, inner_self_eq_norm_sq] at he
  rw [← hw, ← hwm, inclusion_norm, inclusion_norm] at he
  rw [← he, ← huv, inner_re_symm (𝕜 := ℂ)]
  change (inner ℂ (l2ComplexInclusion volume u)
      (complexTail hR A (l2ComplexInclusion volume u))).re =
    inner ℝ u (l2RealPart volume (complexTail hR A (l2ComplexInclusion volume u)))
  rw [← real_inner_eq_complex_re, ← l2RealPart_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

end JanetCartan.ContinuumNormal.FrozenImageComparison
