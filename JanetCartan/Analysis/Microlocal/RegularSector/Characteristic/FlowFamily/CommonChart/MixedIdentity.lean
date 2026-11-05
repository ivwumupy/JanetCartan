module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseBuffers
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Spatial mixed matrix from the inverse differential

The Liouville phase differential identifies `Ψ_η` with the initial spatial
footpoint. Symmetry of the Hessian therefore identifies `Ψ_{yη}` with the
transpose of the spatial block of the inverse differential. This is the
quantitative mixed-gap consumer of the common inverse chart, for
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic
open FourierIntegral
variable {d : ℕ}

/-- The fixed spatial block extraction, with the Frobenius norm on its matrix
output. Its operator norm depends only on the dimension, and is absorbed in
the common source tolerance (`app:ch_regular_base:lem:retarded-kernel`). -/
def twoTimeInverseMixedExtraction :
    (TwoTimePoint (Euclidean d) →L[ℝ] TwoTimePoint (Euclidean d)) →L[ℝ]
      Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun L i j ↦ (L (0, (0, (EuclideanSpace.single i 1, 0)))).2.2.1 j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Every diagonal shear has identity spatial inverse block. This is the
reference matrix for the actual spatial phase gap
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeInverseMixedExtraction_shear (v : Euclidean d) :
    twoTimeInverseMixedExtraction (twoTimeProjectionEquiv v).symm.toContinuousLinearMap = 1 := by
  ext i j
  change (twoTimeProjectionLinear (-v) (0, (0, (EuclideanSpace.single i 1, 0)))).2.2.1 j = _
  simp [Matrix.one_apply, EuclideanSpace.single, eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The literal mixed phase matrix is extracted from the actual inverse
differential. The full phase differential is produced by
`rootFlow_hasFDerivAt_twoTimePhase`, so no second phase estimate is assumed
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimePhaseMixed_eq_inverseMixedExtraction
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hinv : ContDiffOn ℝ ∞ C.symm C.target)
    (hphase : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target) :
    twoTimePhaseMixed C q = twoTimeInverseMixedExtraction (fderiv ℝ C.symm q) := by
  let F := twoTimePhase C
  have hs := contDiffOn_twoTimePhase hinv
  have hsAt := hs.contDiffAt (C.open_target.mem_nhds hq)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) q :=
    (hsAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  ext i j
  let ei := EuclideanSpace.single i (1 : ℝ)
  let ej := EuclideanSpace.single j (1 : ℝ)
  let Y : TwoTimePoint (Euclidean d) := (0, (0, (ei, 0)))
  let P : TwoTimePoint (Euclidean d) := (0, (0, (0, ej)))
  let Iη : Euclidean d →L[ℝ] TwoTimePoint (Euclidean d) :=
    (0 : Euclidean d →L[ℝ] ℝ).prod ((0 : Euclidean d →L[ℝ] ℝ).prod
      ((0 : Euclidean d →L[ℝ] Euclidean d).prod (ContinuousLinearMap.id ℝ _)))
  let pack := fun η : Euclidean d ↦ (q.1, (q.2.1, (q.2.2.1, η)))
  have hpack (η : Euclidean d) : HasFDerivAt pack Iη η :=
    (hasFDerivAt_const q.1 η).prodMk ((hasFDerivAt_const q.2.1 η).prodMk
      ((hasFDerivAt_const q.2.2.1 η).prodMk (hasFDerivAt_id η)))
  have hnear : ∀ᶠ η in 𝓝 q.2.2.2, pack η ∈ C.target :=
    (hpack q.2.2.2).continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hq)
  have hleft : (fun η ↦ partialDeriv (fun y ↦ F (q.1, (q.2.1, (y, η)))) q.2.2.1 i)
      =ᶠ[𝓝 q.2.2.2] (fun η ↦ fderiv ℝ F (pack η) Y) := by
    filter_upwards [hnear] with η hη
    have hslice : HasFDerivAt (fun y : Euclidean d ↦ (q.1, (q.2.1, (y, η))))
        ((0 : Euclidean d →L[ℝ] ℝ).prod ((0 : Euclidean d →L[ℝ] ℝ).prod
          ((ContinuousLinearMap.id ℝ _).prod (0 : Euclidean d →L[ℝ] Euclidean d))))
        q.2.2.1 :=
      (hasFDerivAt_const q.1 q.2.2.1).prodMk
        ((hasFDerivAt_const q.2.1 q.2.2.1).prodMk
          ((hasFDerivAt_id q.2.2.1).prodMk (hasFDerivAt_const η q.2.2.1)))
    have hd := ((hs.contDiffAt (C.open_target.mem_nhds hη)).differentiableAt
      (by simp)).hasFDerivAt.comp q.2.2.1 hslice
    simp only [Function.comp_def] at hd
    change fderiv ℝ _ q.2.2.1 ei = _
    rw [hd.fderiv]
    rfl
  have hfirst := (ContinuousLinearMap.apply ℝ ℝ Y).hasFDerivAt.comp q hDF.hasFDerivAt
  have hsecond := hfirst.comp q.2.2.2 (hpack q.2.2.2)
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hsecond
  have hmixed : twoTimePhaseMixed C q i j = fderiv ℝ (fderiv ℝ F) q P Y := by
    change fderiv ℝ (fun η ↦ partialDeriv
      (fun y ↦ F (q.1, (q.2.1, (y, η)))) q.2.2.1 i) q.2.2.2 ej = _
    rw [hleft.fderiv_eq, hsecond.fderiv]
    rfl
  rw [hmixed, (hsAt.isSymmSndFDerivAt (by simp)).eq P Y]
  have heta : (fun w ↦ fderiv ℝ F w P) =ᶠ[𝓝 q]
      (fun w ↦ ⟪(C.symm w).2.2.1, ej⟫_ℝ) := by
    filter_upwards [C.open_target.mem_nhds hq] with w hw
    rw [(hphase w hw).fderiv]
    simp [twoTimePhaseDifferential, P]
  have hηfirst := (ContinuousLinearMap.apply ℝ ℝ P).hasFDerivAt.comp q hDF.hasFDerivAt
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hηfirst
  have hcoord := ((hinv.contDiffAt (C.open_target.mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt.snd.snd.fst
  have hfoot := (innerSL ℝ ej).hasFDerivAt.comp q hcoord
  have he : fderiv ℝ (fun w ↦ fderiv ℝ F w P) q =
      (innerSL ℝ ej).comp
        ((ContinuousLinearMap.fst ℝ (Euclidean d) (Euclidean d)).comp
          ((ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d)).comp
            ((ContinuousLinearMap.snd ℝ ℝ (RootState (Euclidean d))).comp
              (fderiv ℝ C.symm q)))) := by
    rw [heta.fderiv_eq]
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using hfoot.fderiv
  have hev := congrArg (fun L : TwoTimePoint (Euclidean d) →L[ℝ] ℝ ↦ L Y) he
  rw [hηfirst.fderiv] at hev
  simpa [twoTimeInverseMixedExtraction, ej, Y, ei, innerSL_apply_apply,
    EuclideanSpace.inner_single_left] using hev

end JanetCartan.RegularSector.Characteristic
