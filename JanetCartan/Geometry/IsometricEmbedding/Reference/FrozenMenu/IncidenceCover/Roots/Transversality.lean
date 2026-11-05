module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CubeGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.Shrinking.Regularity
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Patch

/-!
# Joint incidence derivatives and uniform transversality

Smoothness, partial derivative identities, and compactness preserve the derivative
bound on a fixed closed parameter cube in Step 4 of
`app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.FrozenMenu

/-- The incidence equation is jointly smooth in covector and patch parameters at
every point of the closed cube (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.contDiffAt_joint_incidence {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    (q : Euclidean n) {z : Euclidean 3} (hz : z ∈ parameterCube P.radius) :
    ContDiffAt ℝ ∞ (fun p : Euclidean n × Euclidean 3 ↦ incidence p.1 (P.toFun p.2))
      (q, z) := by
  have hf := hP.2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds
    (parameterCube_subset_doubledInterior hP.1 hz))
  have hn := (contDiffAt_normal_of_coordinates_ne_zero (hP.2.2.2.2.1 z hz).1).comp z hf
  exact ContDiffAt.sum fun i _ ↦
    ((contDiffAt_piLp_apply (p := 2)).comp (q, z) contDiffAt_fst).mul
      (((contDiffAt_piLp 2).mp hn i).comp (q, z) contDiffAt_snd)

/-- The parameter derivative of incidence is the second partial derivative of
the joint equation (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.fderiv_incidence_eq_joint {n : ℕ} {P : Patch n} {q : Euclidean n} {z : Euclidean 3}
    (h : DifferentiableAt ℝ
      (fun p : Euclidean n × Euclidean 3 ↦ incidence p.1 (P.toFun p.2)) (q, z)) :
    fderiv ℝ (fun w ↦ incidence q (P.toFun w)) z =
      (fderiv ℝ (fun p : Euclidean n × Euclidean 3 ↦ incidence p.1 (P.toFun p.2))
        (q, z)).comp (ContinuousLinearMap.inr ℝ _ _) := by
  have hg := (hasFDerivAt_const (𝕜 := ℝ) q z).prodMk (hasFDerivAt_id z)
  have he := (h.hasFDerivAt.comp z hg).fderiv
  change fderiv ℝ (fun w ↦ incidence q (P.toFun w)) z = _ at he
  rw [he]
  congr 1

/-- Compactness preserves half the incidence derivative margin on the entire
closed parameter cube for every nearby covector. The patch and its radius stay
fixed (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.eventually_uniform_incidence_bound {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {k : Euclidean n}
    (hb : ∀ z ∈ parameterCube P.radius,
      c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) :
    ∀ᶠ q in 𝓝 k, ∀ z ∈ parameterCube P.radius,
      c / 2 ≤ |fderiv ℝ (fun w ↦ incidence q (P.toFun w)) z (EuclideanSpace.single 0 1)| := by
  let F := fun p : Euclidean n × Euclidean 3 ↦ incidence p.1 (P.toFun p.2)
  let D := fun p ↦ fderiv ℝ F p (0, EuclideanSpace.single 0 1)
  have hD : ∀ᶠ q in 𝓝 k, ∀ z ∈ parameterCube P.radius, c / 2 < |D (q, z)| := by
    apply (isCompact_parameterCube P.radius).eventually_forall_of_forall_eventually
    intro z hz
    have hcont : ContinuousAt D (k, z) :=
      ((Patch.contDiffAt_joint_incidence hP k hz).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const
    apply hcont.abs.eventually (eventually_gt_nhds _)
    have he := Patch.fderiv_incidence_eq_joint
      ((Patch.contDiffAt_joint_incidence hP k hz).differentiableAt (by simp))
    have hbz := hb z hz
    rw [he] at hbz
    change c ≤ |D (k, z)| at hbz
    exact (half_lt_self hP.2.1).trans_le hbz
  filter_upwards [hD] with q hq z hz
  rw [Patch.fderiv_incidence_eq_joint
    ((Patch.contDiffAt_joint_incidence hP q hz).differentiableAt (by simp))]
  exact (hq z hz).le

/-- Varying only coordinate zero gives a jointly smooth scalar incidence
equation (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.contDiffAt_scalar_incidence {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    (q : Euclidean n) {t : ℝ}
    (ht : t • EuclideanSpace.single 0 1 ∈ parameterCube P.radius) :
    ContDiffAt ℝ ∞ (fun p : Euclidean n × ℝ ↦
      incidence p.1 (P.toFun (p.2 • EuclideanSpace.single 0 1))) (q, t) := by
  have hg : ContDiffAt ℝ ∞ (fun p : Euclidean n × ℝ ↦
      (p.1, p.2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) (q, t) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.smul contDiffAt_const)
  have hcomp := (Patch.contDiffAt_joint_incidence hP q ht).comp (q, t) hg
  exact hcomp

/-- The scalar partial derivative is exactly the first-parameter incidence
derivative (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.scalarDerivative_incidence_eq {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    (q : Euclidean n) {t : ℝ}
    (ht : t • EuclideanSpace.single 0 1 ∈ parameterCube P.radius) :
    CharacteristicRoot.scalarDerivative (fun p : Euclidean n × ℝ ↦
      incidence p.1 (P.toFun (p.2 • EuclideanSpace.single 0 1))) (q, t) =
    fderiv ℝ (fun w ↦ incidence q (P.toFun w))
      (t • EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) := by
  have hd := (Patch.contDiffAt_joint_incidence hP q ht).differentiableAt (by simp)
  have hg := (hasFDerivAt_fst (𝕜 := ℝ) (p := (q, t))).prodMk
    (hasFDerivAt_snd.smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
  unfold CharacteristicRoot.scalarDerivative
  have he := (hd.hasFDerivAt.comp (q, t) hg).fderiv
  dsimp only [Function.comp_def] at he
  rw [he, Patch.fderiv_incidence_eq_joint hd]
  simp

end JanetCartan.FrozenMenu
