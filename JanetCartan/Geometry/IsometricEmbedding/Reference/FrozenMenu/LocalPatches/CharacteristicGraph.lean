module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Patch

/-!
# Characteristic graphs with a prescribed tangent frame

The implicit-function construction in Step 3 of
`app:ch_seed:prop:seed-frozen-menu`. Seed regularity supplies a transverse
direction, and the scalar root API supplies a smooth graph. Differentiating
its characteristic equation proves that its tangent map is the chosen frame.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ContDiff Topology

namespace JanetCartan.FrozenMenu

open CubeCarrier CharacteristicRoot

/-- The polynomial formula `app:ch_seed:eq:seed-det` gives global smoothness. -/
private theorem contDiff_cubeDeterminant {n : ℕ} : ContDiff ℝ ∞ (cubeDeterminant (n := n)) := by
  have hc (i : Fin n) : ContDiff ℝ ∞ (fun x : Euclidean n ↦ x i) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  change ContDiff ℝ ∞ (fun x : Euclidean n ↦ cubeDeterminant x)
  simp_rw [cubeDeterminant_eq]
  exact (contDiff_prod (fun i _ ↦ hc i)).sub
    ((contDiff_const.mul (ContDiff.sum (fun i _ ↦ hc i))).mul
      (ContDiff.sum (fun i _ ↦ contDiff_prod (fun j _ ↦ hc j))))

/-- The characteristic graph in Step 3 of `app:ch_seed:prop:seed-frozen-menu`.
The scalar implicit-function theorem constructs the correction `u` on an open
neighborhood of zero. Characteristic tangency of the admissible frame forces
`Du(0) = 0`, so the resulting chart has the prescribed derivative `A`. -/
theorem CarrierSeed.exists_characteristic_graph {n : ℕ} (_hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ)
    (A : Euclidean 3 →L[ℝ] Euclidean n) (hA : IsAdmissibleFrame k ξ A) :
    ∃ (e : Euclidean n) (u : Euclidean 3 → ℝ) (U : Set (Euclidean 3)),
      IsOpen U ∧ 0 ∈ U ∧ fderiv ℝ cubeDeterminant ξ e ≠ 0 ∧
      ContDiffOn ℝ ∞ u U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
      let f := fun z ↦ ξ + A z + u z • e
      ContDiffOn ℝ ∞ f U ∧ f 0 = ξ ∧ fderiv ℝ f 0 = A ∧
        ∀ z ∈ U, cubeDeterminant (f z) = 0 := by
  have hreg := regular_of_quadratic_reciprocal_ne_zero
    h.coordinates_ne_zero h.characteristic h.normal_ne_zero
  obtain ⟨e, he⟩ : ∃ e : Euclidean n, fderiv ℝ cubeDeterminant ξ e ≠ 0 := by
    by_contra! hz
    apply hreg
    ext e
    exact hz e
  let F : Euclidean 3 × ℝ → ℝ :=
    fun w ↦ cubeDeterminant (ξ + A w.1 + w.2 • e)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_cubeDeterminant.comp
      ((contDiff_const.add (A.contDiff.comp contDiff_fst)).add
        (contDiff_snd.smul contDiff_const))
  let L : Euclidean 3 × ℝ →L[ℝ] Euclidean n :=
    A.comp (ContinuousLinearMap.fst ℝ _ _) +
      (ContinuousLinearMap.snd ℝ _ _).smulRight e
  have hg : HasFDerivAt (fun w : Euclidean 3 × ℝ ↦ ξ + A w.1 + w.2 • e) L 0 := by
    simpa [L, add_assoc] using (L.hasFDerivAt (x := 0)).const_add ξ
  have hFd : HasFDerivAt F ((fderiv ℝ cubeDeterminant ξ).comp L) 0 := by
    have hp := (hasFDerivAt_cubeDeterminant
      (ξ + A (0 : Euclidean 3) + (0 : ℝ) • e)).differentiableAt.hasFDerivAt
    simpa [F, Function.comp_def] using hp.comp 0 hg
  have hd : scalarDerivative F (0, 0) ≠ 0 := by
    change fderiv ℝ F 0 (0, 1) ≠ 0
    rw [hFd.fderiv]
    simpa [L] using he
  have hF₀ : F (0, 0) = 0 := by simpa [F] using h.characteristic
  obtain ⟨U, V, c, hU, h0U, _, _, _, hu, heq, _⟩ :=
    exists_localRoot_patch isOpen_univ hF.contDiffOn (mem_univ (0, 0)) hF₀ hd
  let u := localRoot (hF.contDiffOn.contDiffAt (isOpen_univ.mem_nhds (mem_univ (0, 0)))) hd
  have hu₀ : u 0 = 0 := localRoot_base _ _
  have hu' : ContDiffOn ℝ ∞ u U := hu
  have hud : DifferentiableAt ℝ u 0 :=
    (hu'.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  let f := fun z ↦ ξ + A z + u z • e
  have hf₀ : f 0 = ξ := by simp [f, hu₀]
  have hfd : HasFDerivAt f (A + (fderiv ℝ u 0).smulRight e) 0 :=
    ((A.hasFDerivAt (x := 0)).const_add ξ).add (hud.hasFDerivAt.smul_const e)
  have hchar : ∀ z ∈ U, cubeDeterminant (f z) = 0 := by
    intro z hz
    exact (heq z hz).2.2.1
  have hz : (fun z ↦ cubeDeterminant (f z)) =ᶠ[𝓝 0] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact hchar z hz
  have hcomp : (fderiv ℝ cubeDeterminant ξ).comp
      (A + (fderiv ℝ u 0).smulRight e) = 0 := by
    have hp := (hasFDerivAt_cubeDeterminant (f 0)).differentiableAt.hasFDerivAt.comp 0 hfd
    rw [hf₀] at hp
    exact hp.unique ((hasFDerivAt_const (0 : ℝ) (0 : Euclidean 3)).congr_of_eventuallyEq hz)
  have huD : fderiv ℝ u 0 = 0 := by
    ext z
    have ha : fderiv ℝ cubeDeterminant ξ (A z) = 0 :=
      DFunLike.congr_fun hA.1 z
    have hz := DFunLike.congr_fun hcomp z
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, ha, zero_add,
      zero_apply, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_right he
  refine ⟨e, u, U, hU, h0U, he, hu', hu₀, huD, ?_, hf₀, ?_, hchar⟩
  · exact (contDiffOn_const.add A.contDiff.contDiffOn).add (hu'.smul contDiffOn_const)
  · simpa [huD] using hfd.fderiv

end JanetCartan.FrozenMenu
