module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection

/-!
# The projected stress frame of actual immersions

The normal output spaces in `app:ch_background:defn:bg-geometry` vary with the
immersion. Restricted orthogonal projection identifies nearby normal spaces;
its injectivity preserves the stress kernel. This supplies the actual geometric
neighborhood and smoothness, without assuming a constant normal space.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Topology

namespace JanetCartan.StressFrame

open NormalRankStability

/-- The actual second form on symmetric Frobenius tensors, with values in the
actual normal space (`app:ch_background:defn:bg-geometry`). -/
def symmetricNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    SymmetricTensor n →L[ℝ] normalSpace F x :=
  (geometricNormalMap F x).comp (symmetricTensorSubmodule n).subtypeL

/-- Comparison of actual second forms in a fixed reference normal space,
using the proved normal-space identification (`app:ch_waves:thm:leading`). -/
def fixedSymmetricNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (G : Euclidean n → Euclidean N) (y : Euclidean n) :
    SymmetricTensor n →L[ℝ] normalSpace F x :=
  (projectionBetween (normalSpace G y) (normalSpace F x)).comp (symmetricNormalMap G y)

/-- `app:ch_background:defn:bg-geometry`: the actual projected stress. -/
def geometricCubeStress {n N : ℕ} (G : Euclidean n → Euclidean N)
    (y : Euclidean n) (i : Fin n) : SymmetricTensor n :=
  projectedCubeStress (symmetricNormalMap G y).toLinearMap i

/-- `app:ch_background:defn:bg-geometry`: the bundled kernel is exactly the
manuscript's symmetric stress space. -/
theorem mem_symmetricNormalMap_ker {n N : ℕ} (G : Euclidean n → Euclidean N)
    (y : Euclidean n) (H : SymmetricTensor n) :
    H ∈ (symmetricNormalMap G y).ker ↔ H.val ∈ stressSpace G y := by
  change (symmetricNormalMap G y H = 0) ↔ H.val.IsSymm ∧ normalMap G y H.val = 0
  exact ⟨fun h ↦ ⟨H.property, congrArg Subtype.val h⟩,
    fun h ↦ Subtype.ext h.2⟩

/-- `app:ch_background:defn:bg-geometry`: the specified projected tensors
are symmetric stresses for the actual immersion. -/
theorem geometricCubeStress_mem_stressSpace {n N : ℕ} (G : Euclidean n → Euclidean N)
    (y : Euclidean n) (i : Fin n) :
    (geometricCubeStress G y i).val ∈ stressSpace G y :=
  (mem_symmetricNormalMap_ker G y _).mp (projectedCubeStress_mem_ker _ i)

/-- At the reference point comparison is the actual second form
(`app:ch_background:defn:bg-geometry`). -/
@[simp] theorem fixedSymmetricNormalMap_self {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    fixedSymmetricNormalMap F x F x = symmetricNormalMap F x := by
  ext H : 1
  apply Subtype.ext
  exact normalProjection_normalMap F x H.val

/-- Identifying nearby normal spaces preserves the kernel, hence the exact
orthogonal stress projection (`app:ch_waves:thm:leading`). -/
theorem fixedSymmetricNormalMap_ker {n N : ℕ}
    (F G : Euclidean n → Euclidean N) (x y : Euclidean n)
    (hclose : ‖normalProjection F x - normalProjection G y‖ < 1) :
    (fixedSymmetricNormalMap F x G y).ker = (symmetricNormalMap G y).ker := by
  have hi := projectionBetween_injective (normalSpace G y) (normalSpace F x) hclose
  ext H
  change projectionBetween (normalSpace G y) (normalSpace F x)
    (symmetricNormalMap G y H) = 0 ↔ symmetricNormalMap G y H = 0
  rw [← map_zero (projectionBetween (normalSpace G y) (normalSpace F x)), hi.eq_iff]

/-- `app:ch_background:defn:bg-geometry`: smoothness of the fixed-space
second-form comparison follows from the actual C^(r+2) immersion. -/
theorem contDiffOn_fixedSymmetricNormalMap {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} {s : Set (Euclidean n)} {r m : ℕ∞ω}
    (hs : IsOpen s) (hG : ContDiffOn ℝ m G s) (hr : r + 1 + 1 ≤ m)
    (himm : IsImmersionOn G s) :
    ContDiffOn ℝ r (fixedSymmetricNormalMap F x G) s := by
  apply contDiffOn_clm_apply.mpr
  intro H
  change ContDiffOn ℝ r (fun y ↦ (normalSpace F x).orthogonalProjectionOnto
    (∑ i, ∑ j, H.val i j • secondFundamentalForm G y i j)) s
  apply (normalSpace F x).orthogonalProjectionOnto.contDiff.comp_contDiffOn
  exact ContDiffOn.sum fun i _ ↦ ContDiffOn.sum fun j _ ↦
    (contDiffOn_secondFundamentalForm hs hG hr himm i j).const_smul _

/-- `app:ch_waves:thm:leading`: actual stresses are C^r on a patch with
nearby normal spaces and a surjective fixed-space second form. The comparison
is eliminated using the proved equality of kernels. -/
theorem contDiffOn_geometricCubeStress_of_comparison {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} {s : Set (Euclidean n)} {r m : ℕ∞ω}
    (hs : IsOpen s) (hG : ContDiffOn ℝ m G s) (hr : r + 1 + 1 ≤ m)
    (himm : IsImmersionOn G s)
    (hp : ∀ y ∈ s, ‖normalProjection F x - normalProjection G y‖ < 1)
    (hb : ∀ y ∈ s, Function.Surjective (fixedSymmetricNormalMap F x G y))
    (i : Fin n) : ContDiffOn ℝ r (fun y ↦ geometricCubeStress G y i) s := by
  apply (contDiffOn_projectedCubeStress_family
    (contDiffOn_fixedSymmetricNormalMap F x hs hG hr himm) hb i).congr
  intro y hy
  change (symmetricNormalMap G y).ker.starProjection _ =
    (fixedSymmetricNormalMap F x G y).ker.starProjection _
  exact congrArg (fun K : Submodule ℝ (SymmetricTensor n) ↦
    K.starProjection (cubeSymmetricStress n i))
      (fixedSymmetricNormalMap_ker F G x y (hp y hy)).symm

/-- `app:ch_background:defn:bg-geometry`: one neighborhood of a full-rank
reference fixes a positive stress Gram gap for every nearby actual second
form. The moving normal spaces are identified, never assumed equal. -/
theorem exists_geometric_cubeStressFrame_neighborhood {n N : ℕ} (hn : 5 ≤ n)
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hsurj : Function.Surjective (symmetricNormalMap F x))
    (hker : (symmetricNormalMap F x).ker =
      Submodule.span ℝ (Set.range (cubeSymmetricStress n))) :
    ∃ δ > 0, ∃ γ > 0, ∀ (G : Euclidean n → Euclidean N) (y : Euclidean n),
      ‖normalProjection F x - normalProjection G y‖ < 1 →
      ‖fixedSymmetricNormalMap F x G y - symmetricNormalMap F x‖ < δ →
      Function.Surjective (symmetricNormalMap G y) ∧
        HasCubeStressFrame (symmetricNormalMap G y).ker γ := by
  obtain ⟨δ, hδ, γ, hγ, h⟩ := exists_operator_cubeStressFrame_neighborhood hn
    (symmetricNormalMap F x) hsurj hker
  refine ⟨δ, hδ, γ, hγ, fun G y hp hb ↦ ?_⟩
  obtain ⟨honto, hframe⟩ := h (fixedSymmetricNormalMap F x G y) hb
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨H, hH⟩ := honto (projectionBetween (normalSpace G y) (normalSpace F x) w)
    exact ⟨H, projectionBetween_injective (normalSpace G y) (normalSpace F x) hp hH⟩
  · rwa [fixedSymmetricNormalMap_ker F G x y hp] at hframe

/-- `app:ch_background:defn:bg-geometry`: the actual smooth immersion has a
ball with smooth projected basis and a single uniform positive Gram gap.
All comparison and independence premises are discharged by continuity at the
full-rank reference point. -/
theorem exists_ball_smooth_geometricCubeStress {n N : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (himm : IsImmersionOn F s)
    {x : Euclidean n} (hx : x ∈ s)
    (hsurj : Function.Surjective (symmetricNormalMap F x))
    (hker : (symmetricNormalMap F x).ker =
      Submodule.span ℝ (Set.range (cubeSymmetricStress n))) :
    ∃ ε > 0, ∃ γ > 0, Metric.ball x ε ⊆ s ∧
      (∀ i, ContDiffOn ℝ ∞ (fun y ↦ geometricCubeStress F y i) (Metric.ball x ε)) ∧
      ∀ y ∈ Metric.ball x ε, Function.Surjective (symmetricNormalMap F y) ∧
        HasCubeStressFrame (symmetricNormalMap F y).ker γ := by
  obtain ⟨δ, hδ, γ, hγ, hframe⟩ :=
    exists_operator_cubeStressFrame_neighborhood hn (symmetricNormalMap F x) hsurj hker
  have hp : ∀ᶠ y in 𝓝 x, ‖normalProjection F x - normalProjection F y‖ < 1 :=
    (continuousAt_const.sub ((contDiffOn_normalProjection hs hF (r := ∞)
      (by simp) himm).continuousOn.continuousAt (hs.mem_nhds hx))).norm.eventually
      (gt_mem_nhds (by simp))
  have hc : ContinuousAt (fixedSymmetricNormalMap F x F) x :=
    (contDiffOn_fixedSymmetricNormalMap F x hs hF (r := ∞)
    (by simp) himm).continuousOn.continuousAt (hs.mem_nhds hx)
  have hb : ∀ᶠ y in 𝓝 x,
      ‖fixedSymmetricNormalMap F x F y - symmetricNormalMap F x‖ < δ :=
    by
      have hnear := hc.eventually (Metric.ball_mem_nhds
        (fixedSymmetricNormalMap F x F x) hδ)
      filter_upwards [hnear] with y hy
      have hd : dist (fixedSymmetricNormalMap F x F y)
          (fixedSymmetricNormalMap F x F x) < δ := hy
      rwa [dist_eq_norm (fixedSymmetricNormalMap F x F y)
        (fixedSymmetricNormalMap F x F x), fixedSymmetricNormalMap_self] at hd
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Eventually.and (hs.mem_nhds hx) (hp.and hb))
  have hsub : Metric.ball x ε ⊆ s := fun _ hy ↦ (he hy).1
  have hproj : ∀ y ∈ Metric.ball x ε,
      ‖normalProjection F x - normalProjection F y‖ < 1 := fun _ hy ↦ (he hy).2.1
  have honto : ∀ y ∈ Metric.ball x ε,
      Function.Surjective (fixedSymmetricNormalMap F x F y) :=
    fun y hy ↦ (hframe _ (he hy).2.2).1
  refine ⟨ε, hε, γ, hγ, hsub, fun i ↦ ?_, fun y hy ↦ ?_⟩
  · exact contDiffOn_geometricCubeStress_of_comparison F x Metric.isOpen_ball
      (hF.mono hsub) (by simp) (fun y hy ↦ himm y (hsub hy)) hproj honto i
  · refine ⟨?_, ?_⟩
    · intro w
      obtain ⟨H, hH⟩ := honto y hy (projectionBetween (normalSpace F y) (normalSpace F x) w)
      exact ⟨H, projectionBetween_injective _ _ (hproj y hy) hH⟩
    · have hf := (hframe _ (he hy).2.2).2
      rwa [fixedSymmetricNormalMap_ker F F x y (hproj y hy)] at hf

end JanetCartan.StressFrame
