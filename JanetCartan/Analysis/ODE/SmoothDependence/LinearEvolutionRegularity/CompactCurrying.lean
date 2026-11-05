module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.UniformRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Smooth currying on a compact time interval

The parameter regularity used in `app:ch_regular_base:lem:buffered-interpolation`
and `app:lem:common-hamilton-phase` passes from a jointly smooth function to a
smooth family in the supremum norm on continuous curves. The ambient open domain
need only contain the product with the time interval; it need not be a product.

The first derivative follows from the uniform Taylor remainder on the compact
fiber `{x} × [0,1]`. Induction then bundles the parameter derivatives by a
continuous linear map. No finite-dimensional or completeness assumption is needed.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace JanetCartan.ODE.LinearEvolutionRegularity

universe u v

variable {X : Type u} {F : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable local instance : NormedAddCommGroup C(Icc (0 : ℝ) 1, F) := inferInstance
noncomputable local instance : NormedSpace ℝ C(Icc (0 : ℝ) 1, F) := inferInstance
noncomputable local instance : NormedAddCommGroup C(Icc (0 : ℝ) 1, X →L[ℝ] F) := inferInstance
noncomputable local instance : NormedSpace ℝ C(Icc (0 : ℝ) 1, X →L[ℝ] F) := inferInstance

/-- Bundle a continuous curve of linear maps as a linear map into continuous
curves, as used for parameter derivatives in `app:lem:common-hamilton-phase`. -/
noncomputable def curveLinearMap (a : C(Icc (0 : ℝ) 1, X →L[ℝ] F)) :
    X →L[ℝ] C(Icc (0 : ℝ) 1, F) :=
  LinearMap.mkContinuous
    { toFun := fun v ↦ ⟨fun t ↦ a t v, a.continuous.clm_apply continuous_const⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖a‖ (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      exact ((a t).le_opNorm v).trans (mul_le_mul_of_nonneg_right
        (a.norm_coe_le_norm t) (norm_nonneg v)))

/-- Bundling operator curves is continuous and linear in the supremum norm.
This supplies the induction step for `app:ch_regular_base:lem:buffered-interpolation`. -/
noncomputable def curveLinearMapCLM :
    C(Icc (0 : ℝ) 1, X →L[ℝ] F) →L[ℝ] X →L[ℝ] C(Icc (0 : ℝ) 1, F) :=
  LinearMap.mkContinuous
    { toFun := curveLinearMap (X := X) (F := F)
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (by
      intro a
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      exact (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (fun t ↦ ((a t).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm t) (norm_nonneg v))))

omit [NormedSpace ℝ X] [NormedSpace ℝ F] in
/-- Continuous currying on the unit interval, the order-zero case of the curve
regularity needed in `app:lem:common-hamilton-phase`. -/
lemma continuousOn_curve_curry {s : Set X} {U : Set (X × ℝ)}
    {f : X × ℝ → F} {g : X → C(Icc (0 : ℝ) 1, F)}
    (hSU : s ×ˢ Icc (0 : ℝ) 1 ⊆ U) (hf : ContinuousOn f U)
    (hg : ∀ x ∈ s, ∀ t : Icc (0 : ℝ) 1, g x t = f (x, t)) :
    ContinuousOn g s := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  apply (hf.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun z hz ↦ hSU ⟨hz.1, z.2.2⟩)).congr
  intro z hz
  exact hg z.1 hz.1 z.2

/-- The parameter derivative in the supremum norm is obtained by bundling the
pointwise parameter derivatives. The compact-fiber Taylor estimate proves the
uniform remainder required in `app:lem:common-hamilton-phase`. -/
lemma hasFDerivAt_curve_curry {s : Set X} {U : Set (X × ℝ)}
    {f : X × ℝ → F} {g : X → C(Icc (0 : ℝ) 1, F)}
    (hs : IsOpen s) (hU : IsOpen U) (hSU : s ×ˢ Icc (0 : ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ 1 f U)
    (hg : ∀ x ∈ s, ∀ t : Icc (0 : ℝ) 1, g x t = f (x, t))
    {x : X} (hx : x ∈ s) (a : C(Icc (0 : ℝ) 1, X →L[ℝ] F))
    (ha : ∀ t : Icc (0 : ℝ) 1,
      a t = (fderiv ℝ f (x, t)).comp (ContinuousLinearMap.inl ℝ X ℝ)) :
    HasFDerivAt g (curveLinearMap a) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_fderiv_remainder hU hf
    ((isCompact_singleton (x := x)).prod isCompact_Icc)
    (by rintro ⟨y, t⟩ ⟨hy, ht⟩; rcases hy with rfl; exact hSU ⟨hx, ht⟩) hε
  filter_upwards [hs.mem_nhds hx, Metric.ball_mem_nhds x hδ] with y hy hxy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have h := hb (x, t) ⟨rfl, t.2⟩ (y, t) (by simpa using hxy)
  change ‖g y t - g x t - curveLinearMap a (y - x) t‖ ≤ ε * ‖y - x‖
  have he : curveLinearMap a (y - x) t = fderiv ℝ f (x, t) (y - x, 0) := by
    change a t (y - x) = _
    rw [ha t]
    rfl
  rw [hg y hy t, hg x hx t, he]
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)] using h

-- Keep the codomain universe closed under forming spaces of parameter derivatives.
private theorem contDiffOn_curve_curry_aux
    {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) {s : Set X} {U : Set (X × ℝ)}
    {f : X × ℝ → G} {g : X → C(Icc (0 : ℝ) 1, G)}
    (hs : IsOpen s) (hU : IsOpen U) (hSU : s ×ˢ Icc (0 : ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ n f U)
    (hg : ∀ x ∈ s, ∀ t : Icc (0 : ℝ) 1, g x t = f (x, t)) :
    ContDiffOn ℝ n g s := by
  induction n generalizing G with
  | zero =>
    exact contDiffOn_zero.mpr (continuousOn_curve_curry hSU hf.continuousOn hg)
  | succ n ih =>
    let f' : X × ℝ → X →L[ℝ] G := fun z ↦
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ X ℝ)
    have hf' : ContDiffOn ℝ n f' U :=
      (hf.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
    let a : X → C(Icc (0 : ℝ) 1, X →L[ℝ] G) := fun x ↦
      ContinuousMap.mkD (fun t ↦ f' (x, t)) 0
    have ha (x : X) (hx : x ∈ s) (t : Icc (0 : ℝ) 1) : a x t = f' (x, t) := by
      have hc : Continuous (fun t : Icc (0 : ℝ) 1 ↦ f' (x, t)) :=
        hf'.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
          (fun t ↦ hSU ⟨hx, t.2⟩)
      exact ContinuousMap.mkD_apply_of_continuous hc
    have hca : ContDiffOn ℝ n a s := ih hf' ha
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn]
    refine ⟨by simp, (fun x ↦ curveLinearMap (a x)), ?_, ?_⟩
    · exact curveLinearMapCLM.contDiff.comp_contDiffOn hca
    · intro x hx
      exact (hasFDerivAt_curve_curry hs hU hSU
        (hf.of_le (by exact_mod_cast Nat.succ_pos n)) hg hx (a x) (ha x hx)).hasFDerivWithinAt

/-- Finite-order smooth currying into continuous curves, supporting
`app:ch_regular_base:lem:buffered-interpolation` and `app:lem:common-hamilton-phase`.
The open set `U` may be any neighborhood of `s × [0,1]`, and no regularity of `g`
is assumed beyond its pointwise agreement with `f` on that product. -/
theorem contDiffOn_curve_curry (n : ℕ) {s : Set X} {U : Set (X × ℝ)}
    {f : X × ℝ → F} {g : X → C(Icc (0 : ℝ) 1, F)}
    (hs : IsOpen s) (hU : IsOpen U) (hSU : s ×ˢ Icc (0 : ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ n f U)
    (hg : ∀ x ∈ s, ∀ t : Icc (0 : ℝ) 1, g x t = f (x, t)) :
    ContDiffOn ℝ n g s := by
  -- Embed in `X × F` to apply the induction at a common universe, then project back.
  let i : F →L[ℝ] X × F := ContinuousLinearMap.inr ℝ X F
  let p : X × F →L[ℝ] F := ContinuousLinearMap.snd ℝ X F
  have h := contDiffOn_curve_curry_aux n hs hU hSU
    (i.contDiff.comp_contDiffOn hf)
    (g := fun x ↦ i.compLeftContinuous ℝ (Icc (0 : ℝ) 1) (g x))
    (fun x hx t ↦ congrArg i (hg x hx t))
  have h' := (p.compLeftContinuous ℝ (Icc (0 : ℝ) 1)).contDiff.comp_contDiffOn h
  convert h' using 1
  ext x t
  rfl

end JanetCartan.ODE.LinearEvolutionRegularity
