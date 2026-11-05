module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.NormalGeometry
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The actual inverse on the whole normal image

This constructs the inverse used by `LowBounds.exists_graphL2_of_primitive_inputs`
on `bufferedNormalDomain X D S`, retaining both physical positions. Local smoothness
of the original phase, injectivity and the original averaged-Jacobian gap suffice.
No smaller common target is used. Source: `app:ch_regular_base:thm:actual-calculus`,
Step 1, and `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The inverse of the original averaged gradient on its entire image, for
`app:ch_regular_base:eq:actual-normal-amplitude`. Values off the image are immaterial. -/
def wholeImageInverse (S : E → E → ℝ) (D : Set E) (x y ξ : E) : E :=
  Function.invFunOn (averagedGradient S x y) D ξ

/-- The original covector Jacobian in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
def averagedJacobian (S : E → E → ℝ) (x y u : E) : E →L[ℝ] E :=
  fderiv ℝ (averagedGradient S x y) u

/-- The actual inverse takes every point of the whole image back to the
original chart (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem wholeImageInverse_mem {S : E → E → ℝ} {D : Set E} {x y ξ : E}
    (hξ : ξ ∈ averagedGradient S x y '' D) : wholeImageInverse S D x y ξ ∈ D :=
  Function.invFunOn_mem hξ

/-- Right inverse on the entire image, with both positions retained
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem averagedGradient_wholeImageInverse {S : E → E → ℝ} {D : Set E} {x y ξ : E}
    (hξ : ξ ∈ averagedGradient S x y '' D) :
    averagedGradient S x y (wholeImageInverse S D x y ξ) = ξ :=
  Function.invFunOn_eq hξ

/-- Injectivity gives the left inverse on the original chart
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem wholeImageInverse_averagedGradient {S : E → E → ℝ} {D : Set E} {x y u : E}
    (hi : InjOn (averagedGradient S x y) D) (hu : u ∈ D) :
    wholeImageInverse S D x y (averagedGradient S x y u) = u :=
  hi.leftInvOn_invFunOn hu

/-- The joint normal inverse preserves both output positions and maps the
full image into the input chart (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem mapsTo_wholeImageInverse {S : E → E → ℝ} {X D : Set E} :
    MapsTo (normalInverseCoordinates (wholeImageInverse S D))
      (bufferedNormalDomain X D S) (X ×ˢ (X ×ˢ D)) :=
  fun _ hq ↦ ⟨hq.1, hq.2.1, wholeImageInverse_mem hq.2.2⟩

/-- Joint right-inverse equation on the whole image
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem normalForward_wholeImageInverse {S : E → E → ℝ} {X D : Set E}
    {q : NormalVariables n} (hq : q ∈ bufferedNormalDomain X D S) :
    normalForwardCoordinates S (normalInverseCoordinates (wholeImageInverse S D) q) = q := by
  simp only [normalForwardCoordinates, normalInverseCoordinates,
    averagedGradient_wholeImageInverse hq.2.2]

/-- Local phase smoothness implies joint averaged-gradient smoothness on the
entire source chart. This supplies the implicit-function construction in
actual-calculus Step 1, with no global extension or homogeneity assumption. -/
theorem averagedGradient_contDiffOn {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) :
    ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ averagedGradient S q.1 q.2.1 q.2.2)
      (X ×ˢ (X ×ˢ D)) := by
  let H := fun z : ℝ × NormalVariables n ↦ segmentPhaseDifferential S z.1 z.2
  have hH : ∀ z ∈ uIcc (0 : ℝ) 1 ×ˢ (X ×ˢ (X ×ˢ D)), ContDiffAt ℝ ∞ H z := by
    intro z hz
    exact segmentPhaseDifferential_contDiffAt hX hD hcX hS (by simpa using hz)
  have hi := contDiffOn_fixedIntervalIntegral (hX.prod (hX.prod hD)) hH
  have hs := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hi
  apply hs.congr
  intro q hq
  change (InnerProductSpace.toDual ℝ E).symm (averagedPhaseDifferential S q.1 q.2.1 q.2.2) = _
  apply congrArg (InnerProductSpace.toDual ℝ E).symm
  apply intervalIntegral.integral_congr
  intro t ht
  exact (segmentPhaseDifferential_eq hX hD hcX hS (by simpa using ht) hq).symm

private theorem exists_local_inverse {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    {p : NormalVariables n} (hp : p ∈ bufferedNormalDomain X D S) :
    ∃ g : NormalVariables n → E, ContDiffAt ℝ ∞ g p ∧
      ∀ᶠ q in 𝓝 p, q ∈ bufferedNormalDomain X D S ∧
        g q = wholeImageInverse S D q.1 q.2.1 q.2.2 := by
  let u := wholeImageInverse S D p.1 p.2.1 p.2.2
  let H : NormalVariables n × E → E := fun z ↦
    averagedGradient S z.1.1 z.1.2.1 z.2 - z.1.2.2
  have hu : u ∈ D := wholeImageInverse_mem hp.2.2
  have he : averagedGradient S p.1 p.2.1 u = p.2.2 :=
    averagedGradient_wholeImageInverse hp.2.2
  have hf := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt (x := (p.1, (p.2.1, u)))
    ((hX.prod (hX.prod hD)).mem_nhds ⟨hp.1, hp.2.1, hu⟩)
  have hH : ContDiffAt ℝ ∞ H (p, u) :=
    (hf.comp (p, u) (contDiffAt_fst.fst.prodMk
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd))).sub contDiffAt_fst.snd.snd
  have hj : fderiv ℝ H (p, u) ∘L ContinuousLinearMap.inr ℝ (NormalVariables n) E =
      averagedJacobian S p.1 p.2.1 u := by
    have hd := ((hH.differentiableAt (by simp)).hasFDerivAt.comp u
      (hasFDerivAt_prodMk_right p u)).fderiv
    simpa [H, averagedJacobian, Function.comp_def, fderiv_sub_const] using hd.symm
  have hi : (fderiv ℝ H (p, u) ∘L ContinuousLinearMap.inr ℝ (NormalVariables n) E).IsInvertible := by
    rw [hj]
    exact isInvertible_of_det_gap hδ (hgap _ hp.1 _ hp.2.1 _ hu)
  let g := hH.implicitFunction (by simp) hi
  have hg : ContDiffAt ℝ ∞ g p := hH.contDiffAt_implicitFunction (by simp) hi
  have hgu : g p = u := hH.implicitFunction_apply_self (by simp) hi
  refine ⟨g, hg, ?_⟩
  have hmem : ∀ᶠ q in 𝓝 p, g q ∈ D := hg.continuousAt (hD.mem_nhds (hgu.symm ▸ hu))
  have hxy : ∀ᶠ q in 𝓝 p, q.1 ∈ X ∧ q.2.1 ∈ X :=
    ((hX.preimage continuous_fst).inter (hX.preimage (continuous_fst.comp continuous_snd))).mem_nhds
      ⟨hp.1, hp.2.1⟩
  filter_upwards [hmem, hxy, hH.eventually_apply_implicitFunction (by simp) hi] with q hq hqxy hEq
  have hgrad : averagedGradient S q.1 q.2.1 (g q) = q.2.2 :=
    sub_eq_zero.mp (hEq.trans (sub_eq_zero.mpr he))
  refine ⟨⟨hqxy.1, hqxy.2, g q, hq, hgrad⟩, ?_⟩
  rw [← hgrad, wholeImageInverse_averagedGradient (hinj _ hqxy.1 _ hqxy.2) hq]

/-- The whole joint image is open, derived from the original Jacobian gap.
This discharges `PrimitiveNormalGeometry.open_domain` in actual-calculus Step 1. -/
theorem isOpen_bufferedNormalDomain {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) :
    IsOpen (bufferedNormalDomain X D S) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨g, _, hg⟩ := exists_local_inverse hX hD hcX hS hinj hδ hgap hp
  exact Filter.mem_of_superset hg (fun _ h ↦ h.1)

/-- The constructed joint inverse is smooth on every point of the whole
normal image. This discharges `PrimitiveNormalGeometry.inverse_smooth`, not
merely its restriction to a common target (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem wholeImageInverse_contDiffOn {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) :
    ContDiffOn ℝ ∞ (normalInverseCoordinates (wholeImageInverse S D))
      (bufferedNormalDomain X D S) := by
  have hη : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      wholeImageInverse S D q.1 q.2.1 q.2.2) (bufferedNormalDomain X D S) := by
    intro p hp
    obtain ⟨g, hg, he⟩ := exists_local_inverse hX hD hcX hS hinj hδ hgap hp
    exact (hg.congr_of_eventuallyEq (he.mono (fun _ h ↦ h.2.symm))).contDiffWithinAt
  exact contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hη)

/-- Smoothness of the original covector Jacobian on the source chart, for
the input coefficient field in `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem averagedJacobian_contDiffOn {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) :
    ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ averagedJacobian S q.1 q.2.1 q.2.2)
      (X ×ˢ (X ×ˢ D)) := by
  intro q hq
  have hf := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
    ((hX.prod (hX.prod hD)).mem_nhds hq)
  have haux := hf.comp (q, q.2.2)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd))
  exact (haux.fderiv contDiffAt_snd.snd (by simp)).contDiffWithinAt

/-- The joint forward chart has exactly the buffered normal domain as image.
This is the full-image identity in actual-calculus Step 1. -/
theorem normalForwardCoordinates_image (S : E → E → ℝ) (X D : Set E) :
    normalForwardCoordinates S '' (X ×ˢ (X ×ˢ D)) = bufferedNormalDomain X D S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp.1, hp.2.1, p.2.2, hp.2.2, rfl⟩
  · rintro ⟨hx, hy, u, hu, he⟩
    exact ⟨(q.1, (q.2.1, u)), ⟨hx, hy, hu⟩, by
      simp only [normalForwardCoordinates, he]⟩

/-- Every field of the exact change-of-variables chart is derived from local
phase smoothness, injectivity and the averaged-Jacobian gap. This supplies
`LowBounds.AveragedGradientChart` for `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem averagedGradientChart {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) :
    AveragedGradientChart S X D (wholeImageInverse S D) (averagedJacobian S) δ := by
  refine ⟨hD.measurableSet, hδ, ?_, ?_, ?_, hinj, ?_, hgap⟩
  · intro x hx y hy u hu t ht
    have hp := hS.contDiffAt (x := (y + t • (x - y), u)) ((hX.prod hD).mem_nhds
      ⟨hcX.add_smul_sub_mem hy hx (by simpa using ht), hu⟩)
    exact (hp.comp (y + t • (x - y)) (f := fun z : E ↦ (z, u))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · intro x hx y hy u hu
    have hc : ContinuousOn (fun t : ℝ ↦ segmentPhaseDifferential S t (x, (y, u)))
        (uIcc (0 : ℝ) 1) := by
      intro t ht
      exact ((segmentPhaseDifferential_contDiffAt hX hD hcX hS
        (z := (t, (x, (y, u)))) ⟨by simpa using ht, hx, hy, hu⟩).continuousAt.comp
          (f := fun t : ℝ ↦ (t, (x, (y, u))))
          (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
    apply hc.intervalIntegrable.congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      have : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact ⟨this.1.le, this.2⟩
    exact segmentPhaseDifferential_eq hX hD hcX hS ht' ⟨hx, hy, hu⟩
  · intro x hx y hy u hu
    have hf := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
      (x := (x, (y, u))) ((hX.prod (hX.prod hD)).mem_nhds ⟨hx, hy, hu⟩)
    exact ((hf.comp u (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro x hx y hy u hu
    exact wholeImageInverse_averagedGradient (hinj x hx y hy) hu

end JanetCartan.FourierIntegral.WholeImageGeometry
