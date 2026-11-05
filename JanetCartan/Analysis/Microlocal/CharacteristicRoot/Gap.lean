module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Conic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Derivative gaps and compact buffers

For `app:ch_response:thm:response-compatible-choice`, radial continuation preserves
the scalar derivative exactly. Compact subpatches of the open conic root chart
have a positive buffer, including in the scalar root coordinate.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar partial of the full differential is the ordinary scalar derivative.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem hasDerivAt_scalar {f : (X × E) × ℝ → ℝ} {p : X × E} {τ : ℝ}
    (hf : DifferentiableAt ℝ f (p, τ)) :
    HasDerivAt (fun r ↦ f (p, r)) (scalarDerivative f (p, τ)) τ := by
  simpa [scalarDerivative, Function.comp_def] using
    (hf.hasFDerivAt.comp τ
      ((hasFDerivAt_const p τ).prodMk (hasFDerivAt_id τ))).hasDerivAt

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The scalar derivative of a degree-one symbol is unchanged under positive
covector dilation (`app:ch_response:thm:response-compatible-choice`). -/
theorem hasDerivAt_scaled {f : (X × E) × ℝ → ℝ}
    (hh : ∀ (x : X) (η : E) (τ : ℝ) (r : ℝ), 0 < r →
      f ((x, r • η), r * τ) = r * f ((x, η), τ))
    {x : X} {η : E} {τ r d : ℝ} (hr : 0 < r)
    (hd : HasDerivAt (fun s ↦ f ((x, η), s)) d τ) :
    HasDerivAt (fun s ↦ f ((x, r • η), s)) d (r * τ) := by
  have ht : (r * τ) / r = τ := mul_div_cancel_left₀ τ hr.ne'
  have hd' : HasDerivAt (fun s ↦ f ((x, η), s)) d ((r * τ) / r) := by
    rwa [ht]
  have hcomp := (hd'.comp (r * τ) ((hasDerivAt_id (r * τ)).div_const r)).const_mul r
  have heq : (fun s ↦ f ((x, r • η), s)) =
      (fun s ↦ r * f ((x, η), s / r)) := by
    funext s
    simpa only [mul_div_cancel₀ s hr.ne'] using hh x η (s / r) r hr
  rw [heq]
  convert! hcomp using 1
  rw [mul_left_comm r d, one_div, mul_inv_cancel₀ hr.ne', mul_one]

/-- At a nonzero simple characteristic covector, the transverse covector cannot
vanish. This is the Euler-identity argument in the proof of
`app:ch_response:thm:response-compatible-choice`. -/
theorem transverse_ne_zero {f : (X × E) × ℝ → ℝ}
    (hh : ∀ (x : X) (η : E) (τ : ℝ) (r : ℝ), 0 < r →
      f ((x, r • η), r * τ) = r * f ((x, η), τ))
    {x : X} {η : E} {τ : ℝ} (hf : DifferentiableAt ℝ f ((x, η), τ))
    (hz : f ((x, η), τ) = 0) (hd : scalarDerivative f ((x, η), τ) ≠ 0)
    (hξ : (τ, η) ≠ 0) : η ≠ 0 := by
  intro hη
  subst η
  have hs := hasDerivAt_scalar hf
  have hs' : HasDerivAt (fun s ↦ f ((x, (0 : E)), s))
      (scalarDerivative f ((x, 0), τ)) (1 * τ) := by simpa only [one_mul] using hs
  have hcomp := hs'.comp 1 ((hasDerivAt_id 1).mul_const τ)
  have heq : (fun r : ℝ ↦ f ((x, (0 : E)), r * τ)) =ᶠ[𝓝 1] (fun _ ↦ 0) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
    simpa only [smul_zero, hz, mul_zero] using hh x 0 τ r hr
  have he : scalarDerivative f ((x, (0 : E)), τ) * τ = 0 := by
    simpa only [one_mul] using
      hcomp.unique ((hasDerivAt_const 1 (0 : ℝ)).congr_of_eventuallyEq heq)
  have hτ : τ = 0 := (mul_eq_zero.mp he).resolve_left hd
  exact hξ (by simp [hτ])

/-- A conic scalar band around the homogeneous root.
(`app:ch_seed:prop:seed-actual-menu`). -/
def conicBand (ℓ : E →L[ℝ] ℝ) (U : Set (X × E)) (V : Set ℝ) :
    Set ((X × E) × ℝ) :=
  {z | z.1 ∈ conicDomain ℓ U ∧ z.2 / ℓ z.1.2 ∈ V}

/-- The scalar band is an open neighborhood in the full covector space.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem isOpen_conicBand (ℓ : E →L[ℝ] ℝ) {U : Set (X × E)} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (conicBand ℓ U V) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  refine inter_mem ?_ ?_
  · exact continuous_fst.continuousAt.preimage_mem_nhds
      ((isOpen_conicDomain ℓ hU).mem_nhds hz.1)
  · have hd : ContinuousAt (fun z : (X × E) × ℝ ↦ z.2 / ℓ z.1.2) z :=
      continuous_snd.continuousAt.div
        (ℓ.continuous.comp (continuous_snd.comp continuous_fst)).continuousAt hz.1.1.ne'
    exact hd.preimage_mem_nhds (hV.mem_nhds hz.2)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The homogeneous root graph lies in its conic band.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem homogeneousExtension_mem_conicBand (ℓ : E →L[ℝ] ℝ)
    {H : X × E → ℝ} {U : Set (X × E)} {V : Set ℝ}
    (hH : MapsTo H U V) {p : X × E} (hp : p ∈ conicDomain ℓ U) :
    (p, homogeneousExtension ℓ H p) ∈ conicBand ℓ U V := by
  refine ⟨hp, ?_⟩
  simpa only [homogeneousExtension, mul_div_cancel_left₀ _ hp.1.ne'] using hH hp.2

/-- Every compact subpatch of the root chart has a uniform positive buffer in
both the parameters and the scalar covector. This is the compact subpatch gap
used in `app:ch_response:thm:response-compatible-choice`. -/
theorem exists_compact_graph_buffer (ℓ : E →L[ℝ] ℝ)
    {H : X × E → ℝ} {U : Set (X × E)} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H U) (hHV : MapsTo H U V)
    {K : Set (X × E)} (hK : IsCompact K) (hKU : K ⊆ conicDomain ℓ U) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.cthickening δ ((fun p ↦ (p, homogeneousExtension ℓ H p)) '' K) ⊆
        conicBand ℓ U V := by
  apply IsCompact.exists_cthickening_subset_open
    (hK.image_of_continuousOn (continuousOn_id.prodMk
      ((contDiffOn_homogeneousExtension ℓ hU hH).continuousOn.mono hKU)))
    (isOpen_conicBand ℓ hU hV)
  rintro z ⟨p, hp, rfl⟩
  exact homogeneousExtension_mem_conicBand ℓ hHV (hKU hp)

end JanetCartan.CharacteristicRoot
