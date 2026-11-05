module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Profiles
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Derivatives of the literal phase covectors

Restricting the joint phase differential to physical or covector directions
costs one joint derivative. Together with the retained profiles this proves
the `L^(r-1)` power in `app:ch_waves:eq:graded-phase`. The physical restriction
is the exact input used by `cNorm_rawPrimaryDemodulatedIntegral_le`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.AmplitudeGrades

variable {X P E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The phase differential restricted to either group of variables costs
one derivative and no dimension factor (`app:ch_waves:eq:graded-phase`). -/
theorem norm_iteratedFDeriv_restricted_fderiv_le
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (B : X →L[ℝ] E) (hB : ‖B‖ ≤ 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (fderiv ℝ f y).comp B) x‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) f x‖ := by
  let A : (E →L[ℝ] F) →L[ℝ] (X →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ X E F).flip B
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro D
    change ‖D.comp B‖ ≤ 1 * ‖D‖
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [norm_nonneg D])
  have hh := A.norm_iteratedFDeriv_comp_left
    (hf.fderiv_right (show ∞ + 1 ≤ ∞ by simp)) (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (fun y ↦ (fderiv ℝ f y).comp B) x‖ ≤ _ at hh
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans_eq (one_mul _))

/-- Freezing parameters contracts joint jets on any open domain. This is
used to turn the joint WKB/phase grades into the physical jets required by
`cNorm_rawPrimaryDemodulatedIntegral_le`
(`app:ch_waves:eq:individual-grading`). -/
theorem norm_iteratedFDeriv_physical_slice_le
    {Ω : Set (X × P)} (hΩ : IsOpen Ω) {f : X × P → F}
    (hf : ContDiffOn ℝ ∞ f Ω) {x : X} {p : P} (hx : (x, p) ∈ Ω) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f (y, p)) x‖ ≤ ‖iteratedFDeriv ℝ j f (x, p)‖ := by
  let B : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  let g : X × P → F := fun w ↦ f ((0, p) + w)
  let V : Set (X × P) := (fun w ↦ (0, p) + w) ⁻¹' Ω
  have hV : IsOpen V := hΩ.preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g V :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ h ↦ h)
  have hpre : IsOpen (B ⁻¹' V) := hV.preimage B.continuous
  have hx' : B x ∈ V := by simpa [V, B] using hx
  have he := B.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn hx'
    (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hpre hx',
    iteratedFDerivWithin_of_isOpen j hV hx'] at he
  have heq : (fun y ↦ f (y, p)) = g ∘ B := by ext y; simp [g, B]
  rw [heq, he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (B x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
        (fun _ _ ↦ ContinuousLinearMap.norm_inl_le_one ..)
    _ = _ := by simp [g, B, iteratedFDeriv_comp_add_left]

/-- The actual derivative in the second variable is the restriction of the
joint differential (`app:ch_waves:eq:graded-phase`). -/
theorem parameter_fderiv_eq_restricted
    {f : X × P → F} {w : X × P} (hf : DifferentiableAt ℝ f w) :
    fderiv ℝ (fun p ↦ f (w.1, p)) w.2 =
      (fderiv ℝ f w).comp (ContinuousLinearMap.inr ℝ X P) := by
  exact (hf.hasFDerivAt.comp w.2
    ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _))).fderiv

/-- Joint jets of the literal parameter covector are controlled by one
additional phase jet, locally on the original domain
(`app:ch_waves:eq:graded-phase`). -/
theorem norm_iteratedFDeriv_parameter_fderiv_le
    {Ω : Set (X × P)} (hΩ : IsOpen Ω) {S : X × P → ℝ}
    (hS : ContDiffOn ℝ ∞ S Ω) {w : X × P} (hw : w ∈ Ω) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (fun p ↦ S (y.1, p)) y.2) w‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) S w‖ := by
  have he : (fun y ↦ fderiv ℝ (fun p ↦ S (y.1, p)) y.2) =ᶠ[𝓝 w]
      (fun y ↦ (fderiv ℝ S y).comp (ContinuousLinearMap.inr ℝ X P)) := by
    filter_upwards [hΩ.mem_nhds hw] with y hy
    exact parameter_fderiv_eq_restricted
      ((hS.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
  exact norm_iteratedFDeriv_restricted_fderiv_le (hS.contDiffAt (hΩ.mem_nhds hw))
    _ (ContinuousLinearMap.norm_inr_le_one ..) j

/-- The physical phase-covector jets needed by the raw integral are bounded
by the original joint phase jets; no phase-quotient estimate is assumed
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_physical_parameter_fderiv_le
    {Ω : Set (X × P)} (hΩ : IsOpen Ω) {S : X × P → ℝ}
    (hS : ContDiffOn ℝ ∞ S Ω) {x : X} {p : P} (hx : (x, p) ∈ Ω) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (fun q ↦ S (y, q)) p) x‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) S (x, p)‖ := by
  have hd : ContDiffOn ℝ ∞
      (fun w ↦ (fderiv ℝ S w).comp (ContinuousLinearMap.inr ℝ X P)) Ω :=
    (hS.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_comp contDiffOn_const
  have he : (fun y ↦ fderiv ℝ (fun q ↦ S (y, q)) p) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ S (y, p)).comp (ContinuousLinearMap.inr ℝ X P)) := by
    filter_upwards [((hΩ.preimage (by fun_prop : Continuous (fun y : X ↦ (y, p)))).mem_nhds hx)]
      with y hy
    exact parameter_fderiv_eq_restricted
      ((hS.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
  exact (norm_iteratedFDeriv_physical_slice_le hΩ hd hx j).trans
    (norm_iteratedFDeriv_restricted_fderiv_le (hS.contDiffAt (hΩ.mem_nhds hx))
      _ (ContinuousLinearMap.norm_inr_le_one ..) j)

end JanetCartan.RawPrimary.AmplitudeGrades
