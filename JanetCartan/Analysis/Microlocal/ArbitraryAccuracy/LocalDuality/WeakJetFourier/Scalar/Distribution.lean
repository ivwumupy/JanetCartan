module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.RestrictionPairing
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.CompactSchwartz.Cutoff

/-!
# Genuine weak derivatives as tempered distributions

The scalar weak-jet comparison for `app:ch_regular_base:eq:negative-duality`
and `app:ch_regular:eq:inverse-remainder` needs actualdistributional derivatives.
Compact real tests are complexified, then extended to Schwartz tests by the
checked expanding-cutoff convergence theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped SchwartzMap LineDeriv Topology ContDiff

namespace JanetCartan.Mollification

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
/-- The genuine whole-space weak derivative identity determines the tempered
distributional derivative of its L² representative. This supplies the coordinate
derivatives used in `app:ch_regular_base:eq:negative-duality`. -/
theorem HasWeakFDerivOn.toTemperedDistribution {f : E → ℂ} {f' : E → E →L[ℝ] ℂ}
    (hw : HasWeakFDerivOn volume f f' univ)
    (u v : Lp (α := E) ℂ 2) (m : E)
    (hu : u =ᵐ[volume] f) (hv : v =ᵐ[volume] fun x ↦ f' x m) :
    ∂_{m} (u : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ)) := by
  have hreal (ψ : 𝓢(E, ℝ)) (hc : HasCompactSupport (ψ : E → ℝ)) :
      (∂_{m} (u : 𝓢'(E, ℂ))) (ψ.postcompCLM Complex.ofRealCLM) =
        (v : 𝓢'(E, ℂ)) (ψ.postcompCLM Complex.ofRealCLM) := by
    have hd (x : E) : fderiv ℝ (ψ.postcompCLM Complex.ofRealCLM) x m =
        (fderiv ℝ ψ x m : ℂ) := by
      exact congrArg (fun L : E →L[ℝ] ℂ ↦ L m)
        ((Complex.ofRealCLM.hasFDerivAt.comp x
          (ψ.differentiableAt.hasFDerivAt)).fderiv)
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    have hleft : (∫ x, (∂_{m} (ψ.postcompCLM Complex.ofRealCLM)) x • u x) =
        ∫ x, fderiv ℝ ψ x m • f x := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, hd, hx,
        smul_eq_mul, Complex.real_smul]
    have hright : (∫ x, (ψ.postcompCLM Complex.ofRealCLM) x • v x) =
        ∫ x, ψ x • f' x m := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
        hx, smul_eq_mul, Complex.real_smul]
    rw [hleft, hright]
    exact (hw.2.2 ψ (ψ.smooth ⊤) hc (subset_univ _) m).symm
  have hcompact (ψ : 𝓢(E, ℂ)) (hc : HasCompactSupport (ψ : E → ℂ)) :
      (∂_{m} (u : 𝓢'(E, ℂ))) ψ = (v : 𝓢'(E, ℂ)) ψ := by
    have hsplit : ψ = (ψ.postcompCLM Complex.reCLM).postcompCLM Complex.ofRealCLM +
        Complex.I • (ψ.postcompCLM Complex.imCLM).postcompCLM Complex.ofRealCLM := by
      ext x
      simp only [add_apply, smul_apply, SchwartzMap.postcompCLM_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul]
      rw [mul_comm, Complex.re_add_im]
    conv_lhs => rw [hsplit]
    conv_rhs => rw [hsplit]
    simp only [map_add, map_smul]
    exact congrArg₂ (· + ·)
      (hreal (ψ.postcompCLM Complex.reCLM) (hc.comp_left (g := Complex.reCLM) rfl))
      (congrArg (Complex.I • ·)
        (hreal (ψ.postcompCLM Complex.imCLM) (hc.comp_left (g := Complex.imCLM) rfl)))
  ext ψ
  apply tendsto_nhds_unique
    (((∂_{m} (u : 𝓢'(E, ℂ))).continuous).tendsto ψ |>.comp
      (Pseudodifferential.CompactSchwartz.tendsto_truncate ψ))
  convert ((v : 𝓢'(E, ℂ)).continuous.tendsto ψ).comp
    (Pseudodifferential.CompactSchwartz.tendsto_truncate ψ) using 1
  · ext j
    exact hcompact _ (Pseudodifferential.CompactSchwartz.truncate_hasCompactSupport ψ j)
  · rfl

end JanetCartan.Mollification
