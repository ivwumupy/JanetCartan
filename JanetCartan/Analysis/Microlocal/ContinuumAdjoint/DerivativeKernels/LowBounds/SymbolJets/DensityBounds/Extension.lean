module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds

/-!
# Extending the weighted density estimate off its primitive support buffer

These deductions use the published buffered extension for
`app:ch_background:prop:bg-adjoint`. The quantitative estimate on the closed
buffer is a separate primitive-jet obligation.
-/

@[expose] public noncomputable section

open Set Function
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow

variable {n : ℕ}

/-- Every density jet vanishes outside the closed image of the primitive
support buffer. This permits the high-frequency estimate to be imposed only
on that buffer (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedFDeriv_inverseDensity_eq_zero_of_not_mem_image
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    {L : Set (JointVariables n)} (h : PrimitiveRegularity g a m)
    (hb : BufferedSupport g a L) {p : JointVariables n} (hp : p ∉ g.push '' L)
    (j : ℕ) : iteratedFDeriv ℝ j (inverseDensity g a m) p = 0 := by
  have ht : tsupport (inverseDensity g a m) ⊆ g.push '' L :=
    closure_minimal (support_inverseDensity_subset h hb) hb.image_closed
  have he := notMem_tsupport_iff_eventuallyEq.mp (fun hm ↦ hp (ht hm))
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- Restriction of the joint finite jet bound to a fixed spectator costs
no additional constant. The local premise is the estimate on the closed
primitive buffer, still to be supplied by the weighted calculation
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_iteratedFDeriv_inverseDensity_section_le
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    {L : Set (JointVariables n)} (h : PrimitiveRegularity g a m)
    (hb : BufferedSupport g a L) {K : Set (Euclidean 2)} {j : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hjet : ∀ p ∈ g.push '' L, p.2 ∈ K →
      ‖iteratedFDeriv ℝ j (inverseDensity g a m) p‖ ≤ B)
    (p : Variables n) (v : Euclidean 2) (hv : v ∈ K) :
    ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤ B := by
  let I : Variables n →L[ℝ] JointVariables n := (ContinuousLinearMap.id ℝ _).prod 0
  have hI : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simp [I, Prod.norm_def]
  have hjoint : ‖iteratedFDeriv ℝ j (inverseDensity g a m) (p, v)‖ ≤ B := by
    by_cases hp : (p, v) ∈ g.push '' L
    · exact hjet (p, v) hp hv
    · rw [iteratedFDeriv_inverseDensity_eq_zero_of_not_mem_image h hb hp, norm_zero]
      exact hB
  have hf : ContDiff ℝ ∞ (fun q : JointVariables n ↦
      inverseDensity g a m ((0, v) + q)) :=
    (inverseDensity_contDiff h hb).comp (contDiff_const.add contDiff_id)
  have hcomp := Pseudodifferential.norm_iteratedFDeriv_comp_linear_le I
    (fun q ↦ inverseDensity g a m ((0, v) + q)) hf j p
  simp only [iteratedFDeriv_comp_add_left'] at hcomp
  have he : (fun q ↦ inverseDensity g a m ((0, v) + q)) ∘ I =
      (fun q ↦ inverseDensity g a m (q, v)) := by
    funext q
    simp [I]
  rw [he] at hcomp
  have heval : (0, v) + I p = (p, v) := by simp [I]
  rw [heval] at hcomp
  exact hcomp.trans ((mul_le_mul hjoint (pow_le_one₀ (norm_nonneg I) hI)
    (by positivity) hB).trans_eq (mul_one B))

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
