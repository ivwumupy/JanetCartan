module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SymbolJets

/-!
# Root comparison with the order-zero symbol seminorm

The fixed transverse gap supplied by the common `C³` neighborhood is a
low-order bound. Once it is available, the value of the actual section root
depends only on the order-zero symbol perturbation. This is the base case of
the differentiated root comparison in `app:lem:common-hamilton-phase`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- On the fixed transverse interval, the normal root perturbation is bounded
by the scalar `C⁰` distance divided by the normal-velocity gap
(`app:lem:common-hamilton-phase`). The gap is supplied separately by the fixed
`C³` neighborhood; no root closeness is assumed. -/
theorem sectionRoot_sub_le_cNorm_zero
    (H H₀ : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    {D K : Set (E × E)} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ 0 H.h D) (hH₀ : ContDiffOn ℝ 0 H₀.h D)
    {p : InitialData U} {l u c s t : ℝ} (hc : 0 < c)
    (hseg : ∀ v ∈ Icc l u, transverseSectionState j ν (p, v) ∈ K)
    (hgap : ∀ v ∈ Icc l u, c ≤ |⟪H.hp (transverseSectionState j ν (p, v)), ν⟫_ℝ|)
    (hs : s ∈ Icc l u) (ht : t ∈ Icc l u)
    (hroot : H.h (transverseSectionState j ν (p, s)) = p.2.1)
    (hroot₀ : H₀.h (transverseSectionState j ν (p, t)) = p.2.1) :
    |s - t| ≤ cNorm K 0 (fun z ↦ H.h z - H₀.h z) / c := by
  have hd : ∀ v ∈ Icc l u,
      DifferentiableAt ℝ (sectionEnergyEquation H j ν) (p, v) := by
    intro v hv
    exact ((H.hasFDerivAt_h _ (hDH (hKD (hseg v hv)))).differentiableAt.comp _
      ((contDiff_transverseSectionState j ν).differentiable (by simp)).differentiableAt).sub
      (differentiable_fst.snd.fst.differentiableAt)
  have h := CharacteristicRoot.scalar_gap_mul_abs_sub_le hd
    (fun v hv ↦ by
      rw [scalarDerivative_sectionEnergyEquation H j ν (hDH (hKD (hseg v hv)))]
      exact hgap v hv) hs ht
  have hb := norm_symbol_jet_sub_le_cNorm H H₀ hD hH hH₀ hK hKD
    (show 0 ≤ 0 from le_rfl) (hseg t ht)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hroot₀] at hb
  simp only [sectionEnergyEquation, hroot, sub_self, sub_zero] at h
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm, abs_sub_comm] using h.trans hb

end JanetCartan.HamiltonPhase
