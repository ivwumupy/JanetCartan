module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Joint
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SymbolJets

/-!
# Finite-order Hamilton-flow continuity from scalar symbols

The flow part of `app:lem:common-hamilton-phase`: combine the checked ODE
comparison with `cNorm_vectorField_sub_le`. The symbol costs precisely one
more derivative than the requested joint flow norm. Common-domain existence
comes from the fixed low neighborhood; the parent retains initial-section,
inverse-chart, and phase assembly.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff
namespace JanetCartan.HamiltonPhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- `app:lem:common-hamilton-phase`: on a fixed compact inner joint cylinder,
scalar-symbol perturbations of order `m + 1` control actual Hamilton flows in
order `m`. The parent supplies the common flows and subsequently composes with
the varying initial sections; all ODE stability premises are discharged here. -/
theorem exists_cNorm_hamiltonFlow_sub_lt
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} {z₀ : E × E}
    {R r T ρ τ : ℝ} {Ψ₀ : (E × E) × ℝ → E × E}
    (hD : IsOpen D) (hRD : closedBall z₀ R ⊆ D) (hDH₀ : D ⊆ H₀.domain)
    (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hΨ₀ : ODE.IsSmoothFlowOn H₀.vectorField z₀ R r T Ψ₀)
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (H : HomogeneousSymbol E) (Ψ : (E × E) × ℝ → E × E),
      D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
      ODE.IsSmoothFlowOn H.vectorField z₀ R r T Ψ →
      cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.h z - H₀.h z) < δ →
      cNorm (closedBall z₀ ρ ×ˢ Icc (-τ) τ) m (Ψ - Ψ₀) < ε := by
  have hV₀ : ContDiffOn ℝ ∞ H₀.vectorField D :=
    H₀.contDiffOn_vectorField_of_subset hD hDH₀ (by simpa using hH₀)
  obtain ⟨δ, hδ, hstable⟩ := ODE.exists_cNorm_flow_sub_lt hD hRD hV₀ hΨ₀
    hρ hρr hτ hτT m hε
  have hm : 0 < (m + 1 : ℝ) := by positivity
  refine ⟨δ / (m + 1), div_pos hδ hm, ?_⟩
  intro H Ψ hDH hH hΨ hsmall
  apply hstable H.vectorField Ψ
    (H.contDiffOn_vectorField_of_subset hD hDH (by simpa using hH)) hΨ
  have hb := cNorm_vectorField_sub_le H H₀ hD hDH hDH₀ m
    (hH.of_le (by simp)) (hH₀.of_le (by simp)) (isCompact_closedBall z₀ R) hRD
  apply hb.trans_lt
  have := (lt_div_iff₀ hm).mp hsmall
  linarith
end JanetCartan.HamiltonPhase
