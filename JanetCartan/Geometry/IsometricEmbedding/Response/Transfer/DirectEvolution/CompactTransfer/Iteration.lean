module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.ProductRule
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Finite iteration of the actual compact joint transfer

Repeated integration by parts in `paper-v2.tex`, `new:eq:carrier-ibp`, using
the published ordered-action convention. These are actual integrals and actual
derivatives. Expanding the resulting integrands into coefficient expressions
and original input derivatives is a separate algebraic step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

open Pseudodifferential

variable {n : ℕ} {E F ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- The complete transferred integrand, including every coefficient and mask
derivative. It contains no frequency parameter (`new:eq:carrier-ibp`). -/
def transferredIntegrand (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (e : E) (g : E → CarrierVariables n → F) (q : E) (w : CarrierVariables n) : F :=
  fderiv ℝ (fun p ↦ g p w) q e -
    weightedDivergence b (transferCoefficient f w₀ e q) (g q) w

private theorem contDiffOn_integrationDerivative
    {U : Set E} {D : Set (CarrierVariables n)} (hU : IsOpen U) (hD : IsOpen D)
    {g : E → CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D)) (v : CarrierVariables n) :
    ContDiffOn ℝ ∞ (fun p : E × CarrierVariables n ↦ fderiv ℝ (g p.1) p.2 v)
      (U ×ˢ D) := by
  intro p hp
  have hj := hg.contDiffAt ((hU.prod hD).mem_nhds hp)
  have h : ContDiffAt ℝ ∞
      (fun z : (E × CarrierVariables n) × CarrierVariables n ↦ g z.1.1 z.2) (p, p.2) :=
    hj.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact ((h.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

/-- Joint smoothness is preserved by the literal transfer, on the original
open output/parameter domain and integration box (`new:eq:carrier-ibp`). -/
theorem contDiffOn_transferredIntegrand
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)} (hU : IsOpen U) (hD : IsOpen D)
    {g : E → CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D)) (e : E)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (transferredIntegrand b f w₀ e g)) (U ×ˢ D) := by
  apply ((contDiffOn_parameterFDeriv hU hD hg).clm_apply contDiffOn_const).sub
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_integrationDerivative hU hD
    (g := fun q w ↦ inner ℝ (b i) (transferCoefficient f w₀ e q w) • g q w)
    ((contDiffOn_const.inner ℝ hA).smul hg) (b i)

/-- The fixed compact integration support is preserved by each complete
transfer, and hence by every finite iteration (`new:eq:carrier-ibp`). -/
theorem support_transferredIntegrand_subset
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    {U : Set E} {K : Set (CarrierVariables n)} (hU : IsOpen U) (hK : IsClosed K)
    {g : E → CarrierVariables n → F}
    (hs : ∀ q ∈ U, Function.support (g q) ⊆ K) (e : E) :
    ∀ q ∈ U, Function.support (transferredIntegrand b f w₀ e g q) ⊆ K := by
  intro q hq w hw
  by_contra hn
  have hd := Function.notMem_support.mp
    (fun h ↦ hn (support_parameterFDeriv_subset hU hs hq e h))
  have hv := Function.notMem_support.mp (fun h ↦ hn
    (support_weightedDivergence_subset b (transferCoefficient f w₀ e q) hK (hs q hq) h))
  exact hw (by simp only [transferredIntegrand, hd, hv, sub_zero])

variable [FiniteDimensional ℝ E] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- Finite ordered differentiation of the actual compact oscillatory integral.
Each step applies the proved compact identity to the same phase and the actual
transferred integrand. Primitive critical geometry and smoothness of the
literal coefficient are the only phase inputs. Source: iteration of
`new:eq:carrier-ibp` in `app:ch_response:lem:energy-carrier-jets`. -/
theorem orderedTransferAction_integral_oscillation
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {g : E → CarrierVariables n → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D))
    (hs : ∀ q ∈ U, Function.support (g q) ⊆ K)
    (hw₀ : ∀ q ∈ U, DifferentiableAt ℝ w₀ q)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0)
    (h₀ : ∀ q ∈ U, w₀ q ∈ D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ρ : ℝ) (es : List E) {q : E} (hq : q ∈ U) :
    orderedTransferAction (fun e h p ↦ fderiv ℝ h p e) es
        (fun p ↦ ∫ w, oscillation f ρ p w • g p w) q =
      ∫ w, oscillation f ρ q w •
        orderedTransferAction (transferredIntegrand b f w₀) es g q w := by
  have hpres (es : List E) :
      ContDiffOn ℝ ∞
        (Function.uncurry (orderedTransferAction (transferredIntegrand b f w₀) es g))
        (U ×ˢ D) ∧
      ∀ q ∈ U, Function.support
        (orderedTransferAction (transferredIntegrand b f w₀) es g q) ⊆ K := by
    apply orderedTransferAction_preserves (transferredIntegrand b f w₀)
      (fun v ↦ ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ D) ∧
        ∀ q ∈ U, Function.support (v q) ⊆ K) _ es ⟨hg, hs⟩
    intro e v hv
    exact ⟨contDiffOn_transferredIntegrand b hU hD hv.1 e (hA e),
      support_transferredIntegrand_subset b f w₀ hU hK.isClosed hv.2 e⟩
  induction es generalizing q with
  | nil => rfl
  | cons e es ih =>
    have heq :
        orderedTransferAction (fun e h p ↦ fderiv ℝ h p e) es
          (fun p ↦ ∫ w, oscillation f ρ p w • g p w) =ᶠ[𝓝 q]
        (fun p ↦ ∫ w, oscillation f ρ p w •
          orderedTransferAction (transferredIntegrand b f w₀) es g p w) := by
      filter_upwards [hU.mem_nhds hq] with p hp
      exact ih hp
    change fderiv ℝ _ q e = _
    rw [heq.fderiv_eq]
    have hAs : ContDiffOn ℝ ∞ (transferCoefficient f w₀ e q) D := by
      have hcomp := (hA e).comp
        (f := fun w : CarrierVariables n ↦ (q, w))
        (s := D) (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hq, hw⟩)
      simpa only [Function.comp_def, Function.uncurry_def] using hcomp
    exact fderiv_integral_oscillation_smul b hU hD hcD hK hKD hf
      (hpres es).1 (hpres es).2 hq (hw₀ q hq) (hcritical q hq)
      (by filter_upwards [hU.mem_nhds hq] with p hp; exact hvalue p hp)
      (h₀ q hq) (hinv q hq) ρ e
      hAs

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
