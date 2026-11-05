module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.IntegralAlgebra

/-!
# The algebraic PDO contribution to the direct residual

Specialize the existing compact-frequency graph differentiation theorem to
the canonical phase, in physical covectors. The output is
P((1/i) Op(c)) = Op(Hc + (1/i) P_x c). All derivatives of the actual symbol
c = b₋₁ α and the full zeroth-order coefficient are retained. The input v
is the original source-masked input; no multiplier is moved across it.

This is the PDO step of `app:ch_regular_base:eq:energy-complete-residual`.
The complement identity and the retarded endpoint still have to be combined
for the actual sector, before taking the graph/PDO strong limits.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral KernelDifferentiation

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The symbol derivative at a fixed physical covector, including B₀.
For the algebraic correction its argument is the entire symbol b₋₁ α
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalSymbolApply (A : E → Fin n → Mat) (B : E → Mat)
    (c : E → E → Mat) (x ξ : E) : Mat :=
  (∑ a, A x a * partialDeriv (fun y ↦ c y ξ) x a) + B x * c x ξ

private theorem partialDeriv_canonicalPhase (x ξ : E) (a : Fin n) :
    partialDeriv (fun y ↦ inner ℝ y ξ) x a = ξ a := by
  have he : (fun y : E ↦ inner ℝ y ξ) = (innerSL ℝ ξ) := funext fun y ↦ real_inner_comm ξ y
  rw [partialDeriv, he, (innerSL ℝ ξ).fderiv]
  simp [EuclideanSpace.inner_single_right]

/-- The exact finite-cutoff algebraic PDO action with the physical 1/i
normalization. Joint smoothness and compact frequency/source supports discharge
all differentiation and integrability requirements through the existing graph
calculus. Neither Hc nor P_x c is dropped
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_inverseI_cutPDO
    (A : E → Fin n → Mat) (B : E → Mat) (c : E → E → Mat)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    {U : Set E} (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (U ×ˢ univ))
    (v : E → FV) (hv : ContDiff ℝ ∞ v) (hvcs : HasCompactSupport v)
    {x : E} (hx : x ∈ U) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ (1 / Complex.I) • graphOperator (fun z ξ ↦ inner ℝ z ξ)
        (fun z _ ξ ↦ θ ξ • c z ξ) v y) x =
      graphOperator (fun z ξ ↦ inner ℝ z ξ)
        (fun z _ ξ ↦ θ ξ • ((∑ a, (ξ a : ℂ) • A z a) * c z ξ +
          (1 / Complex.I) • physicalSymbolApply A B c z ξ)) v x := by
  have hphase : ContDiffOn ℝ ∞ (fun p : E × E ↦ inner ℝ p.1 p.2) (U ×ˢ univ) :=
    (contDiff_fst.inner ℝ contDiff_snd).contDiffOn
  have hcut : ContDiffOn ℝ ∞ (fun p : E × E ↦ θ p.2 • c p.1 p.2) (U ×ˢ univ) :=
    (hθ.comp contDiff_snd).contDiffOn.smul hc
  have hzero : ∀ z ∈ U, ∀ ξ ∉ tsupport θ, θ ξ • c z ξ = 0 := by
    intro z _ ξ hξ
    rw [image_eq_zero_of_notMem_tsupport hξ, zero_smul]
  have hg := ((contDiffOn_graphOperator_of_compact hU hθcs hphase hcut hzero hv hvcs).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [firstOrderApply_const_smul _ _ hg, one_div, Complex.inv_I]
  change physicalOperator A B (graphOperator (fun z ξ ↦ inner ℝ z ξ)
    (fun z _ ξ ↦ θ ξ • c z ξ) v) x = _
  rw [physicalOperator_graphOperator A B (fun z ξ ↦ inner ℝ z ξ)
    (fun z ξ ↦ θ ξ • c z ξ) v hU hθcs hphase hcut hzero hv hvcs hx]
  have hder (ξ : E) (a : Fin n) :
      partialDeriv (fun z ↦ θ ξ • c z ξ) x a = θ ξ • partialDeriv (fun z ↦ c z ξ) x a := by
    have hcx : DifferentiableAt ℝ (fun z ↦ c z ξ) x :=
      ((hc.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ ξ⟩)).comp x
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    simp only [partialDeriv, fderiv_fun_const_smul hcx, smul_apply]
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  congr 2
  simp only [partialDeriv_canonicalPhase, hder, transportRemainder, physicalSymbolApply,
    Matrix.mul_smul, ← Finset.smul_sum, ← smul_add]
  rw [smul_comm (-Complex.I) (θ ξ), ← smul_add]

end JanetCartan.CharacteristicTransport.CompleteResidual
