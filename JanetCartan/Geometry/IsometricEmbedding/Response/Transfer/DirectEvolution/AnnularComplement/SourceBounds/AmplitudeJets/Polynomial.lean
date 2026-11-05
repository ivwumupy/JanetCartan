module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.CoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.OrderedSpatial

/-!
# Vector carrier polynomials for actual external jets

The scalar carrier-polynomial API is extended only to the vector amplitudes
required by `norm_annularSourceIntegral_le`. It uses the same finite branches,
frequency degrees and primitive budgets. Source:
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.ParameterDerivatives.MixedGrades
open JanetCartan.Localization
variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Vector coefficients on the existing finite carrier branches. The phase
includes `I`; each branch differentiates the original amplitude or adds one
original phase derivative. There is no frequency argument in a coefficient.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def vectorCarrierCoefficient (φ : P → ℂ) (u : P → F) :
    (j : ℕ) → (Fin j → P) → CarrierJetBranch j → P → F
  | 0, _, _ => u
  | j + 1, v, .inl b => fun p =>
      fderiv ℝ (vectorCarrierCoefficient φ u j (Fin.tail v) b) p (v 0)
  | j + 1, v, .inr b => fun p =>
      fderiv ℝ φ p (v 0) • vectorCarrierCoefficient φ u j (Fin.tail v) b p

/-- The actual vector coefficients are smooth on the original open external
neighborhood (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_vectorCarrierCoefficient {V : Set P} (hV : IsOpen V)
    {φ : P → ℂ} {u : P → F} (hφ : ContDiffOn ℝ ∞ φ V) (hu : ContDiffOn ℝ ∞ u V)
    (j : ℕ) (v : Fin j → P) (b : CarrierJetBranch j) :
    ContDiffOn ℝ ∞ (vectorCarrierCoefficient φ u j v b) V := by
  induction j with
  | zero => exact hu
  | succ j ih =>
    cases b with
    | inl b =>
      exact ((ih (Fin.tail v) b).fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply
        contDiffOn_const
    | inr b =>
      exact ((hφ.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply
        contDiffOn_const).smul (ih (Fin.tail v) b)

/-- Finite polynomial identity for the actual vector-valued derivative.
Frequency degree is at most the external order by the shared
`carrierJetDegree_le`; subsequent source derivatives cannot increase it.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem iteratedFDeriv_exp_smul_eq_vectorCarrierPolynomial
    {V : Set P} (hV : IsOpen V) {φ : P → ℂ} {u : P → F}
    (hφ : ContDiffOn ℝ ∞ φ V) (hu : ContDiffOn ℝ ∞ u V)
    (t : ℂ) (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    iteratedFDeriv ℝ j (fun q => Complex.exp (t * φ q) • u q) p v =
      Complex.exp (t * φ p) • ∑ b : CarrierJetBranch j,
        t ^ carrierJetDegree b • vectorCarrierCoefficient φ u j v b p := by
  induction j generalizing p with
  | zero =>
    change Complex.exp (t * φ p) • u p =
      Complex.exp (t * φ p) • ∑ _ : Unit, t ^ 0 • u p
    simp
  | succ j ih =>
    have he : ContDiffOn ℝ ∞ (fun q => Complex.exp (t * φ q) • u q) V :=
      (contDiffOn_const.mul hφ).cexp.smul hu
    rw [(((he.of_le (show ((j + 1 : ℕ) : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
      (hV.mem_nhds hp)).differentiableAt_iteratedFDeriv
      (m := j) (by exact_mod_cast Nat.lt_succ_self j)).iteratedFDeriv_succ_apply_left']
    have hl : (fun q => iteratedFDeriv ℝ j
        (fun w => Complex.exp (t * φ w) • u w) q (Fin.tail v)) =ᶠ[𝓝 p]
        fun q => Complex.exp (t * φ q) • ∑ b : CarrierJetBranch j,
          t ^ carrierJetDegree b • vectorCarrierCoefficient φ u j (Fin.tail v) b q := by
      filter_upwards [hV.mem_nhds hp] with q hq
      exact ih (Fin.tail v) hq
    rw [hl.fderiv_eq]
    have hb (b : CarrierJetBranch j) :
        DifferentiableAt ℝ (vectorCarrierCoefficient φ u j (Fin.tail v) b) p :=
      ((contDiffOn_vectorCarrierCoefficient hV hφ hu j (Fin.tail v) b).contDiffAt
        (hV.mem_nhds hp)).differentiableAt (by simp)
    have hφd := (hφ.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
    have hsum : DifferentiableAt ℝ (fun q => ∑ b : CarrierJetBranch j,
        t ^ carrierJetDegree b • vectorCarrierCoefficient φ u j (Fin.tail v) b q) p :=
      DifferentiableAt.fun_sum fun b _ => (hb b).const_smul _
    rw [fderiv_fun_smul ((hφd.hasFDerivAt.const_mul t).cexp.differentiableAt) hsum,
      fderiv_fun_sum (u := Finset.univ) (A := fun b q => t ^ carrierJetDegree b • vectorCarrierCoefficient φ u j (Fin.tail v) b q) (fun b _ => (hb b).const_smul (t ^ carrierJetDegree b)),
      ((hφd.hasFDerivAt.const_mul t).cexp).fderiv]
    change _ = Complex.exp (t * φ p) •
      ∑ b : CarrierJetBranch j ⊕ CarrierJetBranch j,
        t ^ carrierJetDegree (k := j + 1) b • vectorCarrierCoefficient φ u (j + 1) v b p
    rw [Fintype.sum_sum_type]
    simp only [carrierJetDegree, vectorCarrierCoefficient, pow_succ,
      add_apply, smul_apply,
      sum_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, smul_add, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [fderiv_fun_const_smul (hb b)]
    simp only [smul_apply, smul_smul]
    congr 1
    congr 1
    ring

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Joint smoothness of the vector coefficients follows from the original
joint phase and amplitude, including all source spectators.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_vectorCarrierCoefficient_joint
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → Z → ℂ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (j : ℕ) (v : Fin j → P) (b : CarrierJetBranch j) :
    ContDiffOn ℝ ∞ (fun q : P × Z =>
      vectorCarrierCoefficient (fun p => φ p q.2) (fun p => u p q.2) j v b q.1) (V ×ˢ U) := by
  induction j with
  | zero => exact hu
  | succ j ih =>
    cases b with
    | inl b => exact Complement.ParameterDerivatives.MixedGrades.contDiffOn_parameterFDeriv hV hU (ih (Fin.tail v) b) (v 0)
    | inr b =>
      exact (Complement.ParameterDerivatives.MixedGrades.contDiffOn_parameterFDeriv hV hU hφ (v 0)).smul
        (ih (Fin.tail v) b)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
