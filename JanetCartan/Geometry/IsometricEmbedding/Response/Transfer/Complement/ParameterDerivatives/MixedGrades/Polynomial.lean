module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.KernelJets

/-!
# Finite carrier polynomials before spatial differentiation

The fixed parameter derivative assertion in
`app:ch_response:thm:response-literal-transfer` requires cancellation of the
carrier before estimating spatial jets. The coefficients below are actual
successive derivatives and products of the phase and selector. They have no
frequency argument. The consumer is the mixed amplitude input `hAj` of
`forwardCompleteComplement_rapidDecay` and `reverseCompleteComplement_rapidDecay`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The finite binary choices in the parameter Leibniz rule: differentiate the
coefficient, or differentiate the carrier. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def CarrierJetBranch : ℕ → Type
  | 0 => Unit
  | k + 1 => CarrierJetBranch k ⊕ CarrierJetBranch k

instance carrierJetBranchFintype : (k : ℕ) → Fintype (CarrierJetBranch k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => by
      letI := carrierJetBranchFintype k
      exact inferInstanceAs (Fintype (CarrierJetBranch k ⊕ CarrierJetBranch k))

/-- Frequency degree of a term in the actual carrier expansion. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def carrierJetDegree : {k : ℕ} → CarrierJetBranch k → ℕ
  | 0, _ => 0
  | _ + 1, .inl b => carrierJetDegree b
  | _ + 1, .inr b => carrierJetDegree b + 1

/-- Frequency-independent coefficient in the actual differentiated carrier.
The complex phase includes the factor `I`; the primitive scalar amplitude is
the complementary selector. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def carrierJetCoefficient (φ a : X → ℂ) :
    (k : ℕ) → (Fin k → X) → CarrierJetBranch k → X → ℂ
  | 0, _, _ => a
  | k + 1, v, .inl b => fun z ↦
      fderiv ℝ (carrierJetCoefficient φ a k (Fin.tail v) b) z (v 0)
  | k + 1, v, .inr b => fun z ↦
      fderiv ℝ φ z (v 0) * carrierJetCoefficient φ a k (Fin.tail v) b z

/-- Every frequency degree is at most the parameter order, independently of
any subsequent spatial differentiation. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem carrierJetDegree_le {k : ℕ} (b : CarrierJetBranch k) :
    carrierJetDegree b ≤ k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases b with
    | inl b => exact (ih b).trans (Nat.le_succ _)
    | inr b => exact Nat.add_le_add_right (ih b) 1

/-- All coefficient functions are jointly smooth on the original open
neighborhood, derived from primitive smoothness. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_carrierJetCoefficient {φ a : X → ℂ} {U : Set X}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (k : ℕ) (v : Fin k → X) (b : CarrierJetBranch k) :
    ContDiffOn ℝ ∞ (carrierJetCoefficient φ a k v b) U := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    cases b with
    | inl b =>
        exact ((ih (Fin.tail v) b).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
          contDiffOn_const
    | inr b =>
        exact ((hφ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
          contDiffOn_const).mul (ih (Fin.tail v) b)

/-- Exact finite polynomial expansion of the actual iterated derivative of
`exp(t φ) a`, on an open neighborhood. No bound on a modified amplitude is an
input. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem iteratedFDeriv_exp_mul_eq_carrierPolynomial {φ a : X → ℂ} {U : Set X}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (t : ℂ) (k : ℕ) (v : Fin k → X) {z : X} (hz : z ∈ U) :
    iteratedFDeriv ℝ k (fun w ↦ Complex.exp (t * φ w) * a w) z v =
      Complex.exp (t * φ z) *
        ∑ b : CarrierJetBranch k, t ^ carrierJetDegree b * carrierJetCoefficient φ a k v b z := by
  induction k generalizing z with
  | zero =>
      change Complex.exp (t * φ z) * a z =
        Complex.exp (t * φ z) * ∑ _b : Unit, (t ^ 0 * a z)
      simp
  | succ k ih =>
    have he : ContDiffOn ℝ ∞ (fun w ↦ Complex.exp (t * φ w) * a w) U :=
      (contDiffOn_const.mul hφ).cexp.mul ha
    rw [(((he.of_le (show ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt_iteratedFDeriv
      (m := k) (by exact_mod_cast Nat.lt_succ_self k)).iteratedFDeriv_succ_apply_left']
    have hlocal : (fun w ↦ iteratedFDeriv ℝ k
        (fun u ↦ Complex.exp (t * φ u) * a u) w (Fin.tail v)) =ᶠ[𝓝 z]
        (fun w ↦ Complex.exp (t * φ w) * ∑ b : CarrierJetBranch k,
          t ^ carrierJetDegree b * carrierJetCoefficient φ a k (Fin.tail v) b w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih (Fin.tail v) hw
    rw [hlocal.fderiv_eq]
    have hb (b : CarrierJetBranch k) :
        DifferentiableAt ℝ (carrierJetCoefficient φ a k (Fin.tail v) b) z :=
      ((contDiffOn_carrierJetCoefficient hU hφ ha k (Fin.tail v) b).contDiffAt
        (hU.mem_nhds hz)).differentiableAt (by simp)
    have hφd := (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hsum : DifferentiableAt ℝ (fun w ↦ ∑ b : CarrierJetBranch k,
        t ^ carrierJetDegree b * carrierJetCoefficient φ a k (Fin.tail v) b w) z :=
      DifferentiableAt.fun_sum fun b _ ↦ (hb b).const_mul _
    rw [fderiv_fun_mul ((hφd.hasFDerivAt.const_mul t).cexp.differentiableAt) hsum,
      fderiv_fun_sum (fun b _ ↦ (hb b).const_mul _)]
    simp only [add_apply, smul_apply,
      sum_apply, smul_eq_mul]
    rw [((hφd.hasFDerivAt.const_mul t).cexp).fderiv]
    simp only [smul_apply, smul_eq_mul]
    simp only [fderiv_const_mul (hb _), smul_apply, smul_eq_mul]
    change _ = Complex.exp (t * φ z) *
      ∑ b : CarrierJetBranch k ⊕ CarrierJetBranch k,
        t ^ carrierJetDegree (k := k + 1) b * carrierJetCoefficient φ a (k + 1) v b z
    rw [Fintype.sum_sum_type]
    simp only [carrierJetDegree, carrierJetCoefficient, pow_succ]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Partial parameter differentiation preserves joint smoothness on the open
parameter/spatial neighborhood. This is the regularity step for the polynomial
coefficients in `app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_parameterFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X × Y → F} {C : Set X} {V : Set Y}
    (hC : IsOpen C) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f (C ×ˢ V)) (v : X) :
    ContDiffOn ℝ ∞ (fun p : X × Y ↦ fderiv ℝ (fun c ↦ f (c, p.2)) p.1 v)
      (C ×ˢ V) := by
  apply (hC.prod hV).contDiffOn_iff.mpr
  intro p hp
  have hh : ContDiffAt ℝ ∞
      (Function.uncurry (fun p : X × Y ↦ fun c : X ↦ f (c, p.2))) (p, p.1) :=
    (hf.contDiffAt ((hC.prod hV).mem_nhds hp)).comp (p, p.1)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hh.fderiv (m := ∞) contDiffAt_fst (by simp)).clm_apply contDiffAt_const

/-- Polynomial coefficients retain joint smoothness in all spectator variables,
although only the parameter directions are differentiated. This supplies the
regularity needed for subsequent target/source jets in
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_carrierJetCoefficient_joint {φ a : X → Y → ℂ}
    {C : Set X} {V : Set Y} (hC : IsOpen C) (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (C ×ˢ V))
    (k : ℕ) (v : Fin k → X) (b : CarrierJetBranch k) :
    ContDiffOn ℝ ∞ (fun p : X × Y ↦
      carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) (C ×ˢ V) := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    cases b with
    | inl b =>
        exact contDiffOn_parameterFDeriv hC hV (ih (Fin.tail v) b) (v 0)
    | inr b =>
        exact (contDiffOn_parameterFDeriv hC hV hφ (v 0)).mul (ih (Fin.tail v) b)

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
