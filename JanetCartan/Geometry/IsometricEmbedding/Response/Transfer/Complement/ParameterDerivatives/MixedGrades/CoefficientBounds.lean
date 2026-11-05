module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Primitive budgets for the frequency-independent coefficients

For the mixed amplitude input of `GraphDecay`, parameter differentiation costs
one primitive joint derivative at each step. This cost is independent of the
number of subsequent target or source derivatives. Source:
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

variable {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A partial parameter derivative is a full directional derivative on the
joint space. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem parameterFDeriv_eq_joint {f : X × Y → F} {z : X × Y}
    (hf : DifferentiableAt ℝ f z) (v : X) :
    fderiv ℝ (fun c ↦ f (c, z.2)) z.1 v = fderiv ℝ f z (v, 0) := by
  have h := hf.hasFDerivAt.comp (f := fun c : X ↦ (c, z.2)) z.1
    ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk (hasFDerivAt_const z.2 z.1))
  exact congrArg (fun L : X →L[ℝ] F ↦ L v) h.fderiv

/-- One parameter derivative costs precisely one additional joint jet, even
when subsequent derivatives include arbitrary physical/source directions.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_parameterFDeriv_le {f : X × Y → F} {U : Set (X × Y)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : X × Y} (hz : z ∈ U)
    (v : X) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun p : X × Y ↦ fderiv ℝ (fun c ↦ f (c, p.2)) p.1 v) z‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
  have he : (fun p : X × Y ↦ fderiv ℝ (fun c ↦ f (c, p.2)) p.1 v) =ᶠ[𝓝 z]
      (fun p ↦ fderiv ℝ f p (v, 0)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact parameterFDeriv_eq_joint ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt
      (by simp)) v
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  have hb := norm_iteratedFDeriv_clm_apply_const
    ((hf.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := ∞) (by simp))
    (c := (v, (0 : Y))) (n := j) (by simp)
  simpa only [norm_iteratedFDeriv_fderiv, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg v)] using hb

/-- Explicit finite coefficient budget from primitive phase and selector
profiles. The recursive profile uses only derivatives through `j + k` and has
no frequency, scale, datum or parameter value argument. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def carrierCoefficientBudget (P Q : ℕ → ℝ) :
    (k : ℕ) → (Fin k → X) → CarrierJetBranch k → ℕ → ℝ
  | 0, _, _, j => Q j
  | k + 1, v, .inl b, j => ‖v 0‖ * carrierCoefficientBudget P Q k (Fin.tail v) b (j + 1)
  | k + 1, v, .inr b, j => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * (‖v 0‖ * P (i + 1)) *
        carrierCoefficientBudget P Q k (Fin.tail v) b (j - i)

omit [NormedSpace ℝ X] in
/-- Nonnegativity of the finite coefficient budget for
`app:ch_response:thm:response-literal-transfer`. -/
theorem carrierCoefficientBudget_nonneg {P Q : ℕ → ℝ}
    (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j)
    (k : ℕ) (v : Fin k → X) (b : CarrierJetBranch k) (j : ℕ) :
    0 ≤ carrierCoefficientBudget P Q k v b j := by
  induction k generalizing j with
  | zero => exact hQ j
  | succ k ih =>
    cases b with
    | inl b => exact mul_nonneg (norm_nonneg _) (ih (Fin.tail v) b (j + 1))
    | inr b =>
        exact Finset.sum_nonneg fun i _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (norm_nonneg _) (hP _)))
            (ih (Fin.tail v) b (j - i))

/-- All joint coefficient jets have scale degree at most `j + k`. This is
proved from primitive joint phase/selector grades, not assumed for the modified
amplitude. At fixed parameter order `k`, only finitely many primitive profiles
are used at each spatial order `j`. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_carrierJetCoefficient_joint_le
    {φ a : X → Y → ℂ} {C : Set X} {V : Set Y}
    (hC : IsOpen C) (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (C ×ˢ V))
    (P Q : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {L : ℝ} (hL : 0 ≤ L) {z : X × Y} (hz : z ∈ C ×ˢ V)
    (N : ℕ)
    (hφjet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry φ) z‖ ≤ P j * L ^ j)
    (hajet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry a) z‖ ≤ Q j * L ^ j)
    (k : ℕ) (v : Fin k → X) (b : CarrierJetBranch k) (j : ℕ) (hbudget : j + k ≤ N) :
    ‖iteratedFDeriv ℝ j (fun p : X × Y ↦
      carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z‖ ≤
      carrierCoefficientBudget P Q k v b j * L ^ (j + k) := by
  induction k generalizing j with
  | zero =>
      change ‖iteratedFDeriv ℝ j (Function.uncurry a) z‖ ≤ Q j * L ^ (j + 0)
      simpa only [Nat.add_zero] using hajet j hbudget
  | succ k ih =>
    cases b with
    | inl b =>
        have hb := norm_iteratedFDeriv_parameterFDeriv_le (hC.prod hV)
          (contDiffOn_carrierJetCoefficient_joint hC hV hφ ha k (Fin.tail v) b) hz (v 0) j
        apply hb.trans
        have hi := mul_le_mul_of_nonneg_left (ih (Fin.tail v) b (j + 1) (by omega))
          (norm_nonneg (v 0))
        simpa only [carrierCoefficientBudget, mul_assoc, Nat.add_assoc, Nat.add_comm 1] using hi
    | inr b =>
        have hprod := norm_iteratedFDerivWithin_mul_le
          (contDiffOn_parameterFDeriv hC hV hφ (v 0))
          (contDiffOn_carrierJetCoefficient_joint hC hV hφ ha k (Fin.tail v) b)
          (hC.prod hV).uniqueDiffOn hz (n := j) (by simp)
        simp only [iteratedFDerivWithin_of_isOpen _ (hC.prod hV) hz] at hprod
        apply hprod.trans
        change _ ≤ (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (‖v 0‖ * P (i + 1)) *
          carrierCoefficientBudget P Q k (Fin.tail v) b (j - i)) * L ^ (j + (k + 1))
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Finset.mem_range_succ_iff.mp hi
        have hpd := (norm_iteratedFDeriv_parameterFDeriv_le (hC.prod hV) hφ hz (v 0) i).trans
          (mul_le_mul_of_nonneg_left (hφjet (i + 1) (by omega)) (norm_nonneg _))
        have hbd := ih (Fin.tail v) b (j - i) (by omega)
        calc
          _ ≤ (j.choose i : ℝ) * (‖v 0‖ * (P (i + 1) * L ^ (i + 1))) *
              (carrierCoefficientBudget P Q k (Fin.tail v) b (j - i) * L ^ (j - i + k)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpd (Nat.cast_nonneg _)) hbd
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (norm_nonneg _) (mul_nonneg (hP _) (pow_nonneg hL _))))
          _ = _ := by
            have hexp : i + 1 + (j - i + k) = j + (k + 1) := by omega
            rw [← hexp, pow_add]
            ring

/-- Summing the finite polynomial does not increase the frequency degree when
arbitrary joint spatial jets are taken. Only the parameter order `k` occurs in
`ρ ^ k`. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_carrierPolynomial_joint_le
    {φ a : X → Y → ℂ} {C : Set X} {V : Set Y}
    (hC : IsOpen C) (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (C ×ˢ V))
    (P Q : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 1 ≤ ρ) {z : X × Y} (hz : z ∈ C ×ˢ V)
    (N : ℕ)
    (hφjet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry φ) z‖ ≤ P j * L ^ j)
    (hajet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry a) z‖ ≤ Q j * L ^ j)
    (k : ℕ) (v : Fin k → X) (j : ℕ) (hbudget : j + k ≤ N) :
    ‖iteratedFDeriv ℝ j (fun p : X × Y ↦ ∑ b : CarrierJetBranch k,
      (ρ : ℂ) ^ carrierJetDegree b *
        carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z‖ ≤
      (∑ b : CarrierJetBranch k, carrierCoefficientBudget P Q k v b j) *
        ρ ^ k * L ^ (j + k) := by
  have hb (b : CarrierJetBranch k) : ContDiffAt ℝ j (fun p : X × Y ↦
      carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z :=
    ((contDiffOn_carrierJetCoefficient_joint hC hV hφ ha k v b).contDiffAt
      ((hC.prod hV).mem_nhds hz)).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply (fun b _ ↦ contDiffAt_const.mul (hb b))]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  change ‖iteratedFDeriv ℝ j (fun p : X × Y ↦ (ρ : ℂ) ^ carrierJetDegree b •
    carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hb b), norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hρ)]
  have hjet := norm_iteratedFDeriv_carrierJetCoefficient_joint_le
    hC hV hφ ha P Q hP hL hz N hφjet hajet k v b j hbudget
  calc
    _ ≤ ρ ^ k * (carrierCoefficientBudget P Q k v b j * L ^ (j + k)) :=
      mul_le_mul (pow_le_pow_right₀ hρ (carrierJetDegree_le b)) hjet
        (norm_nonneg _) (pow_nonneg (zero_le_one.trans hρ) _)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
