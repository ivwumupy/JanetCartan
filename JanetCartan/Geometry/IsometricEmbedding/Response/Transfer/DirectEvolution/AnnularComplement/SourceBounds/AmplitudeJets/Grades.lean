module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Polynomial

/-!
# Fixed external losses before source differentiation

The vector carrier polynomial has frequency degree at most the external order
and joint scale degree at most source order plus external order. The constants
below are chosen before the phase, amplitude, scales and unit directions.
They are intermediate deductions for `norm_annularSourceIntegral_le`, not a
substitute for producing the literal elapsed-amplitude inputs from the original
symbol, both masks, beta, and envelope Sobolev profiles.

Source: `app:ch_response:lem:energy-carrier-jets` and the separate scales in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.ParameterDerivatives.MixedGrades
open JanetCartan.Localization
variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Unit-direction constants using the shared finite coefficient budget.
Only primitive phase and ORIGINAL amplitude profiles occur in this constant;
`j` is fixed before the source order `k`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def externalJetBudget (H Q : ℕ → ℝ) (j k : ℕ) : ℝ :=
  ∑ b : CarrierJetBranch j,
    carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b k

/-- Nonnegative constants for the normalized source-amplitude profile.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem externalJetBudget_nonneg {H Q : ℕ → ℝ}
    (hH : ∀ k, 0 ≤ H k) (hQ : ∀ k, 0 ≤ Q k) (j k : ℕ) :
    0 ≤ externalJetBudget H Q j k :=
  Finset.sum_nonneg fun b _ => carrierCoefficientBudget_nonneg hH hQ j _ b k

/-- Vector coefficient estimate from ORIGINAL joint phase/amplitude jets.
The single amplitude size `A` remains linear, and directions have norm at most
one. The fixed external loss is `K^j`, independent of source order.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_vectorCarrierCoefficient_joint_le
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → Z → ℂ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (H Q : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k) (_hQ : ∀ k, 0 ≤ Q k)
    {K A : ℝ} (hK : 0 ≤ K) (_hA : 0 ≤ A) {z : P × Z} (hz : z ∈ V ×ˢ U)
    (N : ℕ)
    (hphase : ∀ k ≤ N, ‖iteratedFDeriv ℝ k (Function.uncurry φ) z‖ ≤ H k * K ^ k)
    (hamplitude : ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Function.uncurry u) z‖ ≤ Q k * A * K ^ k)
    (j : ℕ) (v : Fin j → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    (b : CarrierJetBranch j) (k : ℕ) (hbudget : k + j ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q : P × Z =>
      vectorCarrierCoefficient (fun p => φ p q.2) (fun p => u p q.2) j v b q.1) z‖ ≤
      carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b k * A * K ^ (k + j) := by
  induction j generalizing k with
  | zero => simpa only [vectorCarrierCoefficient, carrierCoefficientBudget, Nat.add_zero, Function.uncurry_def]
      using hamplitude k hbudget
  | succ j ih =>
    cases b with
    | inl b =>
      have hc := norm_iteratedFDeriv_parameterFDeriv_le (hV.prod hU)
        (contDiffOn_vectorCarrierCoefficient_joint hV hU hφ hu j (Fin.tail v) b) hz (v 0) k
      have hi := ih (Fin.tail v) (fun i => hv i.succ) b (k + 1) (by omega)
      calc
        _ ≤ ‖v 0‖ * ‖iteratedFDeriv ℝ (k + 1) (fun q : P × Z =>
            vectorCarrierCoefficient (fun p => φ p q.2) (fun p => u p q.2)
              j (Fin.tail v) b q.1) z‖ := hc
        _ ≤ 1 * (carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b (k + 1) *
            A * K ^ (k + 1 + j)) :=
          mul_le_mul (hv 0) hi (norm_nonneg _) zero_le_one
        _ = _ := by
          simp only [carrierCoefficientBudget, norm_one, one_mul, Fin.tail_def]
          congr 2; omega
    | inr b =>
      have hp := norm_iteratedFDerivWithin_smul_le
        (Complement.ParameterDerivatives.MixedGrades.contDiffOn_parameterFDeriv hV hU hφ (v 0))
        (contDiffOn_vectorCarrierCoefficient_joint hV hU hφ hu j (Fin.tail v) b)
        (hV.prod hU).uniqueDiffOn hz (n := k) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ (hV.prod hU) hz] at hp
      apply hp.trans
      simp only [carrierCoefficientBudget, norm_one, one_mul, Fin.tail_def]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
      have hHi := hH (i + 1)
      have hd := norm_iteratedFDeriv_parameterFDeriv_le (hV.prod hU) hφ hz (v 0) i
      have hd' : ‖iteratedFDeriv ℝ i (fun q : P × Z =>
          fderiv ℝ (fun p => φ p q.2) q.1 (v 0)) z‖ ≤ H (i + 1) * K ^ (i + 1) :=
        hd.trans ((mul_le_mul (hv 0) (hphase (i + 1) (by omega))
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      have hb := ih (Fin.tail v) (fun i => hv i.succ) b (k - i) (by omega)
      calc
        _ ≤ (k.choose i : ℝ) * (H (i + 1) * K ^ (i + 1)) *
            (carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b (k - i) *
              A * K ^ (k - i + j)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg _)) hb
            (norm_nonneg _) (by positivity)
        _ = (k.choose i : ℝ) * H (i + 1) *
            carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b (k - i) *
              A * K ^ ((i + 1) + (k - i + j)) := by rw [pow_add]; ring
        _ = _ := by congr 2; omega

/-- Joint source/parameter derivatives of the finite polynomial. Its
frequency loss is `ρ^j` and its scale loss is `K^j`, both fixed before `k`.
Only original primitive joint profiles through `k+j` are used.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_vectorCarrierPolynomial_joint_le
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → Z → ℂ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (H Q : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k) (hQ : ∀ k, 0 ≤ Q k)
    {K A ρ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hρ : 1 ≤ ρ)
    {z : P × Z} (hz : z ∈ V ×ˢ U) (N : ℕ)
    (hphase : ∀ k ≤ N, ‖iteratedFDeriv ℝ k (Function.uncurry φ) z‖ ≤ H k * K ^ k)
    (hamplitude : ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Function.uncurry u) z‖ ≤ Q k * A * K ^ k)
    (j : ℕ) (v : Fin j → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    (k : ℕ) (hbudget : k + j ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q : P × Z => ∑ b : CarrierJetBranch j,
      (ρ : ℂ) ^ carrierJetDegree b •
        vectorCarrierCoefficient (fun p => φ p q.2) (fun p => u p q.2) j v b q.1) z‖ ≤
      externalJetBudget H Q j k * A * ρ ^ j * K ^ (k + j) := by
  have hb (b : CarrierJetBranch j) : ContDiffAt ℝ k (fun q : P × Z =>
      vectorCarrierCoefficient (fun p => φ p q.2) (fun p => u p q.2) j v b q.1) z :=
    ((contDiffOn_vectorCarrierCoefficient_joint hV hU hφ hu j v b).contDiffAt
      ((hV.prod hU).mem_nhds hz)).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply (fun b _ => (hb b).const_smul _)]
  apply (norm_sum_le _ _).trans
  unfold externalJetBudget
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  rw [iteratedFDeriv_const_smul_apply' (hb b), norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hρ)]
  have ht := norm_iteratedFDeriv_vectorCarrierCoefficient_joint_le hV hU hφ hu H Q hH hQ
    hK hA hz N hphase hamplitude j v hv b k hbudget
  calc
    _ ≤ ρ ^ j * (carrierCoefficientBudget H Q j (fun _ => (1 : ℝ)) b k * A * K ^ (k + j)) :=
      mul_le_mul (pow_le_pow_right₀ hρ (carrierJetDegree_le b)) ht
        (norm_nonneg _) (pow_nonneg (zero_le_one.trans hρ) _)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
