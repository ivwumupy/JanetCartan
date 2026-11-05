module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.FullAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Leibniz.Splittings

/-!
# Finite carrier/source parameter expansion

The actual normalized source derivative is a finite sum of phase-only
polynomials times jets of the original source. The frequency degree is fixed
before spatial differentiation. These are the algebraic inputs to the
inactive-source Sobolev profile in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open MixedGrades
variable {p d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Frequency-independent phase-only coefficient in the finite source Leibniz
expansion (`app:ch_response:thm:response-literal-transfer`). -/
def sourcePhaseCoefficient (φ : P → E → ℝ) (vs : List P)
    (b : CarrierJetBranch vs.length) (c : P) (x : E) : ℂ :=
  carrierJetCoefficient (fun a ↦ Complex.I * (φ a x : ℂ)) (fun _ ↦ 1)
    vs.length vs.get b c

/-- Exact finite polynomial for the actual parameter derivative of the original
carrier (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterListJet_carrier_eq_polynomial {V : Set P} (hV : IsOpen V)
    {φ : P → E → ℝ} (ρ : ℝ) (x : E)
    (hφ : ContDiffOn ℝ ∞ (fun c ↦ φ c x) V) (vs : List P)
    {c : P} (hc : c ∈ V) :
    parameterListJet (fun a ↦ carrier ρ (φ a) x) vs c =
      carrier ρ (φ c) x * ∑ b : CarrierJetBranch vs.length,
        (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b c x := by
  have hp : ContDiffOn ℝ ∞ (fun a ↦ Complex.I * (φ a x : ℂ)) V :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)
  have he (a : P) : Complex.exp ((ρ : ℂ) * (Complex.I * (φ a x : ℂ))) =
      carrier ρ (φ a) x := by
    unfold carrier
    congr 1
    push_cast
    ring
  have h := iteratedFDeriv_exp_mul_eq_carrierPolynomial hV hp contDiffOn_const
    (a := fun _ ↦ 1) (ρ : ℂ) vs.length vs.get hc
  simpa only [mul_one, he, parameterListJet, sourcePhaseCoefficient] using h

/-- One finite term: a phase-only polynomial times an actual parameter jet
of the original source (`app:ch_response:thm:response-literal-transfer`). -/
def sourceCarrierLeibnizTerm (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (s : List P × List P) (c : P) (x : E) : F :=
  (∑ b : CarrierJetBranch s.1.length,
    (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ s.1 b c x) •
      parameterListJet (fun a ↦ f a x) s.2 c

/-- Finite carrier/source expansion of the SAME original source and phase.
All derivatives are actual iterated Fréchet derivatives; no expansion is an
input (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterCarrierJet_eq_leibnizPolynomial
    {V : Set P} (hV : IsOpen V) (ρ : ℝ) {φ : P → E → ℝ} {f : P → E → F}
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) (x : E)
    (hφ : ContDiffOn ℝ ∞ (fun a ↦ φ a x) V)
    (hf : ContDiffOn ℝ ∞ (fun a ↦ f a x) V) :
    parameterCarrierJet ρ φ f k v c x =
      ((parameterLeibnizSplittings (List.ofFn v)).map
        (fun s ↦ sourceCarrierLeibnizTerm ρ φ f s c x)).sum := by
  have hcarrier : ContDiffOn ℝ ∞ (fun a ↦ carrier ρ (φ a) x) V := by
    unfold carrier
    exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul hφ))).cexp
  unfold parameterCarrierJet parameterSourceFunction
  rw [← parameterListJet_ofFn, parameterListJet_smul _ _ hV hcarrier hf _ hc]
  rw [List.smul_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  dsimp only [Function.comp_apply]
  rw [parameterListJet_carrier_eq_polynomial hV ρ x hφ s.1 hc]
  simp only [smul_smul, ← mul_assoc, carrier_neg_mul,
    one_mul, sourceCarrierLeibnizTerm]

/-- Joint regularity of the frequency-independent coefficients follows from
the primitive phase (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_sourcePhaseCoefficient
    {V : Set P} {U : Set E} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (vs : List P) (b : CarrierJetBranch vs.length) :
    ContDiffOn ℝ ∞ (fun z : P × E ↦ sourcePhaseCoefficient φ vs b z.1 z.2)
      (V ×ˢ U) := by
  exact contDiffOn_carrierJetCoefficient_joint
    (φ := fun c x ↦ Complex.I * (φ c x : ℂ)) (a := fun _ _ ↦ 1) hV hU
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ))
    contDiffOn_const vs.length vs.get b

/-- Every mixed phase-polynomial jet has frequency degree at most the parameter
order, regardless of subsequent spatial differentiation. The only analytic
grades are those of the original joint phase;
`carrierCoefficientBudget` explicitly uses finitely many of them. Consumer: the
Sobolev profile of the finite source expansion in
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_sourceCarrierPolynomial_joint_le
    {V : Set P} {U : Set E} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (H : ℕ → ℝ) (hH : ∀ j, 0 ≤ H j)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 1 ≤ ρ) {z : P × E} (hz : z ∈ V ×ˢ U)
    (N : ℕ)
    (hphase : ∀ j ≤ N, ‖iteratedFDeriv ℝ j
      (Function.uncurry φ) z‖ ≤ H j * L ^ j)
    (vs : List P) (j : ℕ) (hbudget : j + vs.length ≤ N) :
    ‖iteratedFDeriv ℝ j (fun z : P × E ↦ ∑ b : CarrierJetBranch vs.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b z.1 z.2) z‖ ≤
      (∑ b : CarrierJetBranch vs.length,
        carrierCoefficientBudget H (fun i ↦ if i = 0 then 1 else 0)
          vs.length vs.get b j) * ρ ^ vs.length * L ^ (j + vs.length) := by
  have hp : ContDiffOn ℝ ∞ (Function.uncurry
      (fun c x ↦ Complex.I * (φ c x : ℂ))) (V ×ˢ U) :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)
  have hpbound : ∀ i ≤ N, ‖iteratedFDeriv ℝ i
      (Function.uncurry (fun c x ↦ Complex.I * (φ c x : ℂ))) z‖ ≤ H i * L ^ i := by
    intro i hi
    have he := norm_iteratedFDeriv_imaginaryPhase
      (hφ.contDiffAt ((hV.prod hU).mem_nhds hz)) i
    exact he.le.trans (hphase i hi)
  have hone : ∀ i ≤ N, ‖iteratedFDeriv ℝ i
      (Function.uncurry (fun (_ : P) (_ : E) ↦ (1 : ℂ))) z‖ ≤
        (if i = 0 then 1 else 0) * L ^ i := by
    intro i _
    cases i with
    | zero => simp [Function.uncurry_def]
    | succ i => simp [Function.uncurry_def, iteratedFDeriv_succ_const]
  exact norm_iteratedFDeriv_carrierPolynomial_joint_le
    (φ := fun c x ↦ Complex.I * (φ c x : ℂ)) (a := fun _ _ ↦ 1) hV hU
    hp contDiffOn_const H (fun i ↦ if i = 0 then 1 else 0) hH hL hρ hz N
    hpbound hone vs.length vs.get j hbudget

/-- Each term in the original-source expansion has frequency degree bounded
by the fixed total parameter order, independently of spatial differentiation
(`app:ch_response:thm:response-literal-transfer`). -/
theorem sourceCarrierLeibnizTerm_degree_le (k : ℕ) (v : Fin k → P)
    {s : List P × List P} (hs : s ∈ parameterLeibnizSplittings (List.ofFn v))
    (b : CarrierJetBranch s.1.length) : carrierJetDegree b ≤ k := by
  have horder := parameterLeibnizSplittings_orders hs
  rw [List.length_ofFn] at horder
  exact (carrierJetDegree_le b).trans (by omega)

/-- On the fixed compact parameter/spatial box, primitive phase smoothness
constructs all polynomial coefficient bounds before frequency, datum, and
parameter. Only the parameter order occurs in the frequency power, regardless
of the requested joint spatial order. Consumer: Sobolev multiplication of the
original source jets in `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_sourceCarrierPolynomial_joint_profile
    {V B : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hB : IsCompact B) (hBV : B ⊆ V) (hS : IsCompact S) (hSU : S ⊆ U)
    {φ : P → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U)) (vs : List P) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ j c, c ∈ B → ∀ x ∈ S,
        ‖iteratedFDeriv ℝ j (fun z : P × E ↦ ∑ b : CarrierJetBranch vs.length,
          (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b z.1 z.2) (c, x)‖ ≤
            C j * ρ ^ vs.length := by
  obtain ⟨H, hH, hbound⟩ := exists_carrierJet_profile_on_compact
    (hV.prod hU) (hB.prod hS) (Set.prod_mono hBV hSU) hφ
  refine ⟨fun j ↦ ∑ b : CarrierJetBranch vs.length,
    carrierCoefficientBudget H (fun i ↦ if i = 0 then 1 else 0) vs.length vs.get b j,
    ?_, ?_⟩
  · intro j
    apply Finset.sum_nonneg
    intro b _
    exact carrierCoefficientBudget_nonneg hH (fun i ↦ by split_ifs <;> positivity)
      vs.length vs.get b j
  · intro ρ hρ j c hc x hx
    simpa only [one_pow, mul_one] using norm_sourceCarrierPolynomial_joint_le
      hV hU hφ H hH (L := 1) zero_le_one hρ ⟨hBV hc, hSU hx⟩ (j + vs.length)
      (fun i _ ↦ by simpa only [one_pow, mul_one] using hbound i (c, x) ⟨hc, hx⟩)
      vs j le_rfl

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
