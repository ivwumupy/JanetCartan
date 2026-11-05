module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.ActualJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.CoefficientBounds

/-!
# Fixed frequency normalization and preservation of the full supports

The parameter order `k` spends at most `ρ^k L^k` in the coefficient bounds.
Since the graph regime has `L ≤ ρ`, extraction of `ρ^(2*k)` gives the original
spatial grades. This normalization is a constant scalar multiplication and
never divides by the complementary mask. Source:
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The actual full jet after extraction of the fixed frequency power `2*k`.
Its definition keeps the entire amplitude, including all original physical and
frequency cutoffs and the literal reverse weight. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def normalizedComplementaryCarrierJet (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (ψ : P → E → E → ℝ) (ρ : ℝ) (k : ℕ) (v : Fin k → P)
    (c : P) : FullAmplitude n r := fun x y η ↦
  ((ρ : ℂ) ^ (2 * k))⁻¹ • complementaryCarrierJet A q ζ ψ ρ k v c x y η

/-- Reconstruction of the actual differentiated amplitude from its fixed
frequency normalization. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem frequency_smul_normalizedComplementaryCarrierJet
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) (v : Fin k → P) (c : P) (x y η : E) :
    (ρ : ℂ) ^ (2 * k) • normalizedComplementaryCarrierJet A q ζ ψ ρ k v c x y η =
      complementaryCarrierJet A q ζ ψ ρ k v c x y η := by
  simp only [normalizedComplementaryCarrierJet, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hρ)), one_smul]

/-- Every original amplitude zero is preserved by the normalization; hence all
physical supports, chart exclusions, and frequency shoulders survive unchanged.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem normalizedComplementaryCarrierJet_eq_zero_of_amplitude_eq_zero
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) (x y η : E) (hA : A x y η = 0) :
    normalizedComplementaryCarrierJet A q ζ ψ ρ k v c x y η = 0 := by
  rw [normalizedComplementaryCarrierJet,
    complementaryCarrierJet_eq_zero_of_amplitude_eq_zero A q ζ ψ ρ k v c x y η hA,
    smul_zero]

/-- Closed joint support is contained in the original full amplitude support,
with all three physical variables present. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_normalizedComplementaryCarrierJet_subset
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) :
    tsupport (fun p : (E × E) × E ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v c p.1.1 p.1.2 p.2) ⊆
      tsupport (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) := by
  apply closure_mono
  intro p hp hz
  exact hp (normalizedComplementaryCarrierJet_eq_zero_of_amplitude_eq_zero
    A q ζ ψ ρ k v c p.1.1 p.1.2 p.2 hz)

/-- The complete closed complementary gap also survives the normalization.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_normalizedComplementaryCarrierJet_subset_far
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) (x y : E) :
    tsupport (fun η ↦ normalizedComplementaryCarrierJet A q ζ ψ ρ k v c x y η) ⊆
      {η | g * ρ ≤ ‖η - ρ • ζ c‖} := by
  exact (tsupport_smul_subset_right _ _).trans
    (tsupport_complementaryCarrierJet_subset_far A q ζ ψ hρ hq hζ k v x y)

/-- The existing auxiliary-selector identity applies exactly to the normalized
full jet. No original mask is inverted. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryAmplitude_auxiliarySelector_normalizedJet
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) {g : ℝ} (hg : 0 < g) (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) :
    complementaryAmplitude (normalizedComplementaryCarrierJet A q ζ ψ ρ k v c)
        (ζ c) ρ (fun δ ↦ auxiliaryComplementSelector n g hg (ρ⁻¹ • δ)) =
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v c := by
  have he := complementaryAmplitude_auxiliaryComplementSelector_jet A q ζ ψ ρ hg hq hζ k v
  funext x y η
  have hp := congrFun (congrFun (congrFun he x) y) η
  change _ • (((ρ : ℂ) ^ (2 * k))⁻¹ • _) = ((ρ : ℂ) ^ (2 * k))⁻¹ • _
  rw [smul_comm]
  exact congrArg (fun M : Matrix (Fin r) (Fin r) ℂ ↦ ((ρ : ℂ) ^ (2 * k))⁻¹ • M) hp

/-- Joint smoothness is preserved by the fixed frequency normalization. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_normalizedComplementaryCarrierJet
    {A : FullAmplitude n r} {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ))
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) (v : Fin k → P) :
    ContDiffOn ℝ ∞ (fun p : P × ((E × E) × E) ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v p.1 p.2.1.1 p.2.1.2 p.2.2)
      (C ×ˢ Set.univ) :=
  (contDiffOn_complementaryCarrierJet hC hζ hq hψ hA hρ k v).const_smul _

section ScalarBudget

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- After extraction of `ρ^(2*k)`, all joint scalar jets have their original
scale degree `j`, provided `L ≤ ρ`. The extracted exponent depends only on
parameter order, independently of target or source differentiation. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_normalizedCarrierPolynomial_joint_le
    {φ a : X → Y → ℂ} {C : Set X} {V : Set Y}
    (hC : IsOpen C) (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (C ×ˢ V))
    (P Q : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 1 ≤ ρ) (hLρ : L ≤ ρ)
    {z : X × Y} (hz : z ∈ C ×ˢ V) (N : ℕ)
    (hφjet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry φ) z‖ ≤ P j * L ^ j)
    (hajet : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry a) z‖ ≤ Q j * L ^ j)
    (k : ℕ) (v : Fin k → X) (j : ℕ) (hbudget : j + k ≤ N) :
    ‖iteratedFDeriv ℝ j (fun p : X × Y ↦ ((ρ : ℂ) ^ (2 * k))⁻¹ •
      ∑ b : CarrierJetBranch k, (ρ : ℂ) ^ carrierJetDegree b *
        carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z‖ ≤
      (∑ b : CarrierJetBranch k, carrierCoefficientBudget P Q k v b j) * L ^ j := by
  have hb (b : CarrierJetBranch k) : ContDiffAt ℝ j (fun p : X × Y ↦
      carrierJetCoefficient (fun c ↦ φ c p.2) (fun c ↦ a c p.2) k v b p.1) z :=
    ((contDiffOn_carrierJetCoefficient_joint hC hV hφ ha k v b).contDiffAt
      ((hC.prod hV).mem_nhds hz)).of_le (by simp)
  have hs := ContDiffAt.sum (s := Finset.univ) (fun b _ ↦
    (contDiffAt_const (c := (ρ : ℂ) ^ carrierJetDegree b)).mul (hb b))
  rw [iteratedFDeriv_const_smul_apply' hs, norm_smul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hρ)]
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hB : 0 ≤ ∑ b : CarrierJetBranch k, carrierCoefficientBudget P Q k v b j :=
    Finset.sum_nonneg fun b _ ↦ carrierCoefficientBudget_nonneg hP hQ k v b j
  calc
    _ ≤ (ρ ^ (2 * k))⁻¹ *
        ((∑ b : CarrierJetBranch k, carrierCoefficientBudget P Q k v b j) *
          ρ ^ k * L ^ (j + k)) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_carrierPolynomial_joint_le
        hC hV hφ ha P Q hP hL hρ hz N hφjet hajet k v j hbudget)
          (inv_nonneg.mpr (pow_nonneg hρ0.le _))
    _ ≤ (ρ ^ (2 * k))⁻¹ *
        ((∑ b : CarrierJetBranch k, carrierCoefficientBudget P Q k v b j) *
          ρ ^ k * (L ^ j * ρ ^ k)) := by
      rw [pow_add]
      gcongr
    _ = _ := by
      rw [show 2 * k = k + k by omega, pow_add]
      field_simp

end ScalarBudget

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
