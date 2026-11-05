module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.Polynomial
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.AuxiliarySelector

/-!
# The polynomial expansion of the actual complementary amplitude

For `app:ch_response:thm:response-literal-transfer`, frequency and physical
covector stay fixed in parameter derivatives. The coefficient functions use
an independent normalized covector. Thus their dependence on frequency is only
through evaluation at `ρ⁻¹ η`; the displayed polynomial has degree at most the
parameter order. The generic full amplitude is never replaced by a selector
quotient, preserving in particular the literal reverse weight.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- Frequency-independent scalar coefficients for the actual complementary
jet. The last argument is the normalized physical covector, not the shifted
selector argument. Source: `app:ch_response:thm:response-literal-transfer`. -/
def complementaryJetPolynomialCoefficient (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (k : ℕ) (v : Fin k → P) (b : CarrierJetBranch k)
    (c : P) (x y ξ : E) : ℂ :=
  carrierJetCoefficient (fun d ↦ Complex.I * (ψ d x y : ℂ))
    (fun d ↦ 1 - q (ξ - ζ d)) k v b c

/-- The actual complementary carrier jet is a finite polynomial after the
carrier cancels exactly. No derivative of the uncancelled exponential enters
subsequent spatial estimates. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryCarrierJet_eq_polynomial
    (A : FullAmplitude n r) {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C)
    (hq : ContDiff ℝ ∞ q) {ρ : ℝ} (hρ : ρ ≠ 0)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ C) (x y η : E)
    (hψ : ContDiffOn ℝ ∞ (fun d ↦ ψ d x y) C) :
    complementaryCarrierJet A q ζ ψ ρ k v c x y η =
      (∑ b : CarrierJetBranch k, (ρ : ℂ) ^ carrierJetDegree b *
        complementaryJetPolynomialCoefficient q ζ ψ k v b c x y (ρ⁻¹ • η)) • A x y η := by
  have hφ : ContDiffOn ℝ ∞ (fun d ↦ Complex.I * (ψ d x y : ℂ)) C :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hψ)
  have ha : ContDiffOn ℝ ∞ (fun d ↦ 1 - q (ρ⁻¹ • η - ζ d)) C :=
    contDiffOn_const.sub (hq.comp_contDiffOn (contDiffOn_const.sub hζ))
  have hf : (fun d ↦ complementaryCarrierCoefficient q ζ ψ ρ d x y η) =
      fun d ↦ Complex.exp ((ρ : ℂ) * (Complex.I * (ψ d x y : ℂ))) *
        (1 - q (ρ⁻¹ • η - ζ d)) := by
    funext d
    simp only [complementaryCarrierCoefficient, parameterCarrierFactor,
      normalizedCarrierOffset_eq ζ hρ, Complex.ofReal_mul]
    congr 2
    ring
  unfold complementaryCarrierJet
  rw [hf, iteratedFDeriv_exp_mul_eq_carrierPolynomial hC hφ ha (ρ : ℂ) k v hc]
  have he : Complex.exp ((ρ : ℂ) * (Complex.I * (ψ c x y : ℂ))) =
      parameterCarrierFactor ψ ρ c x y := by
    unfold parameterCarrierFactor
    congr 1
    push_cast
    ring
  rw [he, ← mul_assoc, parameterCarrierFactor_neg_mul, one_mul]
  rfl

/-- Primitive joint phase/selector/carrier smoothness gives joint smoothness of
every frequency-independent polynomial coefficient on the open parameter
neighborhood. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_complementaryJetPolynomialCoefficient
    {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ} {C : Set P}
    (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ))
    (k : ℕ) (v : Fin k → P) (b : CarrierJetBranch k) :
    ContDiffOn ℝ ∞ (fun p : P × ((E × E) × E) ↦
      complementaryJetPolynomialCoefficient q ζ ψ k v b p.1 p.2.1.1 p.2.1.2 p.2.2)
      (C ×ˢ Set.univ) := by
  have hφ : ContDiffOn ℝ ∞ (fun p : P × ((E × E) × E) ↦
      Complex.I * (ψ p.1 p.2.1.1 p.2.1.2 : ℂ)) (C ×ˢ Set.univ) :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hψ.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)))
  have ha : ContDiffOn ℝ ∞ (fun p : P × ((E × E) × E) ↦
      1 - q (p.2.2 - ζ p.1)) (C ×ˢ Set.univ) :=
    contDiffOn_const.sub (hq.comp_contDiffOn
      (contDiffOn_snd.snd.sub (hζ.comp contDiffOn_fst (fun _ hp ↦ hp.1))))
  exact contDiffOn_carrierJetCoefficient_joint
    (φ := fun (c : P) (z : (E × E) × E) ↦ Complex.I * (ψ c z.1.1 z.1.2 : ℂ))
    (a := fun (c : P) (z : (E × E) × E) ↦ 1 - q (z.2 - ζ c)) hC isOpen_univ hφ ha k v b

/-- Joint smoothness of the actual full jet follows from the primitive phase,
carrier, selector and original amplitude. The parameter box may be any compact
subset of `C`. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_complementaryCarrierJet
    {A : FullAmplitude n r} {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ))
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) (v : Fin k → P) :
    ContDiffOn ℝ ∞ (fun p : P × ((E × E) × E) ↦
      complementaryCarrierJet A q ζ ψ ρ k v p.1 p.2.1.1 p.2.1.2 p.2.2)
      (C ×ˢ Set.univ) := by
  have hb (b : CarrierJetBranch k) : ContDiffOn ℝ ∞
      (fun p : P × ((E × E) × E) ↦ complementaryJetPolynomialCoefficient q ζ ψ k v b
        p.1 p.2.1.1 p.2.1.2 (ρ⁻¹ • p.2.2)) (C ×ˢ Set.univ) :=
    (contDiffOn_complementaryJetPolynomialCoefficient hC hζ hq hψ k v b).comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk
        (contDiffOn_snd.snd.const_smul ρ⁻¹))) (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)
  have hs := (ContDiffOn.sum (s := Finset.univ) (fun b _ ↦
    (contDiffOn_const (c := (ρ : ℂ) ^ carrierJetDegree b)).mul (hb b))).smul (hA.comp_contDiffOn contDiffOn_snd)
  apply hs.congr
  intro p hp
  exact complementaryCarrierJet_eq_polynomial A hC hζ hq hρ k v hp.1 _ _ _
    (hψ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun d hd ↦ ⟨hd, Set.mem_univ _⟩))

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
