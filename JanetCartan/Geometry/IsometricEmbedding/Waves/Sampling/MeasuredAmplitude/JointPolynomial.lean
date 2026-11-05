module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Joint parameter jets of the actual WKB polynomial

The homotopy used by `app:ch_waves:eq:sampling-operator-bounds` must be smooth
through zero, including its parameter derivative. The inverse-frequency
formula does not provide that endpoint. Here the exact cubic polynomial keeps
all four actual coefficients and gives joint parameter/space/carrier jets.
The consumer is the measured amplitude in `CanonicalAmplitude`, followed by
`UniformNormalData.input_jets`. No bound on the resulting amplitude is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary.AmplitudeGrades.Polynomial
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

/-- Fixed scalar power seminorms used by the cubic homotopy
(`app:ch_waves:setup:oscillatory`). -/
def parameterPowerBudget (p k : ℕ) : ℝ :=
  cNorm (Icc (-1 : ℝ) 1) k (fun t : ℝ ↦ (t : ℂ) ^ p)

private theorem parameterPowerBudget_nonneg (p k : ℕ) : 0 ≤ parameterPowerBudget p k :=
  cNorm_nonneg _ _ _

private theorem jet_prelinear_contraction {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {V : Set F} (hV : IsOpen V) {f : F → H} (hf : ContDiffOn ℝ ∞ f V)
    {x : E} (hx : L x ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (L y)) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  have hh := norm_iteratedFDeriv_preAffine_le L 0 hV hf (by simpa using hx) k
  simpa only [add_zero] using hh.trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL))

private theorem jet_parameterPower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (x : E) (p k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × E ↦ (q.1 : ℂ) ^ p) (t, x)‖ ≤
      parameterPowerBudget p k := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ ↦ (t : ℂ) ^ p) := Complex.ofRealCLM.contDiff.pow p
  apply (jet_prelinear_contraction (ContinuousLinearMap.fst ℝ ℝ E)
    (ContinuousLinearMap.norm_fst_le _ _ _) isOpen_univ hs.contDiffOn (mem_univ _) k).trans
  exact norm_iteratedFDeriv_le_cNorm isCompact_Icc (hs.of_le (by simp)) ht le_rfl

private theorem jet_parameterPower_smul {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]
    {V : Set E} (hV : IsOpen V) {f : E → H} (hf : ContDiffOn ℝ ∞ f V)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {x : E} (hx : x ∈ V)
    {L : ℝ} (hL : 1 ≤ L) {b : ℕ} {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k)
    (hjet : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ A k * L ^ (k - b)) (p k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × E ↦ (q.1 : ℂ) ^ p • f q.2) (t, x)‖ ≤
      productProfile (ContinuousLinearMap.lsmul ℝ ℂ (E := H)) (parameterPowerBudget p) A k * L ^ (k - b) := by
  apply jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℂ (E := H)) (isOpen_univ.prod hV)
    (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_fst |>.pow p) (hf.comp contDiffOn_snd (fun q hq ↦ hq.2))
    (show (t, x) ∈ (univ : Set ℝ) ×ˢ V from ⟨mem_univ _, hx⟩)
    hL (parameterPowerBudget_nonneg p) hA
  · intro j
    exact (jet_parameterPower ht x p j).trans
      (le_mul_of_one_le_right (parameterPowerBudget_nonneg p j) (one_le_pow₀ hL))
  · intro j
    exact (jet_prelinear_contraction (ContinuousLinearMap.snd ℝ ℝ E)
      (ContinuousLinearMap.norm_snd_le _ _ _) hV hf hx j).trans (hjet j)

/-- Fixed joint budget for the exact cubic WKB polynomial. Its constants
precede the scale, frequency and all coefficient fields. It is used at joint
order `20*(n+1)+1`, allowing the additional epsilon derivative in
`app:ch_waves:setup:oscillatory`. -/
def jointPolynomialBudget (n N : ℕ) (C A₀ A₁ B₀ B₁ : ℕ → ℝ) (k : ℕ) : ℝ :=
  productProfile (normalTensor n N) C A₀ k +
    (productProfile (ContinuousLinearMap.lsmul ℝ ℂ (E := Matrix (Fin N) (Fin n) ℂ))
        (parameterPowerBudget 1) (correctionOneProfile n N C A₀ A₁ B₀) k +
      productProfile (ContinuousLinearMap.lsmul ℝ ℂ (E := Matrix (Fin N) (Fin n) ℂ))
        (parameterPowerBudget 2) (correctionTwoProfile n N C A₁ B₀ B₁) k +
      productProfile (ContinuousLinearMap.lsmul ℝ ℂ (E := Matrix (Fin N) (Fin n) ℂ))
        (parameterPowerBudget 3) (differentiatedProfile n N B₁) k)

/-- Nonnegativity of the joint polynomial constants
(`app:ch_waves:setup:oscillatory`). -/
theorem jointPolynomialBudget_nonneg (n N : ℕ) {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ k, 0 ≤ C k) (hA₀ : ∀ k, 0 ≤ A₀ k) (hA₁ : ∀ k, 0 ≤ A₁ k)
    (hB₀ : ∀ k, 0 ≤ B₀ k) (hB₁ : ∀ k, 0 ≤ B₁ k) (k : ℕ) :
    0 ≤ jointPolynomialBudget n N C A₀ A₁ B₀ B₁ k := by
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁
  exact add_nonneg (productProfile_nonneg _ hC hA₀ k)
    (add_nonneg (add_nonneg
      (productProfile_nonneg _ (parameterPowerBudget_nonneg 1) (fun j ↦ (hc j).2.1) k)
      (productProfile_nonneg _ (parameterPowerBudget_nonneg 2) (fun j ↦ (hc j).2.2.1) k))
      (productProfile_nonneg _ (parameterPowerBudget_nonneg 3)
        (fun j ↦ mul_nonneg (norm_nonneg (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N)) (hB₁ (j + 1))) k))

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual derivative polynomial is jointly smooth across parameter zero;
all geometric coefficients are unchanged (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_joint_derivativePolynomial
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hV₁ : ContDiffOn ℝ ∞ V₁ Ω) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Z) ↦
      derivativePolynomial q.1 ξ ν₀ ν₁ V₀ V₁ q.2) (univ ×ˢ Ω) := by
  have hsnd : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Z) ↦ q.2) (univ ×ˢ Ω) :=
    contDiffOn_snd
  have hp := (contDiffOn_normalTensor hξ hν₀).neg.comp hsnd
    (fun q hq ↦ hq.2 : MapsTo Prod.snd (univ ×ˢ Ω) Ω)
  have h1 := (contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀).comp hsnd
    (fun q hq ↦ hq.2 : MapsTo Prod.snd (univ ×ˢ Ω) Ω)
  have h2 := (contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁).comp hsnd
    (fun q hq ↦ hq.2 : MapsTo Prod.snd (univ ×ˢ Ω) Ω)
  have h3 := (contDiffOn_physicalJacobian hΩ hV₁).comp hsnd
    (fun q hq ↦ hq.2 : MapsTo Prod.snd (univ ×ˢ Ω) Ω)
  have ht : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Z) ↦ (q.1 : ℂ))
      (univ ×ˢ Ω) := Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_fst
  exact hp.add (((ht.smul h1).add ((ht.pow 2).smul h2)).add ((ht.pow 3).smul h3))

/-- Joint jets in the inverse frequency and all original physical/carrier
variables, including parameter zero and negative parameters. This proves the
open-extension budget from the geometric coefficient profiles, rather than
assuming the measured homotopy's jets (`app:ch_waves:setup:oscillatory`). -/
theorem norm_joint_derivativePolynomial_le
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hV₁ : ContDiffOn ℝ ∞ V₁ Ω)
    {w : Euclidean n × Z} (hw : w ∈ Ω) {τ L : ℝ}
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hL : 1 ≤ L) {b : ℕ}
    {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ k, 0 ≤ C k) (hA₀ : ∀ k, 0 ≤ A₀ k) (hA₁ : ∀ k, 0 ≤ A₁ k)
    (hB₀ : ∀ k, 0 ≤ B₀ k) (hB₁ : ∀ k, 0 ≤ B₁ k)
    (hpξ : ∀ k, ‖iteratedFDeriv ℝ k ξ w‖ ≤ C k * L ^ (k - (b + 3)))
    (hpν₀ : ∀ k, ‖iteratedFDeriv ℝ k ν₀ w‖ ≤ A₀ k * L ^ (k - (b + 2)))
    (hpν₁ : ∀ k, ‖iteratedFDeriv ℝ k ν₁ w‖ ≤ A₁ k * L ^ (k - (b + 1)))
    (hpV₀ : ∀ k, ‖iteratedFDeriv ℝ k V₀ w‖ ≤ B₀ k * L ^ (k - (b + 2)))
    (hpV₁ : ∀ k, ‖iteratedFDeriv ℝ k V₁ w‖ ≤ B₁ k * L ^ (k - (b + 1))) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × (Euclidean n × Z) ↦
      derivativePolynomial q.1 ξ ν₀ ν₁ V₀ V₁ q.2) (τ, w)‖ ≤
      jointPolynomialBudget n N C A₀ A₁ B₀ B₁ k * L ^ (k - b) := by
  have hCj := jet_lower_baseline hL hC (by omega : b ≤ b + 3) hpξ
  have hA₀j := jet_lower_baseline hL hA₀ (by omega : b ≤ b + 2) hpν₀
  have h1 := contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀
  have h2 := contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁
  have h3 := contDiffOn_physicalJacobian hΩ hV₁
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁
  have hj1 (j : ℕ) := jet_correctionOne_profile hΩ hξ hν₀ hν₁ hV₀ hw hL hC hA₁ hB₀
    hCj (jet_lower_baseline hL hA₀ (by omega : b + 1 ≤ b + 2) hpν₀)
    (jet_lower_baseline hL hA₁ (by omega : b ≤ b + 1) hpν₁)
    (jet_lower_baseline hL hB₀ (by omega : b ≤ b + 2) hpV₀) j
  have hj2 (j : ℕ) := jet_correctionTwo_profile hΩ hξ hν₁ hV₀ hV₁ hw hL hC hB₁
    hCj hpν₁ (jet_lower_baseline hL hB₀ (by omega : b + 1 ≤ b + 2) hpV₀)
    (jet_lower_baseline hL hB₁ (by omega : b ≤ b + 1) hpV₁) j
  have hj3 (j : ℕ) : ‖iteratedFDeriv ℝ j (physicalJacobian V₁) w‖ ≤
      differentiatedProfile n N B₁ j * L ^ (j - b) := by
    apply (jet_physicalJacobian_le (hV₁.contDiffAt (hΩ.mem_nhds hw)) j).trans
    simpa only [show j + 1 - (b + 1) = j - b by omega, differentiatedProfile,
      mul_assoc] using mul_le_mul_of_nonneg_left (hpV₁ (j + 1))
        (norm_nonneg (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N))
  have h1b := jet_parameterPower_smul hΩ h1 hτ hw hL
    (fun j ↦ (hc j).2.1) hj1 1 k
  have h2b := jet_parameterPower_smul hΩ h2 hτ hw hL
    (fun j ↦ (hc j).2.2.1) hj2 2 k
  have h3b := jet_parameterPower_smul hΩ h3 hτ hw hL
    (fun j ↦ mul_nonneg (norm_nonneg (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N)) (hB₁ (j + 1))) hj3 3 k
  have hpb : ‖iteratedFDeriv ℝ k (fun q : ℝ × (Euclidean n × Z) ↦
      -(normalTensor n N (ξ q.2) (ν₀ q.2))) (τ, w)‖ ≤
      productProfile (normalTensor n N) C A₀ k * L ^ (k - b) := by
    rw [show (fun q : ℝ × (Euclidean n × Z) ↦ -(normalTensor n N (ξ q.2) (ν₀ q.2))) =
      -(fun q ↦ normalTensor n N (ξ q.2) (ν₀ q.2)) from rfl,
      iteratedFDeriv_neg_apply, norm_neg]
    exact (jet_prelinear_contraction (ContinuousLinearMap.snd ℝ ℝ (Euclidean n × Z))
      (ContinuousLinearMap.norm_snd_le _ _ _) hΩ
      (contDiffOn_normalTensor hξ hν₀) hw k).trans
      (jet_bilinear_le (normalTensor n N) hΩ hξ hν₀ hw hL hC hA₀ hCj hA₀j k)
  have lift {f : Euclidean n × Z → Matrix (Fin N) (Fin n) ℂ} (hf : ContDiffOn ℝ ∞ f Ω) :
      ContDiffAt ℝ ∞ (fun q : ℝ × (Euclidean n × Z) ↦ f q.2) (τ, w) :=
    (hf.contDiffAt (hΩ.mem_nhds hw)).comp _ contDiffAt_snd
  have ht : ContDiffAt ℝ ∞ (fun q : ℝ × (Euclidean n × Z) ↦ (q.1 : ℂ)) (τ, w) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_fst
  have hs1 := ht.smul (lift h1)
  have hs2 := (ht.pow 2).smul (lift h2)
  have hs3 := (ht.pow 3).smul (lift h3)
  simp only [Pi.smul_def'] at hs1 hs2 hs3
  have hh := (jet_add_le (lift (contDiffOn_normalTensor hξ hν₀)).neg
    ((hs1.add hs2).add hs3) k).trans
    (add_le_add hpb ((jet_add_le (hs1.add hs2) hs3 k).trans
      (add_le_add ((jet_add_le hs1 hs2 k).trans (add_le_add (by simpa only [pow_one, Pi.smul_apply] using h1b) h2b)) h3b)))
  exact hh.trans_eq (by unfold jointPolynomialBudget differentiatedProfile; ring)

end JanetCartan.Sampling.MeasuredAmplitude
