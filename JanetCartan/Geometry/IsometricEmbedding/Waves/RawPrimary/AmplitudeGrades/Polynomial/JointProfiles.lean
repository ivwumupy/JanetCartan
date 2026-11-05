module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Bounds

/-!
# The retained total-joint profiles of the WKB polynomial

Leading coefficients have baseline `rpar+2`, correction coefficients
`rpar+1`, and the phase covector `rpar+3`. The resulting displacement has
baseline `rpar+1`, the first error coefficient `rpar+1`, and the derivative
and complete error have baseline `rpar`. In particular this does not supply
the stronger `rpar+2` input of the differentiated-slice consumer.

All profile constants are fixed before the scale, frequency, and coefficient
fields (`app:ch_waves:thm:wkb`, `app:ch_waves:eq:WKB-amplitude-difference`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

/-- The fixed one-derivative Frobenius coefficient profile
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def differentiatedProfile (n N : ℕ) (A : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖differentialMatrix n N‖ * A (j + 1)

/-- Fixed first error coefficient constants
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def correctionOneProfile (n N : ℕ) (C A₀ A₁ B₀ : ℕ → ℝ) (j : ℕ) : ℝ :=
  productProfile (normalTensor n N) C A₁ j +
    (productProfile (normalTensor n N) C B₀ j + differentiatedProfile n N A₀ j)

/-- Fixed second error coefficient constants
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def correctionTwoProfile (n N : ℕ) (C A₁ B₀ B₁ : ℕ → ℝ) (j : ℕ) : ℝ :=
  (productProfile (normalTensor n N) C B₁ j + differentiatedProfile n N A₁ j) +
    differentiatedProfile n N B₀ j

/-- Fixed complete error constants, including the cubic coefficient
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def errorProfile (n N : ℕ) (C A₀ A₁ B₀ B₁ : ℕ → ℝ) (j : ℕ) : ℝ :=
  correctionOneProfile n N C A₀ A₁ B₀ j + correctionTwoProfile n N C A₁ B₀ B₁ j +
    differentiatedProfile n N B₁ j

/-- Fixed derivative constants including the literal leading tensor
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def derivativeProfile (n N : ℕ) (C A₀ A₁ B₀ B₁ : ℕ → ℝ) (j : ℕ) : ℝ :=
  productProfile (normalTensor n N) C A₀ j + errorProfile n N C A₀ A₁ B₀ B₁ j

/-- Positivity of all fixed polynomial constants
(`app:ch_waves:thm:wkb`). -/
theorem polynomialProfiles_nonneg (n N : ℕ) {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (j : ℕ) :
    0 ≤ displacementProfile A₀ A₁ B₀ B₁ j ∧
      0 ≤ correctionOneProfile n N C A₀ A₁ B₀ j ∧
      0 ≤ correctionTwoProfile n N C A₁ B₀ B₁ j ∧
      0 ≤ errorProfile n N C A₀ A₁ B₀ B₁ j ∧
      0 ≤ derivativeProfile n N C A₀ A₁ B₀ B₁ j := by
  have hd (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) : 0 ≤ differentiatedProfile n N A j :=
    mul_nonneg (norm_nonneg (differentialMatrix n N)) (hA _)
  have h1 : 0 ≤ correctionOneProfile n N C A₀ A₁ B₀ j :=
    add_nonneg (productProfile_nonneg _ hC hA₁ _) (add_nonneg
      (productProfile_nonneg _ hC hB₀ _) (hd _ hA₀))
  have h2 : 0 ≤ correctionTwoProfile n N C A₁ B₀ B₁ j :=
    add_nonneg (add_nonneg (productProfile_nonneg _ hC hB₁ _) (hd _ hA₁)) (hd _ hB₀)
  have he : 0 ≤ errorProfile n N C A₀ A₁ B₀ B₁ j :=
    add_nonneg (add_nonneg h1 h2) (hd _ hB₁)
  exact ⟨add_nonneg (add_nonneg (hA₀ _) (add_nonneg (hB₀ _) (hA₁ _))) (hB₁ _),
    h1, h2, he, add_nonneg (productProfile_nonneg _ hC hA₀ _) he⟩

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The first error coefficient has one fewer retained derivative than
its leading normal (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_correctionOne_profile
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    {w : Euclidean n × Z} (hw : w ∈ Ω) {L : ℝ} (hL : 1 ≤ L) {b : ℕ}
    {C A₀ A₁ B₀ : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hA₁ : ∀ j, 0 ≤ A₁ j) (hB₀ : ∀ j, 0 ≤ B₀ j)
    (hpξ : ∀ j, ‖iteratedFDeriv ℝ j ξ w‖ ≤ C j * L ^ (j - b))
    (hpν₀ : ∀ j, ‖iteratedFDeriv ℝ j ν₀ w‖ ≤ A₀ j * L ^ (j - (b + 1)))
    (hpν₁ : ∀ j, ‖iteratedFDeriv ℝ j ν₁ w‖ ≤ A₁ j * L ^ (j - b))
    (hpV₀ : ∀ j, ‖iteratedFDeriv ℝ j V₀ w‖ ≤ B₀ j * L ^ (j - b)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ ≤
      correctionOneProfile n N C A₀ A₁ B₀ j * L ^ (j - b) := by
  have ht := jet_bilinear_le (normalTensor n N) hΩ hξ hν₁ hw hL hC hA₁ hpξ hpν₁ j
  have hv := jet_bilinear_le (normalTensor n N) hΩ hξ hV₀ hw hL hC hB₀ hpξ hpV₀ j
  have hd := mul_le_mul_of_nonneg_left (hpν₀ (j + 1)) (norm_nonneg (differentialMatrix n N))
  rw [show j + 1 - (b + 1) = j - b by omega] at hd
  exact (jet_correctionOne_le hΩ hξ hν₀ hν₁ hV₀ hw j).trans
    ((add_le_add ht (add_le_add hv hd)).trans_eq (by
      unfold correctionOneProfile differentiatedProfile; ring))

/-- The second error coefficient consumes one joint derivative of each
of its differentiated inputs (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_correctionTwo_profile
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω)
    (hV₀ : ContDiffOn ℝ ∞ V₀ Ω) (hV₁ : ContDiffOn ℝ ∞ V₁ Ω)
    {w : Euclidean n × Z} (hw : w ∈ Ω) {L : ℝ} (hL : 1 ≤ L) {b : ℕ}
    {C A₁ B₀ B₁ : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    (hpξ : ∀ j, ‖iteratedFDeriv ℝ j ξ w‖ ≤ C j * L ^ (j - b))
    (hpν₁ : ∀ j, ‖iteratedFDeriv ℝ j ν₁ w‖ ≤ A₁ j * L ^ (j - (b + 1)))
    (hpV₀ : ∀ j, ‖iteratedFDeriv ℝ j V₀ w‖ ≤ B₀ j * L ^ (j - (b + 1)))
    (hpV₁ : ∀ j, ‖iteratedFDeriv ℝ j V₁ w‖ ≤ B₁ j * L ^ (j - b)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ ≤
      correctionTwoProfile n N C A₁ B₀ B₁ j * L ^ (j - b) := by
  have ht := jet_bilinear_le (normalTensor n N) hΩ hξ hV₁ hw hL hC hB₁ hpξ hpV₁ j
  have hd := mul_le_mul_of_nonneg_left (hpν₁ (j + 1)) (norm_nonneg (differentialMatrix n N))
  have hv := mul_le_mul_of_nonneg_left (hpV₀ (j + 1)) (norm_nonneg (differentialMatrix n N))
  rw [show j + 1 - (b + 1) = j - b by omega] at hd hv
  exact (jet_correctionTwo_le hΩ hξ hν₁ hV₀ hV₁ hw j).trans
    ((add_le_add (add_le_add ht hd) hv).trans_eq (by
      unfold correctionTwoProfile differentiatedProfile; ring))

/-- The full error retains baseline `rpar`, derived from the actual input
baselines, with constants depending only on the five fixed profiles. The
first error coefficient in fact has the stronger baseline `rpar+1`
(`app:ch_waves:thm:wkb`). -/
theorem jet_error_profile
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hV₁ : ContDiffOn ℝ ∞ V₁ Ω) {w : Euclidean n × Z} (hw : w ∈ Ω)
    {τ L : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L) {rpar : ℕ}
    {C A₀ A₁ B₀ B₁ : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    (hpξ : ∀ j, ‖iteratedFDeriv ℝ j ξ w‖ ≤ C j * L ^ (j - (rpar + 3)))
    (hpν₀ : ∀ j, ‖iteratedFDeriv ℝ j ν₀ w‖ ≤ A₀ j * L ^ (j - (rpar + 2)))
    (hpν₁ : ∀ j, ‖iteratedFDeriv ℝ j ν₁ w‖ ≤ A₁ j * L ^ (j - (rpar + 1)))
    (hpV₀ : ∀ j, ‖iteratedFDeriv ℝ j V₀ w‖ ≤ B₀ j * L ^ (j - (rpar + 2)))
    (hpV₁ : ∀ j, ‖iteratedFDeriv ℝ j V₁ w‖ ≤ B₁ j * L ^ (j - (rpar + 1))) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (derivativeError τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
      τ * errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) := by
  have h1 := jet_correctionOne_profile hΩ hξ hν₀ hν₁ hV₀ hw hL hC hA₁ hB₀
    (jet_lower_baseline hL hC (by omega : rpar + 1 ≤ rpar + 3) hpξ)
    hpν₀ hpν₁ (jet_lower_baseline hL hB₀ (Nat.le_succ _) hpV₀)
  have h1' := jet_lower_baseline hL
    (fun j ↦ (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).2.1)
    (Nat.le_succ rpar) h1 j
  have h2 := jet_correctionTwo_profile hΩ hξ hν₁ hV₀ hV₁ hw hL hC hB₁
    (jet_lower_baseline hL hC (by omega : rpar ≤ rpar + 3) hpξ)
    hpν₁ (jet_lower_baseline hL hB₀ (Nat.le_succ _) hpV₀)
    (jet_lower_baseline hL hB₁ (Nat.le_succ _) hpV₁) j
  have h3 := mul_le_mul_of_nonneg_left (hpV₁ (j + 1)) (norm_nonneg (differentialMatrix n N))
  rw [show j + 1 - (rpar + 1) = j - rpar by omega] at h3
  have hτ2 : τ^2 ≤ τ := by nlinarith
  have hτ3 : τ^3 ≤ τ := by nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτ2)]
  calc
    _ ≤ τ * ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ +
        τ^2 * ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ +
        τ^3 * (‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) V₁ w‖) :=
      jet_derivativeError_le hΩ hξ hν₀ hν₁ hV₀ hV₁ hw hτ j
    _ ≤ τ * ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ +
        τ * ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ +
        τ * (‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) V₁ w‖) := by gcongr
    _ ≤ τ * (correctionOneProfile n N C A₀ A₁ B₀ j * L ^ (j - rpar)) +
        τ * (correctionTwoProfile n N C A₁ B₀ B₁ j * L ^ (j - rpar)) +
        τ * (‖differentialMatrix n N‖ * (B₁ (j+1) * L ^ (j - rpar))) := by gcongr
    _ = _ := by unfold errorProfile differentiatedProfile; ring

/-- The complete derivative has baseline `rpar`; its order-zero term is the
literal leading tensor. No desired derivative grade is an input
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_derivative_profile
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hV₁ : ContDiffOn ℝ ∞ V₁ Ω) {w : Euclidean n × Z} (hw : w ∈ Ω)
    {τ L : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L) {rpar : ℕ}
    {C A₀ A₁ B₀ B₁ : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    (hpξ : ∀ j, ‖iteratedFDeriv ℝ j ξ w‖ ≤ C j * L ^ (j - (rpar + 3)))
    (hpν₀ : ∀ j, ‖iteratedFDeriv ℝ j ν₀ w‖ ≤ A₀ j * L ^ (j - (rpar + 2)))
    (hpν₁ : ∀ j, ‖iteratedFDeriv ℝ j ν₁ w‖ ≤ A₁ j * L ^ (j - (rpar + 1)))
    (hpV₀ : ∀ j, ‖iteratedFDeriv ℝ j V₀ w‖ ≤ B₀ j * L ^ (j - (rpar + 2)))
    (hpV₁ : ∀ j, ‖iteratedFDeriv ℝ j V₁ w‖ ≤ B₁ j * L ^ (j - (rpar + 1))) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
      derivativeProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) := by
  have h1 := contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀
  have h2 := contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁
  have h3 := contDiffOn_physicalJacobian hΩ hV₁
  have he : ContDiffOn ℝ ∞ (derivativeError τ ξ ν₀ ν₁ V₀ V₁) Ω :=
    ((h1.const_smul _).add (h2.const_smul _)).add (h3.const_smul _)
  have ht := (contDiffOn_normalTensor hξ hν₀).contDiffAt (hΩ.mem_nhds hw)
  have hh := jet_add_le ht.neg (he.contDiffAt (hΩ.mem_nhds hw)) j
  have hn : ‖iteratedFDeriv ℝ j (fun y ↦ -(normalTensor n N (ξ y) (ν₀ y))) w‖ =
      ‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (ν₀ y)) w‖ := by
    change ‖iteratedFDeriv ℝ j (-(fun y ↦ normalTensor n N (ξ y) (ν₀ y))) w‖ = _
    rw [iteratedFDeriv_neg_apply, norm_neg]
  rw [hn] at hh
  have hlead := jet_bilinear_le (normalTensor n N) hΩ hξ hν₀ hw hL hC hA₀
    (jet_lower_baseline hL hC (by omega : rpar ≤ rpar + 3) hpξ)
    (jet_lower_baseline hL hA₀ (by omega : rpar ≤ rpar + 2) hpν₀) j
  have herr := jet_error_profile hΩ hξ hν₀ hν₁ hV₀ hV₁ hw hτ hτ1 hL
    hC hA₀ hA₁ hB₀ hB₁ hpξ hpν₀ hpν₁ hpV₀ hpV₁ j
  have hE := (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).2.2.2.1
  have hsmall : τ * errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) ≤
      errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) := by
    calc
      _ = τ * (errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar)) := by ring
      _ ≤ 1 * (errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar)) :=
        mul_le_mul_of_nonneg_right hτ1
          (mul_nonneg hE (pow_nonneg (le_trans zero_le_one hL) _))
      _ = _ := one_mul _
  exact hh.trans ((add_le_add hlead (herr.trans hsmall)).trans_eq (by
    unfold derivativeProfile; ring))

/-- Explicit quantifier order for the polynomial deduction: the constants
are chosen from dimensions, orders and the five fixed profiles BEFORE `τ`,
`L`, the domain or any varying coefficient field. The literal-family
identities and `full_amplitude_joint_bounds` specialize this implication
(`app:ch_waves:thm:wkb`). -/
theorem exists_polynomial_joint_constants (n N rpar : ℕ)
    (C A₀ A₁ B₀ B₁ : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) :
    ∃ D A R : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧ (∀ j, 0 ≤ A j) ∧ (∀ j, 0 ≤ R j) ∧
      ∀ (τ L : ℝ), 0 < τ → τ ≤ 1 → 1 ≤ L →
      ∀ (Ω : Set (Euclidean n × Z)), IsOpen Ω →
      ∀ (ξ : Euclidean n × Z → Euclidean n)
        (ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)),
      ContDiffOn ℝ ∞ ξ Ω → ContDiffOn ℝ ∞ ν₀ Ω → ContDiffOn ℝ ∞ ν₁ Ω →
      ContDiffOn ℝ ∞ V₀ Ω → ContDiffOn ℝ ∞ V₁ Ω →
      ∀ w ∈ Ω,
      (∀ j, ‖iteratedFDeriv ℝ j ξ w‖ ≤ C j * L ^ (j - (rpar + 3))) →
      (∀ j, ‖iteratedFDeriv ℝ j ν₀ w‖ ≤ A₀ j * L ^ (j - (rpar + 2))) →
      (∀ j, ‖iteratedFDeriv ℝ j ν₁ w‖ ≤ A₁ j * L ^ (j - (rpar + 1))) →
      (∀ j, ‖iteratedFDeriv ℝ j V₀ w‖ ≤ B₀ j * L ^ (j - (rpar + 2))) →
      (∀ j, ‖iteratedFDeriv ℝ j V₁ w‖ ≤ B₁ j * L ^ (j - (rpar + 1))) →
      ∀ j,
      ‖iteratedFDeriv ℝ j (WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁) w‖ ≤
          τ * D j * L ^ (j - (rpar + 1)) ∧
        ‖iteratedFDeriv ℝ j (derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
          A j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j (derivativeError τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
          τ * R j * L ^ (j - rpar) := by
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁
  refine ⟨displacementProfile A₀ A₁ B₀ B₁, derivativeProfile n N C A₀ A₁ B₀ B₁,
    errorProfile n N C A₀ A₁ B₀ B₁, (fun j ↦ (hc j).1),
    (fun j ↦ (hc j).2.2.2.2), (fun j ↦ (hc j).2.2.2.1), ?_⟩
  intro τ L hτ hτ1 hL Ω hΩ ξ ν₀ ν₁ V₀ V₁ hξ hν₀ hν₁ hV₀ hV₁ w hw
    hpξ hpν₀ hpν₁ hpV₀ hpV₁ j
  exact ⟨jet_displacement_profile
      (hν₀.contDiffAt (hΩ.mem_nhds hw)) (hν₁.contDiffAt (hΩ.mem_nhds hw))
      (hV₀.contDiffAt (hΩ.mem_nhds hw)) (hV₁.contDiffAt (hΩ.mem_nhds hw))
      hτ.le hτ1 hL hA₀ hB₀ hpν₀ hpν₁ hpV₀ hpV₁ j,
    jet_derivative_profile hΩ hξ hν₀ hν₁ hV₀ hV₁ hw hτ.le hτ1 hL hC hA₀ hA₁ hB₀ hB₁
      hpξ hpν₀ hpν₁ hpV₀ hpV₁ j,
    jet_error_profile hΩ hξ hν₀ hν₁ hV₀ hV₁ hw hτ.le hτ1 hL hC hA₀ hA₁ hB₀ hB₁
      hpξ hpν₀ hpν₁ hpV₀ hpV₁ j⟩

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
