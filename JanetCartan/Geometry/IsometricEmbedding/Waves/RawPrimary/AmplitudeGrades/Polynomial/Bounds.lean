module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Formulas

/-!
# Quantitative joint bounds for the exact WKB polynomial

The inputs are jets of the phase covector and the four geometric coefficients,
not estimates of the output amplitudes. All constants below are explicit
functions of those fixed profiles and the dimensions. The leading coefficient
producer is `Correction.ActualFamily`; the complex correction coefficient
producer is the separate ambient reconstruction deduction. Their actual
instantiation belongs to the parent construction.

Sources: `app:ch_waves:eq:exact-W-amplitude`,
`app:ch_waves:eq:WKB-amplitude-difference`, `app:ch_waves:thm:wkb`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Joint smoothness of the exact displacement polynomial
(`app:ch_waves:eq:exact-W-amplitude`). -/
theorem contDiffAt_reconstructionAmplitude {ν₀ ν₁ V₀ V₁ : X → E} {x : X}
    (hν₀ : ContDiffAt ℝ ∞ ν₀ x) (hν₁ : ContDiffAt ℝ ∞ ν₁ x)
    (hV₀ : ContDiffAt ℝ ∞ V₀ x) (hV₁ : ContDiffAt ℝ ∞ V₁ x) (lam : ℝ) :
    ContDiffAt ℝ ∞ (WKB.reconstructionAmplitude lam ν₀ ν₁ V₀ V₁) x :=
  ((hν₀.const_smul _).add ((hV₀.add (hν₁.const_smul _)).const_smul _)).add
    (hV₁.const_smul _)

/-- Every joint derivative of the exact displacement polynomial retains
all three small powers (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem jet_reconstructionAmplitude_le {ν₀ ν₁ V₀ V₁ : X → E} {x : X}
    (hν₀ : ContDiffAt ℝ ∞ ν₀ x) (hν₁ : ContDiffAt ℝ ∞ ν₁ x)
    (hV₀ : ContDiffAt ℝ ∞ V₀ x) (hV₁ : ContDiffAt ℝ ∞ V₁ x)
    {τ : ℝ} (hτ : 0 ≤ τ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁) x‖ ≤
      τ * ‖iteratedFDeriv ℝ j ν₀ x‖ +
        τ^2 * (‖iteratedFDeriv ℝ j V₀ x‖ + ‖iteratedFDeriv ℝ j ν₁ x‖) +
        τ^3 * ‖iteratedFDeriv ℝ j V₁ x‖ := by
  have h0 : ContDiffAt ℝ j ((Complex.I * (τ : ℂ)) • ν₀) x :=
    (hν₀.const_smul _).of_le (by simp)
  have hi : ContDiffAt ℝ j (Complex.I • ν₁) x :=
    (hν₁.const_smul _).of_le (by simp)
  have hs : ContDiffAt ℝ j (V₀ + Complex.I • ν₁) x := (hV₀.of_le (by simp)).add hi
  have h2 : ContDiffAt ℝ j ((τ : ℂ)^2 • (V₀ + Complex.I • ν₁)) x :=
    (((hV₀.of_le (by simp)).add hi).const_smul _)
  have h3 : ContDiffAt ℝ j ((τ : ℂ)^3 • V₁) x :=
    (hV₁.const_smul _).of_le (by simp)
  unfold WKB.reconstructionAmplitude
  simp only [Complex.ofReal_inv, inv_inv]
  change ‖iteratedFDeriv ℝ j
    (((Complex.I * (τ : ℂ)) • ν₀ + (τ : ℂ)^2 • (V₀ + Complex.I • ν₁)) +
      (τ : ℂ)^3 • V₁) x‖ ≤ _
  have h02 : ContDiffAt ℝ j
      ((Complex.I * (τ : ℂ)) • ν₀ + (τ : ℂ)^2 • (V₀ + Complex.I • ν₁)) x := h0.add h2
  rw [iteratedFDeriv_add_apply h02 h3,
    iteratedFDeriv_add_apply h0 h2,
    iteratedFDeriv_const_smul_apply (hν₀.of_le (by simp)),
    iteratedFDeriv_const_smul_apply hs,
    iteratedFDeriv_const_smul_apply (hV₁.of_le (by simp)),
    iteratedFDeriv_add_apply (hV₀.of_le (by simp)) hi,
    iteratedFDeriv_const_smul_apply (hν₁.of_le (by simp))]
  calc
    _ ≤ ‖(Complex.I * (τ : ℂ)) • iteratedFDeriv ℝ j ν₀ x‖ +
        ‖(τ : ℂ)^2 • (iteratedFDeriv ℝ j V₀ x + Complex.I • iteratedFDeriv ℝ j ν₁ x)‖ +
        ‖(τ : ℂ)^3 • iteratedFDeriv ℝ j V₁ x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_smul, norm_mul, norm_pow, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Complex.norm_I, one_mul])

/-- Fixed displacement profile, independent of frequency, scale, and the
varying fields (`app:ch_waves:eq:exact-W-amplitude`). -/
def displacementProfile (A₀ A₁ B₀ B₁ : ℕ → ℝ) (j : ℕ) : ℝ :=
  A₀ j + (B₀ j + A₁ j) + B₁ j

/-- The strongest common displacement baseline supplied by leading
baseline `b+1` and correction baseline `b` is `b`. In particular it is
`rpar+1` for the actual producers (`app:ch_waves:thm:wkb`). -/
theorem jet_displacement_profile {ν₀ ν₁ V₀ V₁ : X → E} {x : X}
    (hν₀ : ContDiffAt ℝ ∞ ν₀ x) (hν₁ : ContDiffAt ℝ ∞ ν₁ x)
    (hV₀ : ContDiffAt ℝ ∞ V₀ x) (hV₁ : ContDiffAt ℝ ∞ V₁ x)
    {τ L : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L) {b : ℕ}
    {A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hA₀ : ∀ j, 0 ≤ A₀ j) (hB₀ : ∀ j, 0 ≤ B₀ j)
    (hpν₀ : ∀ j, ‖iteratedFDeriv ℝ j ν₀ x‖ ≤ A₀ j * L ^ (j - (b + 1)))
    (hpν₁ : ∀ j, ‖iteratedFDeriv ℝ j ν₁ x‖ ≤ A₁ j * L ^ (j - b))
    (hpV₀ : ∀ j, ‖iteratedFDeriv ℝ j V₀ x‖ ≤ B₀ j * L ^ (j - (b + 1)))
    (hpV₁ : ∀ j, ‖iteratedFDeriv ℝ j V₁ x‖ ≤ B₁ j * L ^ (j - b)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁) x‖ ≤
      τ * displacementProfile A₀ A₁ B₀ B₁ j * L ^ (j - b) := by
  have hτ2 : τ^2 ≤ τ := by nlinarith
  have hτ3 : τ^3 ≤ τ := by nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτ2)]
  have h0 := jet_lower_baseline hL hA₀ (Nat.le_succ b) hpν₀ j
  have hv := jet_lower_baseline hL hB₀ (Nat.le_succ b) hpV₀ j
  calc
    _ ≤ τ * ‖iteratedFDeriv ℝ j ν₀ x‖ +
        τ^2 * (‖iteratedFDeriv ℝ j V₀ x‖ + ‖iteratedFDeriv ℝ j ν₁ x‖) +
        τ^3 * ‖iteratedFDeriv ℝ j V₁ x‖ :=
      jet_reconstructionAmplitude_le hν₀ hν₁ hV₀ hV₁ hτ j
    _ ≤ τ * ‖iteratedFDeriv ℝ j ν₀ x‖ +
        τ * (‖iteratedFDeriv ℝ j V₀ x‖ + ‖iteratedFDeriv ℝ j ν₁ x‖) +
        τ * ‖iteratedFDeriv ℝ j V₁ x‖ := by gcongr
    _ ≤ τ * (A₀ j * L ^ (j - b)) +
        τ * (B₀ j * L ^ (j - b) + A₁ j * L ^ (j - b)) +
        τ * (B₁ j * L ^ (j - b)) := by gcongr; exact hpν₁ j; exact hpV₁ j
    _ = _ := by unfold displacementProfile; ring

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Smoothness of a literal normal tensor with its Frobenius norm
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_normalTensor {Ω : Set X} {ξ : X → Euclidean n}
    {ν : X → EuclideanSpace ℂ (Fin N)} (hξ : ContDiffOn ℝ ∞ ξ Ω)
    (hν : ContDiffOn ℝ ∞ ν Ω) :
    ContDiffOn ℝ ∞ (fun w ↦ normalTensor n N (ξ w) (ν w)) Ω :=
  ((normalTensor n N).contDiff.comp_contDiffOn hξ).clm_apply hν

/-- Smoothness of the first exact correction coefficient
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_correctionOne {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω) :
    ContDiffOn ℝ ∞ (correctionOne ξ ν₀ ν₁ V₀) Ω :=
  (contDiffOn_normalTensor hξ hν₁).neg.add
    (((contDiffOn_normalTensor hξ hV₀).add
      (contDiffOn_physicalJacobian hΩ hν₀)).const_smul Complex.I)

/-- Smoothness of the second exact correction coefficient
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_correctionTwo {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω)
    (hV₀ : ContDiffOn ℝ ∞ V₀ Ω) (hV₁ : ContDiffOn ℝ ∞ V₁ Ω) :
    ContDiffOn ℝ ∞ (correctionTwo ξ ν₁ V₀ V₁) Ω :=
  (((contDiffOn_normalTensor hξ hV₁).add
    (contDiffOn_physicalJacobian hΩ hν₁)).const_smul Complex.I).add
      (contDiffOn_physicalJacobian hΩ hV₀)

/-- Every joint derivative of the first coefficient is bounded by the
literal tensor and differentiated leading normal
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_correctionOne_le {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    {w : Euclidean n × Z} (hw : w ∈ Ω) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ ≤
      ‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (ν₁ y)) w‖ +
        (‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (V₀ y)) w‖ +
          ‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) ν₀ w‖) := by
  have ht := (contDiffOn_normalTensor hξ hν₁).contDiffAt (hΩ.mem_nhds hw)
  have hv := (contDiffOn_normalTensor hξ hV₀).contDiffAt (hΩ.mem_nhds hw)
  have hd := (contDiffOn_physicalJacobian hΩ hν₀).contDiffAt (hΩ.mem_nhds hw)
  have hh := jet_add_le
    (f := fun y ↦ -(normalTensor n N (ξ y) (ν₁ y)))
    (g := fun y ↦ Complex.I • (normalTensor n N (ξ y) (V₀ y) + physicalJacobian ν₀ y))
    ht.neg ((hv.add hd).const_smul Complex.I) j
  change ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ ≤ _ at hh
  rw [jet_const_smul (hv.add hd) Complex.I j, Complex.norm_I, one_mul] at hh
  have hn : ‖iteratedFDeriv ℝ j (fun y ↦ -(normalTensor n N (ξ y) (ν₁ y))) w‖ =
      ‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (ν₁ y)) w‖ := by
    change ‖iteratedFDeriv ℝ j (-(fun y ↦ normalTensor n N (ξ y) (ν₁ y))) w‖ = _
    rw [iteratedFDeriv_neg_apply, norm_neg]
  rw [hn] at hh
  exact hh.trans (add_le_add le_rfl ((jet_add_le hv hd j).trans
    (add_le_add le_rfl (jet_physicalJacobian_le (hν₀.contDiffAt (hΩ.mem_nhds hw)) j))))

/-- All joint derivatives of the second coefficient retain both first
coefficient derivatives (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_correctionTwo_le {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω)
    (hV₀ : ContDiffOn ℝ ∞ V₀ Ω) (hV₁ : ContDiffOn ℝ ∞ V₁ Ω)
    {w : Euclidean n × Z} (hw : w ∈ Ω) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ ≤
      (‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (V₁ y)) w‖ +
        ‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) ν₁ w‖) +
        ‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) V₀ w‖ := by
  have ht := (contDiffOn_normalTensor hξ hV₁).contDiffAt (hΩ.mem_nhds hw)
  have hd := (contDiffOn_physicalJacobian hΩ hν₁).contDiffAt (hΩ.mem_nhds hw)
  have hv := (contDiffOn_physicalJacobian hΩ hV₀).contDiffAt (hΩ.mem_nhds hw)
  have hh := jet_add_le
    (f := fun y ↦ Complex.I • (normalTensor n N (ξ y) (V₁ y) + physicalJacobian ν₁ y))
    (g := physicalJacobian V₀) ((ht.add hd).const_smul Complex.I) hv j
  rw [jet_const_smul (ht.add hd) Complex.I j, Complex.norm_I, one_mul] at hh
  exact hh.trans (add_le_add ((jet_add_le ht hd j).trans
    (add_le_add le_rfl (jet_physicalJacobian_le (hν₁.contDiffAt (hΩ.mem_nhds hw)) j)))
      (jet_physicalJacobian_le (hV₀.contDiffAt (hΩ.mem_nhds hw)) j))

/-- Every joint derivative of the error retains `τ`, `τ²`, and `τ³`
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_derivativeError_le {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {ξ : Euclidean n × Z → Euclidean n}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    (hξ : ContDiffOn ℝ ∞ ξ Ω) (hν₀ : ContDiffOn ℝ ∞ ν₀ Ω)
    (hν₁ : ContDiffOn ℝ ∞ ν₁ Ω) (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hV₁ : ContDiffOn ℝ ∞ V₁ Ω) {w : Euclidean n × Z} (hw : w ∈ Ω)
    {τ : ℝ} (hτ : 0 ≤ τ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (derivativeError τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
      τ * ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ +
        τ^2 * ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ +
        τ^3 * (‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) V₁ w‖) := by
  have h1 := (contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀).contDiffAt (hΩ.mem_nhds hw)
  have h2 := (contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁).contDiffAt (hΩ.mem_nhds hw)
  have h3 := (contDiffOn_physicalJacobian hΩ hV₁).contDiffAt (hΩ.mem_nhds hw)
  have hh := (jet_add_le
    (f := fun y ↦ (τ : ℂ) • correctionOne ξ ν₀ ν₁ V₀ y +
      (τ : ℂ)^2 • correctionTwo ξ ν₁ V₀ V₁ y)
    (g := fun y ↦ (τ : ℂ)^3 • physicalJacobian V₁ y)
    ((h1.const_smul (τ : ℂ)).add (h2.const_smul ((τ : ℂ)^2)))
    (h3.const_smul ((τ : ℂ)^3)) j).trans
      (add_le_add (jet_add_le
        (f := fun y ↦ (τ : ℂ) • correctionOne ξ ν₀ ν₁ V₀ y)
        (g := fun y ↦ (τ : ℂ)^2 • correctionTwo ξ ν₁ V₀ V₁ y)
        (h1.const_smul (τ : ℂ)) (h2.const_smul ((τ : ℂ)^2)) j) le_rfl)
  simp only [jet_const_smul h1 (τ : ℂ) j, jet_const_smul h2 ((τ : ℂ)^2) j,
    jet_const_smul h3 ((τ : ℂ)^3) j,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (jet_physicalJacobian_le (hV₁.contDiffAt (hΩ.mem_nhds hw)) j) (pow_nonneg hτ 3)))

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
