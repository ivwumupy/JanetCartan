module
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Derivative bounds for the actual nonstationary coefficients

For `app:ch_osc:prop:osc-source-shell`, normalize the full phase covector by
`R = ρ + ‖ξ‖`. Its reciprocal coefficient map is smooth on a fixed compact
annulus. The constants below are finite sums of suprema of its derivatives;
they depend only on that annulus, the coordinate vectors, and the requested
order. The phase's higher derivative constants enter through a separate finite
majorant. In particular, no coefficient estimate is an assumption of the final
integration-by-parts theorem.
-/

open scoped ContDiff
open Set
@[expose] public noncomputable section
namespace JanetCartan.Localization
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
/-- `app:ch_osc:prop:osc-source-shell`: Sum of squared coordinate components of a covector. -/
def covectorSquare (e : ι → E) (v : E →L[ℝ] ℝ) : ℝ := ∑ i, (v (e i)) ^ 2
/-- `app:ch_osc:prop:osc-source-shell`: The reciprocal coefficient map on covectors, before composition with the phase derivative. -/
def reciprocalCoefficient (e : ι → E) (i : ι) (v : E →L[ℝ] ℝ) : ℂ :=
  (v (e i) : ℂ) / (Complex.I * (covectorSquare e v : ℂ))
/-- `app:ch_osc:prop:osc-source-shell`: The squared coordinate length is continuous. -/
theorem continuous_covectorSquare (e : ι → E) : Continuous (covectorSquare e) := by
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.apply ℝ ℝ (e i)).continuous.pow 2
/-- `app:ch_osc:prop:osc-source-shell`: The reciprocal map is smooth wherever its denominator is nonzero. -/
theorem contDiffOn_reciprocalCoefficient (e : ι → E) (i : ι) :
    ContDiffOn ℝ ∞ (reciprocalCoefficient e i) {v | covectorSquare e v ≠ 0} := by
  have hs : ContDiff ℝ ∞ (covectorSquare e) := by
    apply ContDiff.sum
    intro j _
    exact (ContinuousLinearMap.apply ℝ ℝ (e j)).contDiff.pow 2
  have hn : ContDiff ℝ ∞ (fun v : E →L[ℝ] ℝ ↦ (v (e i) : ℂ)) := Complex.ofRealCLM.contDiff.comp
    (ContinuousLinearMap.apply ℝ ℝ (e i)).contDiff
  change ContDiffOn ℝ ∞ (fun v ↦ (v (e i) : ℂ) / (Complex.I * (covectorSquare e v : ℂ))) _
  simp only [div_eq_mul_inv]
  apply hn.contDiffOn.mul
    ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp hs).contDiffOn).inv _)
  intro v hv
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv)
variable [FiniteDimensional ℝ E]
/-- `app:ch_osc:prop:osc-source-shell`: A fixed compact set of normalized phase covectors; `δ` bounds the squared coordinate length below. -/
def covectorAnnulus (e : ι → E) (δ G : ℝ) : Set (E →L[ℝ] ℝ) :=
  {v | ‖v‖ ≤ G ∧ δ ≤ covectorSquare e v}
/-- `app:ch_osc:prop:osc-source-shell`: The normalized covector region is compact in finite dimension. -/
theorem isCompact_covectorAnnulus (e : ι → E) (δ G : ℝ) :
    IsCompact (covectorAnnulus e δ G) := by
  apply (isCompact_closedBall (0 : E →L[ℝ] ℝ) G).of_isClosed_subset
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_covectorSquare e))
  · intro v hv
    simpa using hv.1
omit [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Every derivative norm of the reciprocal map is continuous on the fixed annulus. -/
theorem continuousOn_reciprocalCoefficient_derivative (e : ι → E) {δ G : ℝ}
    (hδ : 0 < δ) (i : ι) (r : ℕ) :
    ContinuousOn (fun v ↦ ‖iteratedFDeriv ℝ r (reciprocalCoefficient e i) v‖)
      (covectorAnnulus e δ G) := by
  intro v hv
  have hne : covectorSquare e v ≠ 0 := ne_of_gt (hδ.trans_le hv.2)
  exact (((contDiffOn_reciprocalCoefficient e i).contDiffAt
    ((isOpen_ne.preimage (continuous_covectorSquare e)).mem_nhds hne)).continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt

/-- `app:ch_osc:prop:osc-source-shell`: An explicit constant for all reciprocal-map derivatives through order `r`, uniform in the coordinate index. The suprema are finite when `δ > 0`. -/
def reciprocalDerivativeBound (e : ι → E) (δ G : ℝ) (r : ℕ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.range (r + 1), max 0
    (sSup ((fun v ↦ ‖iteratedFDeriv ℝ j (reciprocalCoefficient e i) v‖) ''
      covectorAnnulus e δ G))
omit [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The reciprocal derivative constant is nonnegative. -/
theorem reciprocalDerivativeBound_nonneg (e : ι → E) (δ G : ℝ) (r : ℕ) :
    0 ≤ reciprocalDerivativeBound e δ G r := by
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
/-- `app:ch_osc:prop:osc-source-shell`: Compactness bounds every reciprocal-map derivative by the specified constant. -/
theorem norm_iteratedFDeriv_reciprocalCoefficient_le (e : ι → E) {δ G : ℝ}
    (hδ : 0 < δ) (i : ι) {j r : ℕ} (hj : j ≤ r) {v : E →L[ℝ] ℝ}
    (hv : v ∈ covectorAnnulus e δ G) :
    ‖iteratedFDeriv ℝ j (reciprocalCoefficient e i) v‖ ≤ reciprocalDerivativeBound e δ G r := by
  apply le_trans ((le_csSup ((isCompact_covectorAnnulus e δ G).bddAbove_image
    (continuousOn_reciprocalCoefficient_derivative e hδ i j)) (mem_image_of_mem _ hv)).trans
      (le_max_right 0 _))
  apply le_trans (Finset.single_le_sum (f := fun k ↦ max 0
    (sSup ((fun v ↦ ‖iteratedFDeriv ℝ k (reciprocalCoefficient e i) v‖) ''
      covectorAnnulus e δ G))) (fun _ _ ↦ le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  unfold reciprocalDerivativeBound
  apply Finset.single_le_sum (f := fun k ↦ ∑ j ∈ Finset.range (r + 1), max 0
    (sSup ((fun v ↦ ‖iteratedFDeriv ℝ j (reciprocalCoefficient e k) v‖) '' covectorAnnulus e δ G)))
    (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
    (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The squared coordinate length has degree two under real scaling. -/
theorem covectorSquare_smul (e : ι → E) (t : ℝ) (v : E →L[ℝ] ℝ) :
    covectorSquare e (t • v) = t ^ 2 * covectorSquare e v := by
  simp only [covectorSquare, smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum]

omit [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The actual reciprocal coefficient has degree minus one under positive frequency normalization. -/
theorem reciprocalCoefficient_rescale (e : ι → E) (i : ι) {R : ℝ} (hR : R ≠ 0)
    (v : E →L[ℝ] ℝ) :
    reciprocalCoefficient e i v = R⁻¹ • reciprocalCoefficient e i (R⁻¹ • v) := by
  by_cases hv : covectorSquare e v = 0
  · simp [reciprocalCoefficient, covectorSquare_smul, hv]
  · have hv' : (covectorSquare e v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
    have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
    simp only [reciprocalCoefficient, covectorSquare_smul, smul_apply,
      smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.real_smul]
    field_simp

/-- `app:ch_osc:prop:osc-source-shell`: The composition estimate on an open phase domain, retaining the factorial and reciprocal-map constants. -/
theorem norm_iteratedFDeriv_reciprocalCoefficient_comp_le {U : Set E} (hU : IsOpen U)
    (e : ι → E) (f : E → (E →L[ℝ] ℝ)) (hf : ContDiffOn ℝ ∞ f U)
    {δ G D : ℝ} (hδ : 0 < δ) (hmap : MapsTo f U (covectorAnnulus e δ G))
    {x : E} (hx : x ∈ U) (i : ι) (r : ℕ)
    (hd : ∀ j, 1 ≤ j → j ≤ r → ‖iteratedFDeriv ℝ j f x‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ r (reciprocalCoefficient e i ∘ f) x‖ ≤
      r.factorial * reciprocalDerivativeBound e δ G r * D ^ r := by
  have hopen : IsOpen {v : E →L[ℝ] ℝ | covectorSquare e v ≠ 0} :=
    isOpen_ne.preimage (continuous_covectorSquare e)
  have hmaps : MapsTo f U {v | covectorSquare e v ≠ 0} :=
    fun y hy ↦ ne_of_gt (hδ.trans_le (hmap hy).2)
  have h := norm_iteratedFDerivWithin_comp_le (contDiffOn_reciprocalCoefficient e i)
    hf (by simp : (r : ℕ∞ω) ≤ ∞) hopen.uniqueDiffOn hU.uniqueDiffOn hmaps hx
    (C := reciprocalDerivativeBound e δ G r) (D := D)
    (fun j hj ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hopen (hmaps hx)]
      exact norm_iteratedFDeriv_reciprocalCoefficient_le e hδ i hj (hmap hx))
    (fun j hj hjr ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hU hx]
      exact hd j hj hjr)
  rwa [iteratedFDerivWithin_of_isOpen _ hU hx] at h

/-- `app:ch_osc:prop:osc-source-shell`: Reciprocal differentiation gives the exact `Lʳ / R` scale from the full phase bounds. -/
theorem norm_iteratedFDeriv_phaseCoefficient_le {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    {δ G D L R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hgap : ∀ y ∈ U, δ * R ^ 2 ≤ phaseGradientSquare e ψ y)
    (hupper : ∀ y ∈ U, ‖fderiv ℝ ψ y‖ ≤ G * R)
    {x : E} (hx : x ∈ U) (i : ι) (r : ℕ)
    (hd : ∀ j, 1 ≤ j → j ≤ r →
      ‖iteratedFDeriv ℝ (j + 1) ψ x‖ ≤ R * D ^ j * L ^ j) :
    ‖iteratedFDeriv ℝ r (phaseCoefficient e ψ i) x‖ ≤
      (r.factorial * reciprocalDerivativeBound e δ G r * D ^ r) * L ^ r / R := by
  let f : E → (E →L[ℝ] ℝ) := R⁻¹ • fderiv ℝ ψ
  have hf : ContDiffOn ℝ ∞ f U := (hψ.fderiv_of_isOpen hU (m := ∞) (by simp)).const_smul (R⁻¹)
  have hm : MapsTo f U (covectorAnnulus e δ G) := by
    intro y hy
    constructor
    · change ‖R⁻¹ • fderiv ℝ ψ y‖ ≤ G
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      exact (mul_le_mul_of_nonneg_left (hupper y hy) (inv_nonneg.mpr hR.le)).trans_eq
        (by field_simp)
    · change δ ≤ covectorSquare e (R⁻¹ • fderiv ℝ ψ y)
      rw [covectorSquare_smul]
      change δ ≤ R⁻¹ ^ 2 * phaseGradientSquare e ψ y
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (sq_pos_of_pos hR)]
      exact hgap y hy
  have hdf : ∀ j, 1 ≤ j → j ≤ r → ‖iteratedFDeriv ℝ j f x‖ ≤ (D * L) ^ j := by
    intro j hj hjr
    rw [iteratedFDeriv_const_smul_apply
      ((hψ.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt (hU.mem_nhds hx) |>.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), norm_iteratedFDeriv_fderiv]
    apply (mul_le_mul_of_nonneg_left (hd j hj hjr) (inv_nonneg.mpr hR.le)).trans_eq
    rw [mul_pow]
    field_simp
  have heq : phaseCoefficient e ψ i = R⁻¹ • (reciprocalCoefficient e i ∘ f) := by
    ext y
    exact reciprocalCoefficient_rescale e i hR.ne' (fderiv ℝ ψ y)
  rw [heq, iteratedFDeriv_const_smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  · apply (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_reciprocalCoefficient_comp_le hU e f hf hδ hm hx i r hdf)
      (inv_nonneg.mpr hR.le)).trans_eq
    rw [mul_pow]
    ring
  · exact (((contDiffOn_reciprocalCoefficient e i).comp hf
      (fun y hy ↦ ne_of_gt (hδ.trans_le (hm hy).2))).contDiffAt
        (hU.mem_nhds hx)).of_le (by simp)

/-- `app:ch_osc:prop:osc-source-shell`: A finite majorant of the phase derivative profile through the requested order. -/
def phaseDerivativeMajorant (P : ℕ → ℝ) (r : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (r + 1), max 0 (P j)
/-- `app:ch_osc:prop:osc-source-shell`: The majorant is at least one. -/
theorem one_le_phaseDerivativeMajorant (P : ℕ → ℝ) (r : ℕ) :
    1 ≤ phaseDerivativeMajorant P r := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
/-- `app:ch_osc:prop:osc-source-shell`: The finite majorant converts the phase derivative constants to geometric bounds. -/
theorem le_phaseDerivativeMajorant_pow (P : ℕ → ℝ) {j r : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r) :
    P j ≤ phaseDerivativeMajorant P r ^ j := by
  apply le_trans _ (le_self_pow₀ (one_le_phaseDerivativeMajorant P r) (by omega : j ≠ 0))
  apply le_trans (le_max_right 0 (P j))
  apply le_trans (Finset.single_le_sum (f := fun k ↦ max 0 (P k))
    (fun _ _ ↦ le_max_left _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjr)))
  exact le_add_of_nonneg_left (by norm_num)

/-- `app:ch_osc:prop:osc-source-shell`: The full coefficient constant at order `r`, retaining dependence on the phase profile through order `r + 1`. -/
def phaseCoefficientDerivativeBound (e : ι → E) (δ G : ℝ) (P : ℕ → ℝ) (r : ℕ) : ℝ :=
  r.factorial * reciprocalDerivativeBound e δ G r * phaseDerivativeMajorant P r ^ r
omit [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The full coefficient derivative constant is nonnegative. -/
theorem phaseCoefficientDerivativeBound_nonneg (e : ι → E) (δ G : ℝ) (P : ℕ → ℝ) (r : ℕ) :
    0 ≤ phaseCoefficientDerivativeBound e δ G P r := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (reciprocalDerivativeBound_nonneg e δ G r))
    (pow_nonneg (le_trans (by norm_num) (one_le_phaseDerivativeMajorant P r)) r)

/-- `app:ch_osc:prop:osc-source-shell`: All-order graded coefficient bounds derived from the actual phase gradient gap and higher derivative profile. -/
theorem norm_iteratedFDeriv_phaseCoefficient_le_graded {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    {δ G L R : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hR : 0 < R)
    (hgap : ∀ y ∈ U, δ * R ^ 2 ≤ phaseGradientSquare e ψ y)
    (hupper : ∀ y ∈ U, ‖fderiv ℝ ψ y‖ ≤ G * R)
    {P : ℕ → ℝ} {x : E} (hx : x ∈ U) (i : ι) (r : ℕ)
    (hd : ∀ j, 1 ≤ j → j ≤ r →
      ‖iteratedFDeriv ℝ (j + 1) ψ x‖ ≤ P j * R * L ^ j) :
    ‖iteratedFDeriv ℝ r (phaseCoefficient e ψ i) x‖ ≤
      phaseCoefficientDerivativeBound e δ G P r * L ^ r / R := by
  apply norm_iteratedFDeriv_phaseCoefficient_le hU e ψ hψ hδ hR hgap hupper hx i r
  intro j hj hjr
  apply (hd j hj hjr).trans
  rw [mul_comm (P j) R]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_phaseDerivativeMajorant_pow P hj hjr) hR.le)
    (pow_nonneg hL j)

open MeasureTheory
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
/-- `app:ch_osc:prop:osc-source-shell`: Repeated integration by parts with compact support, deriving the coefficient estimates from the phase itself. The constants retain every high derivative dependence. -/
theorem norm_oscillatory_integral_le_of_phase_derivative_bounds {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (a : E → ℂ) (q : ℕ)
    (hψ : ContDiffOn ℝ ∞ ψ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    {δ G A L R : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hR : 0 < R)
    (hgap : ∀ x ∈ U, δ * R ^ 2 ≤ phaseGradientSquare e ψ x)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ ψ x‖ ≤ G * R)
    {P C : ℕ → ℝ}
    (hp : ∀ x ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) ψ x‖ ≤ P j * R * L ^ j)
    (ha_bound : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖∫ x, phaseOscillation ψ x * a x ∂μ‖ ≤
      (transposeDerivativeConstant e (phaseCoefficientDerivativeBound e δ G P) C q 0 *
        (A * (L / R) ^ q)) * μ.real (tsupport a) := by
  apply norm_oscillatory_integral_le_of_coefficient_bounds hU e ψ a q hψ ha hs hc
    (fun x hx ↦ ne_of_gt ((mul_pos hδ (sq_pos_of_pos hR)).trans_le (hgap x hx)))
    (phaseCoefficientDerivativeBound_nonneg e δ G P) hL hR _ ha_bound
  intro x hx i r
  exact norm_iteratedFDeriv_phaseCoefficient_le_graded hU e ψ hψ hδ hL hR hgap hupper
    (hs hx) i r (fun j hj _ ↦ hp x hx j hj)
end JanetCartan.Localization
