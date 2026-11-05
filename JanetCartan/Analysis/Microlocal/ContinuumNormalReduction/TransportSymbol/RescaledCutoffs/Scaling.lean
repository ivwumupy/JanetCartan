module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.ConicJets

/-!
# Exact transport amplitude rescaling

Positive dilation changes only the scalar high coefficient. The actual conic
inverse and Jacobian scaling cancel the transverse norm, while the squared
regularization and literal spectator integral are retained. These identities
feed the global symbol assembly of `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Rescale only the primitive high coefficient in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def rescaledCoefficients (a : Coefficients n N) (t : ℝ) : Coefficients n N :=
  { a with high := fun r ↦ a.high (t * r) }

/-- Rescaling the regularized carrier gives exactly `h(t r) χ(t r/R)`.
The input density squares this whole coefficient, as required in bg-frame
Step 1. -/
theorem rescaled_regularized_high (a : Coefficients n N) (χ : ℝ → ℝ) (t R r : ℝ) :
    (rescaledCoefficients (regularizedCoefficients a χ R) t).high r =
      a.high (t * r) * χ (t * r / R) := rfl

/-- The actual density under positive input dilation equals the density with
the rescaled high coefficient; the degree-one Jacobian cancels the norm.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and bg-jacobian. -/
theorem inputDensity_rescaled (a : Coefficients n N) (J : InputVariables n → ℝ)
    {t : ℝ} (ht : 0 < t) (p : InputVariables n)
    (hJ : J (scaleInput t p) = t * J p) :
    inputDensity a J (scaleInput t p) = inputDensity (rescaledCoefficients a t) J p := by
  have hnorm : ‖t • p.2.2‖ = t * ‖p.2.2‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hw : inputWeight a J (scaleInput t p) = inputWeight (rescaledCoefficients a t) J p := by
    simp only [inputWeight, rescaledCoefficients]
    dsimp only [scaleInput] at hJ ⊢
    rw [direction_pos_smul ht, hJ, hnorm]
    by_cases hj : J p = 0
    · simp [hj]
    · field_simp
  exact congrArg (fun w ↦ w • Matrix.vecMulVec (a.reduced (p.1.1, p.2.1))
    (a.reduced (p.1.2, p.2.1))) hw

/-- The rescaled regularized density retains exactly the square of the radial
profile. This is the scalar factor in bg-frame Step 1, with no altered measure
or omitted coefficients; source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem inputDensity_rescaled_regularized
    (a : Coefficients n N) (J : InputVariables n → ℝ) (χ : ℝ → ℝ) (R : ℝ)
    {t : ℝ} (ht : 0 < t) (p : InputVariables n)
    (hJ : J (scaleInput t p) = t * J p) :
    inputDensity (rescaledCoefficients (regularizedCoefficients a χ R) t) J p =
      χ (t * ‖p.2.2‖ / R) ^ 2 • inputDensity (rescaledCoefficients a t) J p := by
  rw [← inputDensity_rescaled (regularizedCoefficients a χ R) J ht p hJ,
    inputDensity_regularized, inputDensity_rescaled a J ht p hJ]
  simp [scaleInput, norm_smul, Real.norm_eq_abs, abs_of_pos ht]

/-- Zero extension commutes with the actual conic dilation and the rescaled
high coefficient. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem extendedDensity_rescaled
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (p : Variables n × Euclidean 2) :
    extendedDensity a J u Ω (scaleFrequency t p.1, p.2) =
      extendedDensity (rescaledCoefficients a t) J u Ω p := by
  by_cases hp : p ∈ Ω
  · have he : inverseCoordinates u (scaleFrequency t p.1, p.2) =
        scaleInput t (inverseCoordinates u p) := by
      simp only [inverseCoordinates, hu p hp]
      rfl
    simp only [extendedDensity, indicator_of_mem hp, indicator_of_mem ((hΩ p).mpr hp), he]
    exact inputDensity_rescaled a J ht _ (hJ p hp)
  · simp [extendedDensity, hp, (hΩ p).not.mpr hp]

/-- Exact amplitude rescaling with the unchanged literal spectator integral.
Only actual inverse, chart and Jacobian scaling are inputs; the amplitude
identity is a conclusion. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitude_rescaled
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (p : Variables n) :
    amplitude a J u Ω K (scaleFrequency t p) =
      amplitude (rescaledCoefficients a t) J u Ω K p := by
  apply integral_congr_ae
  filter_upwards [] with v
  exact extendedDensity_rescaled a J u Ω ht hΩ hu hJ (p, v)

/-- Literal spectator integral form of the regularized rescaling identity.
The radial profile stays squared inside the same Lebesgue integral, including
zero extension off the actual chart. Source:
`app:ch_background:eq:bg-full-complex-amplitude` and bg-frame Step 1. -/
theorem amplitude_regularized_rescaled_eq_integral
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (R : ℝ) {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (p : Variables n) :
    amplitude (regularizedCoefficients a χ R) J u Ω K (scaleFrequency t p) =
      ∫ v in K, χ (t * ‖(u (p, v)).2‖ / R) ^ 2 •
        extendedDensity (rescaledCoefficients a t) J u Ω (p, v) := by
  rw [amplitude_rescaled (regularizedCoefficients a χ R) J u Ω K ht hΩ hu hJ]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hp : (p, v) ∈ Ω
  · simp only [extendedDensity, indicator_of_mem hp]
    exact inputDensity_rescaled_regularized a J χ R ht _ (hJ (p, v) hp)
  · simp [extendedDensity, hp]

/-- Mixed jets of the original amplitude equal the rescaled amplitude jets
with one inverse dilation factor per frequency slot. This applies verbatim to
`regularizedCoefficients a χ R` and retains its squared regularization.
Source: `app:ch_background:eq:bg-symbol` and bg-frame Step 1. -/
theorem iteratedFDeriv_amplitude_rescaled
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p))
    (p : Variables n) (j : ℕ) (S : Finset (Fin j)) (v : Fin j → Variables n)
    (hk : ∀ i ∈ S, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hx : ∀ i ∉ S, (v i).2.2 = 0) :
    iteratedFDeriv ℝ j (amplitude a J u Ω K) (scaleFrequency t p) v =
      (t ^ S.card)⁻¹ •
        iteratedFDeriv ℝ j (amplitude (rescaledCoefficients a t) J u Ω K) p v := by
  have he := (frequencyDilationEquiv (n := n) t ht.ne').iteratedFDerivWithin_comp_right
    (amplitude a J u Ω K) uniqueDiffOn_univ (x := p) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  have hh : (fun q ↦ amplitude a J u Ω K (scaleFrequency t q)) =
      amplitude (rescaledCoefficients a t) J u Ω K :=
    funext (amplitude_rescaled a J u Ω K ht hΩ hu hJ)
  have hj := (congrArg (fun A ↦ A v) he).symm
  change iteratedFDeriv ℝ j (amplitude a J u Ω K) (scaleFrequency t p)
    (fun i ↦ scaleFrequency t (v i)) =
      iteratedFDeriv ℝ j (fun q ↦ amplitude a J u Ω K (scaleFrequency t q)) p v at hj
  rw [hh] at hj
  have hd (i : Fin j) : scaleFrequency t (v i) = (if i ∈ S then t else 1) • v i := by
    by_cases hi : i ∈ S
    · obtain ⟨h₁, h₂⟩ := hk i hi
      ext <;> simp [scaleFrequency, hi, h₁, h₂]
    · ext <;> simp [scaleFrequency, hi, hx i hi]
  simp_rw [hd] at hj
  rw [ContinuousMultilinearMap.map_smul_univ] at hj
  simp only [Fintype.prod_ite_mem, Finset.prod_const] at hj
  rw [← hj, inv_smul_smul₀ (pow_ne_zero _ ht.ne')]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
