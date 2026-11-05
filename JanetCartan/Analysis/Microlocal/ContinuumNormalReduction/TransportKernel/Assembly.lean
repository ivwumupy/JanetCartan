module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Integrability
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Regularization
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Reflection

/-!
# Full-amplitude action of the compact carrier normal

Assembly of the actual regularization, matrix Fubini calculation, and conic
substitution for `app:ch_background:eq:bg-full-complex-amplitude`. The geometric
inputs describe the genuine inverse charts and primitive measurability. They
contain no normal identity, integral estimate, or operator bound.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Classical
namespace JanetCartan.ContinuumRow.TransportKernel
variable {n N : ℕ}

/-- Primitive inputs at two output positions for the conic substitution in
`app:ch_background:eq:bg-full-complex-amplitude`. Actual phase-chart and
leading-wave producers must instantiate this record. It asserts neither
integrability nor an oscillatory integral identity. -/
structure ChartInputs (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) where
  coordinates : Euclidean n ≃ᵐ SliceVariable n
  measure_preserving : MeasurePreserving coordinates volume (volume.prod volume)
  domain : Euclidean 2 → Set (Euclidean n)
  phaseMap : Euclidean 2 → Euclidean n → Euclidean n
  inverse : Euclidean 2 → Euclidean n → Euclidean n
  derivative : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n
  domain_measurable : ∀ v, MeasurableSet (domain v)
  has_derivative : ∀ v t, t ∈ domain v →
    HasFDerivWithinAt (phaseMap v) (derivative v t) (domain v) t
  injective : ∀ v, InjOn (phaseMap v) (domain v)
  left_inverse : ∀ v t, t ∈ domain v → inverse v (phaseMap v t) = t
  determinant_ne_zero : ∀ v t, t ∈ domain v → (derivative v t).det ≠ 0
  support : ∀ v t, t ∉ domain v → ∀ i j,
    normalDensityEntry d m x y (chartCarrierVariable coordinates v t) i j = 0
  phase_identity : ∀ v t, t ∈ domain v →
    carrierPhase d x (chartCarrierVariable coordinates v t) -
      carrierPhase d y (chartCarrierVariable coordinates v t) =
        inner ℝ (d.chartPoint x - d.chartPoint y) (phaseMap v t)
  density_measurable : ∀ i j, Measurable (fun u ↦ normalDensityEntry d m x y u i j)
  inverse_measurable : Measurable (fun p : Euclidean 2 × Euclidean n ↦ inverse p.1 p.2)
  determinant_measurable : Measurable
    (fun p : Euclidean 2 × Euclidean n ↦ (derivative p.1 p.2).det)
  image_measurable : MeasurableSet
    {p : Euclidean 2 × Euclidean n | p.2 ∈ phaseMap p.1 '' domain p.1}

variable {d : CarrierData n N} {m : CarrierVariable n → ℝ}

/-- Literal spectator amplitude attached to a genuine conic chart, with both
positions and the squared regularization retained
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def ChartInputs.amplitude {x y : Torus n} (c : ChartInputs d m x y)
    (k : Euclidean n) (i j : Fin n) : ℝ :=
  fullAmplitudeEntry d m x y c.coordinates c.domain c.phaseMap c.inverse c.derivative k i j

/-- The chart amplitude represents the literal kernel; absolute convergence of
both Fubini steps is proved from the finite-band bounds
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem ChartInputs.normalEntry_eq (h : FiniteCarrierKernelBounds d m)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (c : ChartInputs d m x y) (i j : Fin n) :
    regularizedNormalEntry d m x y i j =
      ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) * (c.amplitude k i j : ℂ) :=
  regularizedNormalEntry_eq_fullAmplitude_of_finiteBand d m h hx hy
    c.coordinates c.measure_preserving c.domain c.phaseMap c.inverse c.derivative i j
    c.domain_measurable c.has_derivative c.injective c.left_inverse c.determinant_ne_zero
    (fun v t ht ↦ c.support v t ht i j) c.phase_identity (c.density_measurable i j)
    c.inverse_measurable c.determinant_measurable c.image_measurable

/-- The normalized PDO uses `(2π)^n` times the literal spectator amplitude
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem ChartInputs.normalEntry_eq_normalized (h : FiniteCarrierKernelBounds d m)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (c : ChartInputs d m x y) (i j : Fin n) :
    regularizedNormalEntry d m x y i j =
      (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (((2 * Real.pi) ^ n : ℂ) * (c.amplitude k i j : ℂ))) := by
  rw [integral_normalized_amplitude]
  exact c.normalEntry_eq h hx hy i j

/-- The spectator integral gives an absolutely integrable oscillatory amplitude
at finite regularization. This supplies the analytic input to frequency reflection
in `app:ch_background:eq:bg-real-symbol`. -/
theorem ChartInputs.integrable_amplitude (h : FiniteCarrierKernelBounds d m)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (c : ChartInputs d m x y) (i j : Fin n) :
    Integrable (fun k ↦ NormalComparison.oscillatoryFactor 1
      (inner ℝ (d.chartPoint x - d.chartPoint y) k) * (c.amplitude k i j : ℂ)) := by
  have hm := stronglyMeasurable_inverseDensityEntry d m x y c.coordinates c.domain
    c.phaseMap c.inverse c.derivative i j (c.density_measurable i j)
    c.inverse_measurable c.determinant_measurable c.image_measurable
  have hp : Continuous (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) p.2)) := by
    unfold NormalComparison.oscillatoryFactor
    fun_prop
  have hi := integrable_transformed_phase_density d m hx hy h
    c.coordinates c.measure_preserving c.domain c.phaseMap c.inverse c.derivative i j
    c.domain_measurable c.has_derivative c.injective c.left_inverse c.determinant_ne_zero
    (fun v t ht ↦ c.support v t ht i j) c.phase_identity
    (hp.stronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_stronglyMeasurable hm)).aestronglyMeasurable
  apply hi.integral_prod_right.congr
  apply Filter.Eventually.of_forall
  intro k
  dsimp only
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

/-- Reflection of the actual full amplitude, with the PDO normalization and
the factor four from real quadratures. This proves the two-position real kernel
formula; passing to its homogeneous principal diagonal remains the separate
symbol reduction (`app:ch_background:eq:bg-real-symbol`). -/
theorem ChartInputs.realNormalEntry_eq_normalized (h : FiniteCarrierKernelBounds d m)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (c : ChartInputs d m x y) (i j : Fin n) :
    ((4 * (regularizedNormalEntry d m x y i j).re : ℝ) : ℂ) =
      (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (((2 * Real.pi) ^ n : ℂ) *
            ((2 * (c.amplitude k i j + c.amplitude (-k) i j) : ℝ) : ℂ))) := by
  rw [integral_normalized_amplitude, c.normalEntry_eq h hx hy i j]
  exact (integral_reflected_eq_four_realPart (fun k ↦ c.amplitude k i j)
    (d.chartPoint x - d.chartPoint y) (c.integrable_amplitude h hx hy i j)).symm

/-- Exact output support of the matrix normal, inherited from the literal
kernel (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedNormalEntry_eq_zero_outside_right (x : Torus n) {y : Torus n}
    (hy : y ∉ d.outputChart) (i j : Fin n) :
    regularizedNormalEntry d m x y i j = 0 := by
  simp [regularizedNormalEntry, carrierKernel_eq_zero_outside d hy]

/-- The actual compact carrier normal acts by the full two-position amplitude.
Charts are required only where both output points lie in the output chart;
elsewhere the literal kernel is zero. This combines all finite matrix sums,
Fubini, and conic substitutions in
`app:ch_background:eq:bg-full-complex-amplitude`. The outer output integral is
still the original torus measure, not an unproved physical pushforward. -/
theorem regularizedOperator_normal_eq_fullAmplitude
    {Z : Set CarrierParameter} {R M C : ℝ}
    (h : CarrierRegularization.MaskHypotheses d m Z R M C)
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (w : ComplexOutputL2 n) :
    ∀ᵐ x ∂volume, ∀ hx : x ∈ d.outputChart, ∀ i,
      h.operator (h.operator.adjoint w) x i =
        ∑ j, ∫ y, (if hy : y ∈ d.outputChart then
          ∫ k, NormalComparison.oscillatoryFactor 1
            (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
              ((charts x hx y hy).amplitude k i j : ℂ)
          else 0) * w y j := by
  classical
  filter_upwards [regularizedOperator_normal_eq_matrix h w] with x hxnormal
  intro hx i
  rw [hxnormal i]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  by_cases hy : y ∈ d.outputChart
  · rw [dite_eq_left hy, (charts x hx y hy).normalEntry_eq
      (finiteCarrierKernelBoundsOfMask h) hx hy i j]
  · rw [dite_eq_right hy, regularizedNormalEntry_eq_zero_outside_right x hy i j]

end JanetCartan.ContinuumRow.TransportKernel
