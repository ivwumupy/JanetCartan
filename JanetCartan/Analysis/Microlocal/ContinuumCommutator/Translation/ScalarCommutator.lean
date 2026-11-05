module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.ScalarBound

/-!
# Scalar Euclidean translation commutators

The order-one difference-quotient argument in
`app:ch_background:prop:bg-inverse`: the divided full amplitude realizes the
actual conjugation difference. Linearity of the literal Lebesgue kernels and
strong frequency exhaustion establish the identity on every L² datum.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Kernel linearity used to identify the divided full amplitude in
`app:ch_background:prop:bg-inverse`. Continuity supplies absolute integrability
on the frequency ball before subtraction is moved outside the integral. -/
theorem compactFrequencyAmplitudeKernel_smul_sub
    (b c : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : Continuous (Function.uncurry b)) (hc : Continuous (Function.uncurry c))
    (s ρ : ℝ) (x y : E) :
    compactFrequencyAmplitudeKernel (fun ξ z ↦ s • (b ξ z - c ξ z)) ρ x y =
      s • (compactFrequencyAmplitudeKernel b ρ x y -
        compactFrequencyAmplitudeKernel c ρ x y) := by
  have hi (a : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
      (ha : Continuous (Function.uncurry a)) :
      IntegrableOn (fun ξ ↦
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          a ξ (pairedPosition x y)) (Metric.closedBall 0 ρ) := by
    apply ContinuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)
    exact ((by fun_prop : Continuous (fun ξ : E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I))).mul
      (ha.comp (continuous_id.prodMk continuous_const))).continuousOn
  simp only [compactFrequencyAmplitudeKernel, mul_smul_comm, mul_sub]
  rw [integral_smul, integral_sub (hi b hb) (hi c hc)]

/-- Linearity of the literal physical integral on arbitrary Lebesgue L² data.
Compact physical support supplies the integrability needed by the scalar
commutator in `app:ch_background:prop:bg-inverse`. -/
theorem integral_compactFrequencyAmplitudeKernel_smul_sub
    (b c : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : Continuous (Function.uncurry b)) (hc : Continuous (Function.uncurry c))
    (Rb Rc : ℝ) (hbs : ∀ ξ, SupportedInCenteredBox Rb (b ξ))
    (hcs : ∀ ξ, SupportedInCenteredBox Rc (c ξ))
    (s ρ : ℝ) (u : L²) (x : E) :
    (∫ y, compactFrequencyAmplitudeKernel (fun ξ z ↦ s • (b ξ z - c ξ z))
        ρ x y * u y) =
      s • ((∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y) -
        ∫ y, compactFrequencyAmplitudeKernel c ρ x y * u y) := by
  simp only [compactFrequencyAmplitudeKernel_smul_sub b c hb hc,
    smul_mul_assoc, sub_mul]
  rw [integral_smul, integral_sub
    (integrable_compactKernel_mul_L2 (continuous_compactFrequencyAmplitudeKernel hb ρ)
      (hasCompactSupport_compactFrequencyAmplitudeKernel hbs ρ) u x)
    (integrable_compactKernel_mul_L2 (continuous_compactFrequencyAmplitudeKernel hc ρ)
      (hasCompactSupport_compactFrequencyAmplitudeKernel hcs ρ) u x)]

/-- The inverse translation identity on literal Lebesgue L², used to factor
the commutator in `app:ch_background:prop:bg-inverse`. -/
theorem euclideanL2Translation_neg_apply (a : E) (u : L²) :
    euclideanL2Translation (-a) (euclideanL2Translation a u) = u := by
  apply Lp.ext
  filter_upwards [euclideanL2Translation_coe (-a) (euclideanL2Translation a u),
    (measurePreserving_add_right volume (-a)).quasiMeasurePreserving.ae
      (euclideanL2Translation_coe a u)] with x h₁ h₂
  simpa only [neg_add_cancel_right] using h₁.trans h₂

/-- The Euclidean difference quotient on every Lebesgue L² datum, without
an H¹ premise (`app:ch_background:prop:bg-inverse`). -/
def euclideanL2DifferenceQuotient (i : Fin d) (h : ℝ) : L² →L[ℂ] L² :=
  h⁻¹ • ((euclideanL2Translation (h • EuclideanSpace.single i 1)).toContinuousLinearMap -
    ContinuousLinearMap.id ℂ L²)

/-- The divided conjugation difference for the positive-shift convention
of `euclideanL2Translation` (`app:ch_background:prop:bg-inverse`). -/
def euclideanConjugationDifference (B : L² →L[ℂ] L²) (i : Fin d) (h : ℝ) :
    L² →L[ℂ] L² :=
  h⁻¹ • ((euclideanL2Translation (h • EuclideanSpace.single i 1)).toContinuousLinearMap.comp
    (B.comp (euclideanL2Translation (-(h • EuclideanSpace.single i 1))).toContinuousLinearMap) - B)

/-- The exact scalar commutator factors as the divided conjugation difference
followed by an isometric translation (`app:ch_background:prop:bg-inverse`). -/
theorem euclideanL2DifferenceQuotient_commutator
    (B : L² →L[ℂ] L²) (i : Fin d) (h : ℝ) (u : L²) :
    euclideanL2DifferenceQuotient i h (B u) - B (euclideanL2DifferenceQuotient i h u) =
      euclideanConjugationDifference B i h
        (euclideanL2Translation (h • EuclideanSpace.single i 1) u) := by
  change h⁻¹ • (euclideanL2Translation (h • EuclideanSpace.single i 1) (B u) - B u) -
    B (h⁻¹ • (euclideanL2Translation (h • EuclideanSpace.single i 1) u - u)) =
      h⁻¹ • (euclideanL2Translation (h • EuclideanSpace.single i 1)
        (B (euclideanL2Translation (-(h • EuclideanSpace.single i 1))
          (euclideanL2Translation (h • EuclideanSpace.single i 1) u))) -
        B (euclideanL2Translation (h • EuclideanSpace.single i 1) u))
  rw [euclideanL2Translation_neg_apply, B.map_smul_of_tower, map_sub]
  module

section Amplitude

variable (hd : 0 < d) (R h₀ : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀)

include hh hsmall

/-- At each compact frequency radius the divided amplitude is the divided
operator subtraction, by linearity of its actual kernel
(`app:ch_background:prop:bg-inverse`). -/
theorem twoPositionCompactFrequencyL2Operator_translationDifferenceAmplitude
    (ρ : ℝ) (u : L²) :
    twoPositionCompactFrequencyL2Operator hd (R + h₀) (translationDifferenceAmplitude b i h)
      (contDiff_uncurry_translationDifferenceAmplitude b hb i h)
      (supportedInCenteredBox_translationDifferenceAmplitude b R h₀ hs i h hsmall) (2 * A)
      (hasAmplitudeDerivativeBound_translationDifferenceAmplitude b
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA h hh) ρ u =
      h⁻¹ • (twoPositionCompactFrequencyL2Operator hd (R + h₀) (translatedAmplitude b i h)
        (contDiff_uncurry_translatedAmplitude b hb i h)
        (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
        (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) h) ρ u -
        twoPositionCompactFrequencyL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) ρ u) := by
  let D := twoPositionCompactFrequencyL2Operator hd (R + h₀)
    (translationDifferenceAmplitude b i h)
    (contDiff_uncurry_translationDifferenceAmplitude b hb i h)
    (supportedInCenteredBox_translationDifferenceAmplitude b R h₀ hs i h hsmall) (2 * A)
    (hasAmplitudeDerivativeBound_translationDifferenceAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA h hh) ρ
  let T := twoPositionCompactFrequencyL2Operator hd (R + h₀) (translatedAmplitude b i h)
    (contDiff_uncurry_translatedAmplitude b hb i h)
    (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
    (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A
      (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) h) ρ
  let B := twoPositionCompactFrequencyL2Operator hd R b hb hs A
    (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) ρ
  change D u = h⁻¹ • (T u - B u)
  apply Lp.ext
  filter_upwards [twoPositionCompactFrequencyL2Operator_ae_kernel
    hd (R + h₀) (translationDifferenceAmplitude b i h) _ _ (2 * A) _ ρ u,
    twoPositionCompactFrequencyL2Operator_ae_kernel
      hd (R + h₀) (translatedAmplitude b i h) _ _ A _ ρ u,
    twoPositionCompactFrequencyL2Operator_ae_kernel hd R b hb hs A
      (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) ρ u,
    Lp.coeFn_smul h⁻¹ (T u - B u), Lp.coeFn_sub (T u) (B u)] with x hD hT hB hsm hsub
  change D u x = _ at hD
  change T u x = _ at hT
  change B u x = _ at hB
  change (h⁻¹ • (T u - B u)) x = h⁻¹ • (T u - B u) x at hsm
  change (T u - B u) x = T u x - B u x at hsub
  rw [hD, hsm, hsub, hT, hB]
  exact integral_compactFrequencyAmplitudeKernel_smul_sub (translatedAmplitude b i h) b
    (contDiff_uncurry_translatedAmplitude b hb i h).continuous hb.continuous
    (R + h₀) R (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) hs
    h⁻¹ ρ u x

/-- Strong frequency exhaustion identifies the divided amplitude with the
actual divided conjugation difference on every Euclidean L² datum
(`app:ch_background:prop:bg-inverse`). The base operator uses only the lower
budget extracted from the original primitive derivative hypothesis. -/
theorem translationDifferenceL2Operator_apply_eq_conjugation_sub (u : L²) :
    translationDifferenceL2Operator hd R h₀ b hb hs A hA i h hh hsmall u =
      h⁻¹ • (euclideanL2Translation (h • EuclideanSpace.single i 1)
        (twoPositionL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his))
          (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)) -
        twoPositionL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) u) := by
  erw [twoPositionL2Operator_conjugate hd R h₀ b hb hs A
    (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) i h hsmall u]
  apply tendsto_nhds_unique
    (tendsto_twoPositionCompactFrequencyL2Operator hd (R + h₀)
      (translationDifferenceAmplitude b i h) _ _ (2 * A) _ u)
  exact (((tendsto_twoPositionCompactFrequencyL2Operator hd (R + h₀)
    (translatedAmplitude b i h) _ _ A _ u).sub
    (tendsto_twoPositionCompactFrequencyL2Operator hd R b hb hs A _ u)).const_smul h⁻¹).congr
      (fun ρ ↦ (twoPositionCompactFrequencyL2Operator_translationDifferenceAmplitude
        hd R h₀ b hb hs A hA i h hh hsmall ρ u).symm)

/-- Equality of continuous linear operators: the FTC amplitude is exactly
`h⁻¹ • (τₕ E τ₋ₕ - E)`, with the original amplitude and its extracted lower
budget (`app:ch_background:prop:bg-inverse`). -/
theorem translationDifferenceL2Operator_eq_conjugationDifference :
    translationDifferenceL2Operator hd R h₀ b hb hs A hA i h hh hsmall =
      euclideanConjugationDifference
        (twoPositionL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his))) i h := by
  apply ContinuousLinearMap.ext
  intro u
  exact translationDifferenceL2Operator_apply_eq_conjugation_sub
    hd R h₀ b hb hs A hA i h hh hsmall u

/-- The divided conjugation difference of the original scalar PDO is
uniformly bounded in the nonzero step, with the fixed enlarged box constant
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_euclideanConjugationDifference_twoPositionL2Operator_le :
    ‖euclideanConjugationDifference
      (twoPositionL2Operator hd R b hb hs A
        (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his))) i h‖ ≤
      fixedBoxAmplitudeConstant d (R + h₀) * (2 * A) := by
  rw [← translationDifferenceL2Operator_eq_conjugationDifference
    hd R h₀ b hb hs A hA i h hh hsmall]
  exact norm_translationDifferenceL2Operator_le hd R h₀ b hb hs A hA i h hh hsmall

/-- The actual scalar difference-quotient commutator is the divided-amplitude
operator applied to a translation of the input. This keeps both physical
positions and literal Lebesgue measure (`app:ch_background:prop:bg-inverse`). -/
theorem euclideanL2DifferenceQuotient_twoPositionL2Operator_commutator (u : L²) :
    euclideanL2DifferenceQuotient i h
        (twoPositionL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) u) -
      twoPositionL2Operator hd R b hb hs A
        (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his))
        (euclideanL2DifferenceQuotient i h u) =
      translationDifferenceL2Operator hd R h₀ b hb hs A hA i h hh hsmall
        (euclideanL2Translation (h • EuclideanSpace.single i 1) u) := by
  rw [translationDifferenceL2Operator_eq_conjugationDifference
    hd R h₀ b hb hs A hA i h hh hsmall]
  exact euclideanL2DifferenceQuotient_commutator _ i h u

/-- Uniform scalar Euclidean difference-quotient commutator estimate on all
L² data, from the primitive derivative budget of the full amplitude
(`app:ch_background:prop:bg-inverse`). No Sobolev regularity of the datum is
assumed, and the constant is independent of `h` for `0 < |h| ≤ h₀`. -/
theorem norm_euclideanL2DifferenceQuotient_twoPositionL2Operator_commutator_le
    (u : L²) :
    ‖euclideanL2DifferenceQuotient i h
        (twoPositionL2Operator hd R b hb hs A
          (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his)) u) -
      twoPositionL2Operator hd R b hb hs A
        (fun ξ is his ↦ hA ξ is (Nat.le_succ_of_le his))
        (euclideanL2DifferenceQuotient i h u)‖ ≤
      (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A)) * ‖u‖ := by
  rw [euclideanL2DifferenceQuotient_twoPositionL2Operator_commutator
    hd R h₀ b hb hs A hA i h hh hsmall u]
  simpa only [LinearIsometry.norm_map] using
    norm_translationDifferenceL2Operator_apply_le hd R h₀ b hb hs A hA i h hh hsmall
      (euclideanL2Translation (h • EuclideanSpace.single i 1) u)

end Amplitude

end JanetCartan.ContinuumCommutator
