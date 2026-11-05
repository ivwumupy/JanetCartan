module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.SchwartzInput
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.PolynomialGrowth
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.Regularization

/-!
# Removing the compact frequency regularization

Both sides of `app:ch_regular_base:eq:fixed-source-multiplication` converge on
Schwartz inputs. The compact-frequency Fubini identity therefore passes to the
actual source-first graph integral for arbitrary polynomial-growth symbols.
All measures and Fourier frequencies are Euclidean and physical.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Matrix.Norms.Frobenius RealInnerProductSpace Topology
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Literal compact frequency truncation converges on Schwartz inputs for every
polynomial amplitude in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_tendsto_frequencyCutoff
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (C : ℝ) (k : ℕ) (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (χ : ℕ → Euclidean n → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχbound : ∀ j η, ‖χ j η‖ ≤ 1)
    (hχlim : ∀ η, Tendsto (fun j ↦ χ j η) atTop (𝓝 1)) :
    Tendsto (fun j ↦ graphOperator S (fun z _ η ↦ χ j η • A z η) u x)
      atTop (𝓝 (graphOperator S (fun z _ η ↦ A z η) u x)) := by
  apply graphOperator_tendsto_of_polynomialBound S _ A u x hS
    (fun j ↦ ((hχ j).smul hA).aestronglyMeasurable) C k
  · intro j η
    exact (norm_smul_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hχbound j η) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hbound η))
  · intro η
    simpa only [one_smul] using (hχlim η).smul_const (A x η)

/-- The exact transformed symbols converge at the level of actual source-first
graph operators, with the cutoff retained at `η + v`. This is the second limit
needed in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceSymbol_tendsto_frequencyCutoff
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (χ : ℕ → Euclidean n → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχbound : ∀ j η, ‖χ j η‖ ≤ 1)
    (hχlim : ∀ η, Tendsto (fun j ↦ χ j η) atTop (𝓝 1)) :
    Tendsto (fun j ↦ graphOperator S
      (fun z _ η ↦ sourceSymbol S (fun z ξ ↦ χ j ξ • A z ξ) m z η) u x)
      atTop (𝓝 (graphOperator S (fun z _ η ↦ sourceSymbol S A m z η) u x)) := by
  apply graphOperator_tendsto_of_polynomialBound S _ (sourceSymbol S A m) u x hS
    (fun j ↦ (sourceSymbol_stronglyMeasurable S _ m x hS
      ((hχ j).smul hA)).aestronglyMeasurable)
    (C * (1 + 2 ^ (k - 1)) * ∫ v,
      ‖sourceFourierTransform m v‖ + ‖v‖ ^ k * ‖sourceFourierTransform m v‖) k
  · intro j η
    apply sourceSymbol_polynomial_majorant S _ m x η C hC k
    intro ξ
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hχbound j ξ) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound ξ)
  · intro η
    obtain ⟨D, hD⟩ := sourceAmplitude_shifted_growth A x η C hC k hbound
    exact sourceSymbol_tendsto_frequencyCutoff S A m x η hS hA D k hD χ hχ hχbound hχlim

private theorem exists_sourceFrequencyCutoffs (n : ℕ) :
    ∃ χ : ℕ → Euclidean n → ℂ,
      (∀ j, Continuous (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j η, ‖χ j η‖ ≤ 1) ∧
      (∀ η, Tendsto (fun j ↦ χ j η) atTop (𝓝 1)) := by
  let χ : ℕ → Euclidean n → ℂ := fun j η ↦
    (max 0 (min 1 ((j : ℝ) + 1 - ‖η‖)) : ℝ)
  refine ⟨χ, (fun j ↦ by dsimp [χ]; fun_prop), ?_, ?_, ?_⟩
  · intro j
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Euclidean n) ((j : ℝ) + 1))
    intro η hη
    by_contra h
    have ht : (j : ℝ) + 1 < ‖η‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h
    have hz : χ j η = 0 := by
      dsimp [χ]
      rw [min_eq_right (by linarith), max_eq_left (by linarith), Complex.ofReal_zero]
    exact hη hz
  · intro j η
    dsimp [χ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (min_le_left _ _)
  · intro η
    obtain ⟨N, hN⟩ := exists_nat_ge ‖η‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
    dsimp [χ]
    rw [min_eq_left (by linarith), max_eq_right (by norm_num), Complex.ofReal_one]

/-- The exact source-first multiplication theorem for the extended real phase
and a polynomial-growth source-independent symbol. All interchanges and the
removal of compact frequency regularization are proved. Smooth compact source
cutoffs are particular Schwartz multipliers. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceSymbol
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    graphOperator S (fun z _ η ↦ A z η) (fun y ↦ m y • u y) x =
      graphOperator S (fun z _ η ↦ sourceSymbol S A m z η) u x := by
  obtain ⟨χ, hχ, hsχ, hbχ, hlχ⟩ := exists_sourceFrequencyCutoffs n
  let mu := SchwartzMap.smulLeftCLM (Fin r → ℂ) (m : Euclidean n → ℂ) u
  have hmu : (mu : Euclidean n → Fin r → ℂ) = fun y ↦ m y • u y := by
    funext y
    exact SchwartzMap.smulLeftCLM_apply_apply m.hasTemperateGrowth u y
  have hleft := graphOperator_tendsto_frequencyCutoff S A mu x hS hA C k hbound
    χ hχ hbχ hlχ
  rw [hmu] at hleft
  have hright := graphOperator_sourceSymbol_tendsto_frequencyCutoff S A m u x
    hS hA C hC k hbound χ hχ hbχ hlχ
  have he (j : ℕ) := graphOperator_sourceSymbol_frequencyCutoff S A m u (χ j) x
    hS hA (hχ j) (hsχ j) u.integrable
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

end JanetCartan.FourierIntegral
