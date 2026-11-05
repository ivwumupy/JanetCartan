module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralLimit.SourceBounds
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Frequency integrability of literal test kernels

Source integration by parts, with the fixed reserve `n+2`, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. The consumer is the
pointwise cutoff-removal theorem in `SourceExpansion.LiteralLimit`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}

private theorem scalar_source_integral_eq_fourier
    (S : Euclidean n → Euclidean n → ℝ) (f : Euclidean n → ℂ)
    (x η : Euclidean n) :
    (∫ y, graphOscillation S x y η * f y) =
      Complex.exp (Complex.I * (S x η : ℂ)) * 𝓕 f ((2 * Real.pi)⁻¹ • η) := by
  rw [Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  unfold graphOscillation
  congr 1
  rw [inner_smul_right]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The scalar entry of the literal inner integral is integrable in physical
frequency. The derivative mass is proved by Leibniz from the full symbol bound
and the actual test function, with reserve `n+2`; no decay or outer
integrability is assumed (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem integrable_scalar_graph_sourceIntegral
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (μ : ℕ) {B : ℝ}
    (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : Euclidean n → Euclidean n → ℝ) (hS : Continuous (Function.uncurry S))
    (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (x : Euclidean n) (i j : Fin r) :
    Integrable (fun η ↦ ∫ y, graphOscillation S x y η * (A x y η i j * v y)) := by
  let g : Euclidean n → Euclidean n → ℂ :=
    fun ξ y ↦ A x y ((2 * Real.pi) • ξ) i j * v y
  have ha (η : Euclidean n) : ContDiff ℝ ∞ (fun y ↦ A x y η i j) :=
    contDiff_fullAmplitudeParameterJet_entry A hA [] x η i j
  have hg : Continuous (Function.uncurry g) := by
    exact (((matrixEntryEvaluation i j).continuous.comp hA.continuous).comp
      (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, (2 * Real.pi) • p.1))
      (by fun_prop)).mul (hv.continuous.comp continuous_snd)
  have hF : Integrable (fun ξ ↦ 𝓕 (g ξ) ξ) := by
    apply Pseudodifferential.integrable_sourceFourier_of_compact_derivativeMass
      g hg 0 (lowReserve n)
    · simp [lowReserve, Euclidean]
    · intro ξ
      exact ((ha _).mul hv).of_le (by simp)
    · intro ξ
      exact hvc.mul_left
    · intro ξ
      simpa only [pow_zero, mul_one] using
        sourceDerivativeMass_mul_le (ha _) hv hvc (lowReserve n)
          (fun k hk y ↦ norm_iteratedFDeriv_fullAmplitude_entry_le A hA hb k
            (by omega) x _ y i j)
  have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hF' : Integrable (fun η ↦ 𝓕 (fun y ↦ A x y η i j * v y) ((2 * Real.pi)⁻¹ • η)) := by
    simpa only [g, smul_smul, mul_inv_cancel₀ hp, one_smul] using
      hF.comp_smul (inv_ne_zero hp)
  have hc : Continuous (fun η ↦ Complex.exp (Complex.I * (S x η : ℂ))) := by
    have : Continuous (fun η ↦ S x η) := hS.comp (continuous_const.prodMk continuous_id)
    fun_prop
  have hi := hF'.bdd_smul 1 hc.aestronglyMeasurable
    (Eventually.of_forall (fun η ↦ by simp [Complex.norm_exp]))
  simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, scalar_source_integral_eq_fourier] using hi

private theorem integrable_graph_source_entry
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (S : Euclidean n → Euclidean n → ℝ)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (x η : Euclidean n) (i j : Fin r) :
    Integrable (fun y ↦ graphOscillation S x y η * (A x y η i j * v y j)) := by
  have ha := contDiff_fullAmplitudeParameterJet_entry A hA [] x η i j
  have hosc : Continuous (fun y ↦ graphOscillation S x y η) := by
    unfold graphOscillation
    fun_prop
  apply (hosc.mul (ha.continuous.mul ((continuous_apply j).comp hv.continuous))).integrable_of_hasCompactSupport
  exact (hvc.comp_left (g := fun w : Fin r → ℂ ↦ w j) rfl).mul_left.mul_left

/-- Absolute frequency integrability after the original source integration,
with ordered matrix multiplication and Euclidean Lebesgue measure. The proof
uses `n+2` source derivatives of the actual test product, including every
original source cutoff (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem integrable_graph_sourceIntegral
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (μ : ℕ) {B : ℝ}
    (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : Euclidean n → Euclidean n → ℝ) (hS : Continuous (Function.uncurry S))
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (x : Euclidean n) :
    Integrable (fun η ↦ ∫ y, graphOscillation S x y η • (A x y η).mulVec (v y)) := by
  classical
  have he (η : Euclidean n) (i : Fin r) :
      (∫ y, graphOscillation S x y η • (A x y η).mulVec (v y)) i =
        ∑ j, ∫ y, graphOscillation S x y η * (A x y η i j * v y j) := by
    have hi (i : Fin r) : Integrable (fun y ↦
        (graphOscillation S x y η • (A x y η).mulVec (v y)) i) := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact integrable_finsetSum _ fun j _ ↦ integrable_graph_source_entry A hA S v hv hvc x η i j
    rw [eval_integral hi]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact integral_finsetSum _ fun j _ ↦ integrable_graph_source_entry A hA S v hv hvc x η i j
  apply Integrable.of_eval
  intro i
  simp_rw [he]
  apply integrable_finsetSum
  intro j _
  exact integrable_scalar_graph_sourceIntegral A hA μ hb S hS (fun y ↦ v y j)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r ↦ ℂ) j).contDiff.comp hv)
    (hvc.comp_left (g := fun w : Fin r → ℂ ↦ w j) rfl) x i j

end JanetCartan.FourierIntegral.SourceExpansion
