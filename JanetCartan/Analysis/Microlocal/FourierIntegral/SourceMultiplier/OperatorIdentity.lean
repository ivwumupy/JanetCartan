module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.KernelIdentity

/-!
# Source-first graph multiplication for integrable amplitudes

The literal `graphOperator` integrates the source first. Absolute product
majorants justify changing that order for frequency-integrable amplitudes.
The kernel identity then proves `app:ch_regular_base:eq:fixed-source-multiplication`
for all literal compact frequency regularizations and integrable input data.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

private instance sourceMatrixNormable : IsNormableSpace ℂ (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (IsNormableSpace ℂ (Fin r → Fin r → ℂ))

/-- Continuous matrix action used to justify the source and frequency integrals
in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceMatrixAction : Matrix (Fin r) (Fin r) ℂ →L[ℂ]
    (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin ℂ ℂ)).toContinuousLinearMap

/-- Absolute integrability of the full source/frequency kernel from separate
L¹ inputs. This justifies the source-first Fubini interchange for
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOscillation_mulVec_integrable_prod
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Integrable (A x)) (hu : Integrable u) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 • (A x p.1).mulVec (u p.2))
      (volume.prod volume) := by
  let L := sourceMatrixAction (r := r)
  have hb := (hA.norm.mul_prod hu.norm).const_mul L.opNorm
  apply hb.mono'
  · have hpair := hA.aestronglyMeasurable.comp_fst.prodMk
      hu.aestronglyMeasurable.comp_snd
    exact (by unfold graphOscillation; fun_prop : Continuous
      (fun p : Euclidean n × Euclidean n ↦ graphOscillation S x p.2 p.1)).aestronglyMeasurable.smul (L.continuous₂.comp_aestronglyMeasurable hpair)
  · filter_upwards [] with p
    simp only [norm_smul, graphOscillation, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact (L.le_opNorm₂ (A x p.1) (u p.2)).trans_eq (mul_assoc _ _ _)

private theorem integrable_sourceKernel
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x y : Euclidean n) (hS : Continuous (S x)) (hA : Integrable (A x)) :
    Integrable (fun η ↦ graphOscillation S x y η • A x η) := by
  apply hA.norm.mono'
  · exact (by unfold graphOscillation; fun_prop : Continuous
      (fun η ↦ graphOscillation S x y η)).aestronglyMeasurable.smul hA.aestronglyMeasurable
  · filter_upwards [] with η
    simp only [norm_smul, graphOscillation, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- The source-first graph agrees with its integrated matrix kernel, proved by
Fubini from L¹ inputs. Used in the literal source identity
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_eq_kernelIntegral_of_integrable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Integrable (A x)) (hu : Integrable u) :
    graphOperator S (fun z _ η ↦ A z η) u x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ y, (∫ η, graphOscillation S x y η • A x η).mulVec (u y) := by
  unfold graphOperator
  congr 1
  rw [integral_integral_swap (graphOscillation_mulVec_integrable_prod S A u x hS hA hu)]
  apply integral_congr_ae
  filter_upwards [] with y
  have h := ((sourceMatrixAction (r := r)).flip (u y)).integral_comp_comm
    (integrable_sourceKernel S A x y hS hA)
  change (∫ η, (graphOscillation S x y η • A x η).mulVec (u y)) = (∫ η, graphOscillation S x y η • A x η).mulVec (u y) at h
  simpa only [Matrix.smul_mulVec] using h

/-- The exact source-first operator identity for every frequency-integrable
amplitude, in particular every compact frequency regularization. No Fourier
inversion or interchange is assumed. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceSymbol_of_integrable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (u : Euclidean n → Fin r → ℂ)
    (x : Euclidean n) (hS : Continuous (S x)) (hA : Continuous (A x))
    (hAi : Integrable (A x)) (hu : Integrable u) :
    graphOperator S (fun z _ η ↦ A z η) (fun y ↦ m y • u y) x =
      graphOperator S (fun z _ η ↦ sourceSymbol S A m z η) u x := by
  have hmu : Integrable (fun y ↦ m y • u y) := by
    apply (hu.norm.const_mul (SchwartzMap.seminorm ℂ 0 0 m)).mono'
    · exact m.continuous.aestronglyMeasurable.smul hu.aestronglyMeasurable
    · filter_upwards [] with y
      simpa only [norm_smul] using
        mul_le_mul_of_nonneg_right (m.norm_le_seminorm ℂ y) (norm_nonneg (u y))
  rw [graphOperator_eq_kernelIntegral_of_integrable S A _ x hS hAi hmu,
    graphOperator_eq_kernelIntegral_of_integrable S (sourceSymbol S A m) u x hS
      (sourceSymbol_integrable_of_integrable S A m x hS hA hAi) hu]
  simp_rw [integral_graphOscillation_sourceSymbol S A m x _ hS hA hAi,
    Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- Literal compact frequency regularization of the source multiplication
identity. The cutoff is retained at the original frequency `η + v` inside the
source symbol, exactly as in `app:ch_regular_base:eq:fixed-source-multiplication`.
The input `u` may already contain all physical masks and the fixed input Fourier
cutoff; its L¹ property is the only datum assumption here. -/
theorem graphOperator_sourceSymbol_frequencyCutoff
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (u : Euclidean n → Fin r → ℂ)
    (χ : Euclidean n → ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (hχ : Continuous χ) (hsχ : HasCompactSupport χ) (hu : Integrable u) :
    graphOperator S (fun z _ η ↦ χ η • A z η) (fun y ↦ m y • u y) x =
      graphOperator S (fun z _ η ↦ sourceSymbol S (fun z ξ ↦ χ ξ • A z ξ) m z η) u x := by
  apply graphOperator_sourceSymbol_of_integrable S (fun z ξ ↦ χ ξ • A z ξ) m u x hS
    (hχ.smul hA) _ hu
  exact (hχ.smul hA).integrable_of_hasCompactSupport (hsχ.smul_right)

end JanetCartan.FourierIntegral
