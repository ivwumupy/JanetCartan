module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Basic
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Smoothness of the regularized quantizations

The compact frequency and source carriers justify differentiation of the actual
kernel integrals in `app:ch_regular:lem:finite-chain`, “Retarded and signed
factors”. The resulting smooth right quantization is the input to the retarded
Sobolev smoothness theorem and to the physical composition argument.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner

namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel

private theorem contDiff_integral_carrier
    {V Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [MeasureSpace Z] [BorelSpace Z] [IsFiniteMeasureOnCompacts (volume : Measure Z)]
    (f : V × Z → ℂ) (hf : ContDiff ℝ ∞ f)
    (K : Set Z) (hK : IsCompact K) (hs : ∀ x z, z ∉ K → f (x,z) = 0) :
    ContDiff ℝ ∞ (fun x => ∫ z, f (x,z)) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have h := JanetCartan.contDiffOn_compactParameterIntegral
    (μ := volume) isOpen_univ isOpen_univ hK (subset_univ _)
    hf.contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  ext x
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs x)).symm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Joint smoothness of the radian character, used for differentiation of the
actual left and right kernels (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_wave : ContDiff ℝ ∞ (Function.uncurry (wave (E := E))) := by
  unfold Function.uncurry wave pairing
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp
      ((contDiff_fst.fst.mul contDiff_snd.fst).add
        (contDiff_fst.snd.inner ℝ contDiff_snd.snd))).mul contDiff_const)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Joint smoothness of the actual right kernel follows from the compact
frequency projection of the input symbol (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_rightKernel (mi : (ℝ × E) → (ℝ × E) → ℂ)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (his : HasCompactSupport (Function.uncurry mi)) :
    ContDiff ℝ ∞ (Function.uncurry (rightKernel mi)) := by
  have hf : ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × E) =>
      wave p.2 (p.1.1-p.1.2) * mi p.1.2 p.2) :=
    (contDiff_wave.comp (contDiff_snd.prodMk
      (contDiff_fst.fst.sub contDiff_fst.snd))).mul
        (hi.comp (contDiff_fst.snd.prodMk contDiff_snd))
  have hs (x : (ℝ × E) × (ℝ × E)) (ξ : ℝ × E)
      (hξ : ξ ∉ Prod.snd '' tsupport (Function.uncurry mi)) :
      wave ξ (x.1-x.2) * mi x.2 ξ = 0 := by
    have hm : mi x.2 ξ = 0 := image_eq_zero_of_notMem_tsupport
      (f := Function.uncurry mi) (x := (x.2,ξ)) (fun h => hξ ⟨(x.2,ξ), h, rfl⟩)
    rw [hm, mul_zero]
  exact contDiff_const.mul (contDiff_integral_carrier _ hf _
    (his.image continuous_snd) hs)

/-- Joint smoothness of the regularized complementary left kernel, including
the identity contribution (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_leftKernel_complementarySymbol
    (mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    (hrs : HasCompactSupport r) :
    ContDiff ℝ ∞ (Function.uncurry (leftKernel (complementarySymbol r mo))) := by
  have hf : ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × E) =>
      wave p.2 (p.1.1-p.1.2) * (r p.2 * (1-mo p.1.1 p.2))) := by
    exact (contDiff_wave.comp (contDiff_snd.prodMk
      (contDiff_fst.fst.sub contDiff_fst.snd))).mul
      ((hr.comp contDiff_snd).mul
        (contDiff_const.sub (ho.comp (contDiff_fst.fst.prodMk contDiff_snd))))
  exact contDiff_const.mul (contDiff_integral_carrier _ hf _ hrs
    (fun x ξ hξ => by simp [image_eq_zero_of_notMem_tsupport hξ]))
/-- The literal right quantization of a smooth compact input is smooth. All
differentiation under its defining integrals is justified by compact carriers
(`app:ch_regular:lem:finite-chain`). This is consumed by retarded smoothness. -/
theorem contDiff_rightOperator (mi : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (his : HasCompactSupport (Function.uncurry mi))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ContDiff ℝ ∞ (rightOperator mi u) := by
  exact contDiff_integral_carrier _
    ((contDiff_rightKernel mi hi his).mul (hu.comp contDiff_snd)) _ hus
    (fun x y hy => by simp [image_eq_zero_of_notMem_tsupport hy])

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
