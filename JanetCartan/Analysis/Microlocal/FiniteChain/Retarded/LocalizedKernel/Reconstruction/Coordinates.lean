module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Rescaling
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SymbolOperator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Product coordinates for complementary output reconstruction

The physical product uses the maximum norm, whereas Fourier inversion uses an
inner product domain. The volume-preserving `WithLp` equivalence and the radian
Jacobian identify the two literal kernel integrals in
`app:ch_regular:lem:finite-chain`, including `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Volume transport used by `leftOperator_eq_cyclesKernel` in the reconstruction
of the identity contribution (`app:ch_regular:eq:chain-tail`). -/
theorem integral_product_eq_integral_ofLp (f : ℝ × E → ℂ) :
    (∫ x, f x) = ∫ x : WithLp 2 (ℝ × E), f x.ofLp :=
  ((WithLp.volume_preserving_ofLp ℝ E).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × E)).symm.measurableEmbedding f).symm

/-- The radian left kernel is the cycles kernel on the inner product domain;
both the Jacobian and product volume transport are explicit
(`app:ch_regular:lem:finite-chain`). -/
theorem leftKernel_eq_cyclesKernel (m : (ℝ × E) → (ℝ × E) → ℂ)
    (x y : WithLp 2 (ℝ × E)) :
    leftKernel m x.ofLp y.ofLp =
      Pseudodifferential.amplitudeKernel
        (fun x _y ξ : WithLp 2 (ℝ × E) => m x.ofLp ((2 * Real.pi) • ξ.ofLp)) x y := by
  rw [leftKernel, ← Complex.real_smul, normalization_smul_integral,
    integral_product_eq_integral_ofLp, Pseudodifferential.amplitudeKernel_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [wave, pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inner_smul_left, WithLp.prod_inner_apply, WithLp.ofLp_sub, Prod.fst_sub,
    Prod.snd_sub, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

/-- Transport the physical left operator to the literal cycles kernel, consumed
by `tendsto_leftOperator_complementarySymbol` (`app:ch_regular:eq:chain-tail`). -/
theorem leftOperator_eq_cyclesKernel (m : (ℝ × E) → (ℝ × E) → ℂ)
    (v : ℝ × E → ℂ) (x : WithLp 2 (ℝ × E)) :
    leftOperator m v x.ofLp = ∫ y : WithLp 2 (ℝ × E), v y.ofLp •
      Pseudodifferential.amplitudeKernel
        (fun x _y ξ : WithLp 2 (ℝ × E) => m x.ofLp ((2 * Real.pi) • ξ.ofLp)) x y := by
  rw [leftOperator, integral_product_eq_integral_ofLp]
  simp_rw [leftKernel_eq_cyclesKernel, smul_eq_mul, mul_comm]

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
