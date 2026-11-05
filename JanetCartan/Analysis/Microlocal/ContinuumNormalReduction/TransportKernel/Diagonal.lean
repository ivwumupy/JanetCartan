module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.SymbolBridge
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.OscillatoryDiagonal

/-!
# The literal reflected amplitude in diagonal reduction

The exact source-tested reduction for `app:ch_background:eq:bg-real-symbol`
uses the shared Taylor/divergence remainder. Frequency is converted explicitly
from physical `k` to the Fourier convention `k = 2πξ`. Source Fourier
integrability remains an input of the unregularized reduction; no bounded
unregularized carrier is assumed. Quantitative order-minus-one estimates and
uniform tame bounds for the bounded-frequency completion remain quantitative
obligations. The smooth completion kernel is constructed in `TransportKernel.Completion`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
  {x₀ y₀ : Torus n} {c : ChartInputs d m x₀ y₀}

/-- The physical covector substitution `k = 2πξ`, with its Lebesgue Jacobian,
for the normalization in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitudeKernel_eq_physicalFrequency_integral {n : ℕ} (A : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (x y : Euclidean n) :
    Pseudodifferential.amplitudeKernel (fun x y ξ ↦ A x y ((2 * Real.pi) • ξ)) x y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (x - y) k) * A x y k := by
  rw [Pseudodifferential.amplitudeKernel_eq_integral]
  have he : (fun ξ : Euclidean n ↦
      Complex.exp ((2 * Real.pi * inner ℝ ξ (x - y) : ℝ) * Complex.I) •
        A x y ((2 * Real.pi) • ξ)) =
      (fun k ↦ NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) * A x y k) ∘
        (fun ξ ↦ (2 * Real.pi) • ξ) := by
    funext ξ
    simp only [Function.comp_apply, NormalComparison.oscillatoryFactor,
      inner_smul_right, real_inner_comm (x - y) ξ, one_mul, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [he]
  have hc := Measure.integral_comp_smul_of_nonneg volume
    (fun k ↦ NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) * A x y k)
    (2 * Real.pi) (hR := by positivity)
  dsimp only [Function.comp_def]
  rw [hc]
  simp [finrank_euclideanSpace, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul]

/-- The shared normalized reflected amplitude in the Fourier convention used
by the PDO calculus. The argument is `2πξ`, not `ξ`
(`app:ch_background:eq:bg-real-symbol`). -/
def SymbolInputs.unitReflectedEntry (s : SymbolInputs c) (i j : Fin n)
    (x y ξ : Euclidean n) : ℂ :=
  reflectedSymbolAmplitude s.coefficients s.jacobian s.inverse s.domain
    s.spectatorSupport (x, y, (2 * Real.pi) • ξ) i j

/-- The literal real finite-band normal is exactly the kernel used in the
shared PDO diagonal calculus, after the checked Lebesgue frequency substitution
`k = 2πξ` (`app:ch_background:eq:bg-real-symbol`). -/
theorem SymbolInputs.realNormalEntry_eq_amplitudeKernel
    (s : SymbolInputs c) (h : FiniteCarrierKernelBounds d m)
    (hx : x₀ ∈ d.outputChart) (hy : y₀ ∈ d.outputChart) (i j : Fin n) :
    ((4 * (regularizedNormalEntry d m x₀ y₀ i j).re : ℝ) : ℂ) =
      Pseudodifferential.amplitudeKernel (s.unitReflectedEntry i j)
        (d.chartPoint x₀) (d.chartPoint y₀) := by
  exact (s.realNormalEntry_eq_symbol h hx hy i j).trans
    (amplitudeKernel_eq_physicalFrequency_integral (fun x y k ↦
      (reflectedSymbolAmplitude s.coefficients s.jacobian s.inverse s.domain
        s.spectatorSupport (x, y, k) i j : ℂ)) (d.chartPoint x₀) (d.chartPoint y₀)).symm

/-- Primitive smoothness and global support buffers give the exact smooth
amplitude required by diagonal reduction (`app:ch_background:eq:bg-real-symbol`). -/
theorem SymbolInputs.unitReflectedEntry_contDiff (s : SymbolInputs c) (i j : Fin n)
    (hclosed : IsClosed (s.forward '' s.inputSupport))
    (hbuffer : s.forward '' s.inputSupport ⊆ s.domain) :
    ContDiff ℝ ∞ (fun p : TransportSymbol.Variables n ↦ s.unitReflectedEntry i j p.1 p.2.1 p.2.2) := by
  have ha := reflectedSymbolAmplitude_contDiff s.coefficients s.jacobian s.inverse s.forward
    s.domain_open s.regularity s.inverse_smooth s.inverse_maps s.right_inverse s.primitive_support
    hclosed hbuffer s.compact_spectator
  exact Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp ha).comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul (2 * Real.pi)))))

/-- Exact diagonal reduction of the actual reflected amplitude on compact
physical source tests, with the source cutoff and literal Taylor/divergence
remainder retained. The four source Fourier integrability premises are the
explicit convergence inputs to the shared calculus, not an operator identity
or a remainder estimate (`app:ch_background:eq:bg-real-symbol`). -/
theorem SymbolInputs.unitReflectedEntry_diagonal_reduction
    (s : SymbolInputs c) (i j : Fin n)
    (hclosed : IsClosed (s.forward '' s.inputSupport))
    (hbuffer : s.forward '' s.inputSupport ⊆ s.domain)
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (f : Euclidean n → ℂ) (x : Euclidean n)
    (hβ : ContDiff ℝ ∞ β)
    (hβa : ∀ ξ y, s.unitReflectedEntry i j x y ξ ≠ 0 → β y = 1)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hi : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (s.unitReflectedEntry i j) f x))
    (hid : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalAmplitude (s.unitReflectedEntry i j) β) f x))
    (hir : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalRemainderAmplitude b (s.unitReflectedEntry i j) β) f x))
    (hiB : Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.fullTaylorCoefficient (s.unitReflectedEntry i j) β) f x)) :
    Pseudodifferential.fullAmplitudeOperator (s.unitReflectedEntry i j) f x =
      Pseudodifferential.fullAmplitudeOperator
        (fun x _y ξ ↦ s.unitReflectedEntry i j x x ξ) (fun y ↦ β y • f y) x +
      Pseudodifferential.fullAmplitudeOperator
        (Pseudodifferential.diagonalRemainderAmplitude b (s.unitReflectedEntry i j) β) f x := by
  rw [Pseudodifferential.fullAmplitudeOperator_eq_diagonal_add_remainder b
    (s.unitReflectedEntry i j) β f x (s.unitReflectedEntry_contDiff i j hclosed hbuffer)
      hβ hβa hf hfc hi hid hir hiB,
    Pseudodifferential.fullAmplitudeOperator_diagonalAmplitude]

/-- The actual diagonal term of the exact reduction is the reflected
homogeneous matrix at large physical frequency, including the full Fourier
normalization (`app:ch_background:eq:bg-real-symbol`). -/
theorem SymbolInputs.unitReflectedEntry_diagonal_eq_homogeneous
    (s : SymbolInputs c) (i j : Fin n)
    (hhigh : ∀ r : ℝ, 2 ≤ r → s.coefficients.high r = 1)
    {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ s.domain, ‖p.1.2.2‖ ≤ C * ‖(s.inverse p).2‖)
    (x ξ : Euclidean n) (hξ : 2 * C ≤ ‖(2 * Real.pi) • ξ‖) :
    s.unitReflectedEntry i j x x ξ =
      (reflectedDiagonalMatrix (TransportSymbol.homogeneousDiagonal s.coefficients
        s.jacobian s.inverse s.domain s.spectatorSupport x) ((2 * Real.pi) • ξ) i j : ℝ) := by
  unfold SymbolInputs.unitReflectedEntry
  rw [reflectedSymbolAmplitude_diagonal_eq_homogeneous s.coefficients s.jacobian s.inverse
    s.domain s.spectatorSupport hhigh hC hcomparison x _ hξ]

end JanetCartan.ContinuumRow.TransportKernel
