module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.SingleBand
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation

/-!
# Matching the original raw-frequency slices

The unit-annulus slice used by the common-kernel disintegration is identified
from the original raw half-derivative kernel via `RawInputDilation`, with its
precise Fourier scalar and Jacobian. This is the normalization preceding
`app:ch_waves:eq:sampling-prefix-normal`. The original normal is unchanged.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison RawInputRealization RawInputDilation

variable {n : ℕ} {K τ : ℝ}

/-- The compact unit-annulus slice is the actual input dilation of the raw
operator. All matching premises are original forward-kernel equalities;
the scalar is exactly `(K/(2π))^(n/2)` and both quadratures are retained
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem compactSliceOperator_eq_dilatedRaw
    (hn : 1 ≤ n) (hK : 0 < K) (hτ : τ ≠ 0)
    (S : Euclidean n → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1))
    (β : Euclidean (n - 1) → ℂ) (a : Euclidean n → Euclidean (n - 1) → Fin n → ℂ)
    (T : AnnularL2 n K →L[ℂ] NormalOutputL2 n n)
    (hT : ∀ (f : AnnularL2 n K) (i : Fin n), (T f) i =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        ∫ η, ((Real.sqrt ‖η‖ : ℂ) *
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) *
            f η) • a x η i ∂annularMeasure n K)
    (b : ℝ → Fin n → Euclidean n → Euclidean (n - 1) → ℂ)
    (hb : ∀ s i, Continuous (Function.uncurry (b s i)))
    {X : Set (Euclidean n)} {U : Set (Euclidean (n - 1))}
    (hX : IsCompact X) (hU : IsCompact U)
    (hs : ∀ s i x θ, (x, θ) ∉ X ×ˢ U → b s i x θ = 0)
    (s : ℝ)
    (hkernel : ∀ x θ i, θ ∈ annulus n 1 →
      b s i x θ = (normalOperatorScale n K : ℂ) * (Real.sqrt ‖θ‖ : ℂ) *
        oscillatoryFactor K (rawPrimaryPhaseDifference S ζ (τ * K) x θ) *
          β (K • θ) * a x (K • θ) i) :
    compactSliceOperator (annulus n 1) b hb hX hU hs s = dilatedOperator hK T ∧
      compactSliceOperator (annulus n 1) b hb hX hU hs s ∘L
        (compactSliceOperator (annulus n 1) b hb hX hU hs s).adjoint = T ∘L T.adjoint := by
  have he : compactSliceOperator (annulus n 1) b hb hX hU hs s = dilatedOperator hK T := by
    ext f i
    filter_upwards [compactVectorKernelOperator_ae_integral (annulus n 1) (hb s)
      (fun i ↦ HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs s i z.1 z.2 hz)) f i,
      dilatedRawPrimaryOperator_ae_integral hn hK hτ S ζ β a T hT f i] with x hx hy
    change (compactSliceOperator (annulus n 1) b hb hX hU hs s f) i x = _ at hx
    refine hx.trans (Eq.trans ?_ hy.symm)
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_annulus n 1)] with θ hθ
    rw [hkernel x θ i hθ]
    simp only [smul_eq_mul, Complex.real_smul]
    ring_nf
    rfl
  refine ⟨he, ?_⟩
  rw [he]
  exact normal_dilatedOperator hK T

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
