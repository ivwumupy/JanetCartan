module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Frequency
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Output

/-!
# Compact-frequency literal reverse weak pairing

Source transfer and output integration by parts prove the reverse `hpair` in
`fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings`, with
`K = reverseGraphOperator S`, `R = adjointTransferRemainder S`, and
`P = adjointTransferDatum S`. The imported admissibility closure supplies `hR`
and `hP` from primitive phase smoothness and the actual mixed inverse gap.

Original coordinates remain `(x,y,η)`, with output `y` and source `x`.
Initialize `C x y η = (A x y η).conjTranspose`; no later branch is conjugated.
Physical masks, normalization, Lebesgue measure, and the complex Hilbert fiber
are preserved. The parent still supplies the distributional realization of every
branch, using the literal Hilbert adjoint at the initial reversed amplitude,
before applying the finite expansion. No limiting-operator recurrence is assumed.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Compact-frequency reverse weak pairing in the exact source test space and
complex Hilbert fiber of `fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings`.
All integrability obligations follow from smoothness and compact supports. The
phase is smooth only away from zero, and its homogeneity and actual mixed inverse
gap are required only on the common physical support. The already reversed `C`
retains every physical mask and is transferred without further conjugation.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_frequencyCut_weak_pairing
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hhom : ∀ p ∈ K, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    (∫ y, partialDeriv φ y i • WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) =
      -((∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferRemainder S i C))
            (fun x ↦ (u.val x).ofLp) y)) +
        ∑ j, ∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferDatum S i j C))
            (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) y)) := by
  have hR := reverseGraphOperator_frequencyCut_integrable_pairing
    (hC.adjointTransferRemainder S hS hinv i) hK hS hχ hχs hχ0 u φ
  have hP (j : Fin n) := reverseGraphOperator_frequencyCut_integrable_pairing
    (hC.adjointTransferDatum S hS hinv i j) hK hS hχ hχs hχ0
      (graphTestPartialDeriv j u) φ
  rw [reverseGraphOperator_frequencyCut_output_weak_pairing hC hK hS hχ hχs hχ0]
  simp_rw [hC.reverseGraphOperator_reverseFirstOutputAmplitude hK S hS hinv hhom
    χ hχ hχs hχ0 i _ u, WithLp.toLp_add, WithLp.toLp_sum, smul_add, Finset.smul_sum]
  rw [integral_add hR (integrable_finsetSum Finset.univ (fun j _ ↦ hP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hP j)]

end JanetCartan.FourierIntegral
