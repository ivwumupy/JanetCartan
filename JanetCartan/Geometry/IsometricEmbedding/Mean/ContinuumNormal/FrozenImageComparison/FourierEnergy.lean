module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.FourierEnergy.MultiplierActions
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.FourierEnergy.Reality
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Analysis.Microlocal.SingleChannel.TimeIntegration

/-!
# Fourier energy of the concrete frozen image normal

The squared adjoint norm of the literal real uncut channel equals the integrable
`fourierEnergy`, for `paper-v2.tex`, `app:ch_background:prop:bg-frame`.
The proved multiplier action, reality identity, and Plancherel theorem apply to
every real L² input, including in dimension zero. For integrable inputs and the
existing cell zero extensions, the transform also equals the ordinary Fourier
integral. The physical frequency remains `2πξ` and the pairing retains its real part.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 n E

/-- For real L¹ ∩ L² inputs, the L² transform of the actual complex inclusion
is represented by the ordinary Fourier integral of the pointwise inclusion
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem fourier_l2ComplexInclusion_ae_integral (u : R²)
    (hu : Integrable (u : E → E)) :
    (𝓕 (l2ComplexInclusion volume u) : C²) =ᵐ[volume]
      𝓕 (fun x ↦ euclideanComplexInclusion (u x)) := by
  have he := euclideanComplexInclusion.coeFn_compLpL u
  have hi : Integrable (l2ComplexInclusion volume u : E → EuclideanSpace ℂ (Fin n)) :=
    (euclideanComplexInclusion.integrable_comp hu).congr he.symm
  exact (JanetCartan.Localization.fourierTransform_coeFn_ae_integral_hilbert _ hi).trans
    (Filter.Eventually.of_forall (Real.fourier_congr_ae he))

/-- The specified energy is the integral of the squared adjoint-symbol norm
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
theorem fourierEnergy_eq_integral_adjointSymbol
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    fourierEnergy A u = ∫ ξ, ‖uncutChannelAdjointAction A ξ
      ((𝓕 (l2ComplexInclusion volume u) : C²) ξ)‖ ^ 2 := by
  simp only [fourierEnergy, re_inner_normalComplexAction_eq_norm_sq]

/-- The frozen image energy integrand is integrable for every real L² input:
the literal adjoint multiplier identifies it with the squared norm of an L²
Fourier transform (`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem integrable_fourierEnergy_integrand
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    Integrable (fun ξ ↦
      (inner ℂ ((𝓕 (l2ComplexInclusion volume u) : C²) ξ)
        (normalComplexAction A ((2 * Real.pi) • ξ)
          ((𝓕 (l2ComplexInclusion volume u) : C²) ξ))).re) := by
  have hi := (Lp.memLp (𝓕 ((uncutComplexChannel A).adjoint
    (l2ComplexInclusion volume u)) : C²)).integrable_norm_pow (by norm_num)
  apply hi.congr
  filter_upwards [fourier_uncutComplexChannel_adjoint_ae A
    (l2ComplexInclusion volume u)] with ξ hξ
  rw [re_inner_normalComplexAction_eq_norm_sq, hξ]

/-- Plancherel identifies the actual real frozen channel's squared adjoint norm
with its Fourier energy, for arbitrary real constant coefficients and every
real L² input. This supplies the uncut image term in the frozen normal comparison
(`app:ch_background:prop:bg-frame`), with no extra action or reality premise. -/
theorem norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    ‖(uncutRealChannel A).adjoint u‖ ^ 2 = fourierEnergy A u := by
  rw [fourierEnergy_eq_integral_adjointSymbol,
    ← norm_uncutComplexChannel_adjoint_complexInclusion A u,
    ← Lp.norm_fourier_eq,
    ← JanetCartan.SingleChannel.integral_norm_sq_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [fourier_uncutComplexChannel_adjoint_ae A
    (l2ComplexInclusion volume u)] with ξ hξ
  rw [hξ]

/-- Positivity of the frozen image energy
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
theorem fourierEnergy_nonneg
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    0 ≤ fourierEnergy A u := by
  rw [fourierEnergy_eq_integral_adjointSymbol]
  exact integral_nonneg fun _ ↦ sq_nonneg _

/-- The specified L² Fourier energy agrees with the ordinary Fourier integral
for every integrable real L² input. The normal is evaluated at physical
frequency `2πξ` and the complex pairing retains its real part
(`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem fourierEnergy_eq_fourierIntegral
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : Integrable (u : E → E)) :
    fourierEnergy A u = ∫ ξ,
      (inner ℂ (𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ)
        (normalComplexAction A ((2 * Real.pi) • ξ)
          (𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ))).re := by
  apply integral_congr_ae
  filter_upwards [fourier_l2ComplexInclusion_ae_integral u hu] with ξ hξ
  rw [hξ]

/-- For integrable real L² inputs, the ordinary Fourier-integral version of the
energy is integrable as well (`app:ch_background:prop:bg-frame`, Plancherel step).
In particular this applies to the existing zero extensions via
`integrable_zeroExtension`. -/
theorem integrable_fourierIntegral_energy
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : Integrable (u : E → E)) :
    Integrable (fun ξ ↦
      (inner ℂ (𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ)
        (normalComplexAction A ((2 * Real.pi) • ξ)
          (𝓕 (fun x ↦ euclideanComplexInclusion (u x)) ξ))).re) := by
  apply (integrable_fourierEnergy_integrand A u).congr
  filter_upwards [fourier_l2ComplexInclusion_ae_integral u hu] with ξ hξ
  rw [hξ]

/-- The actual cell zero extensions satisfy the ordinary Fourier-integral
formula by the proved `integrable_zeroExtension`, with no extra source
hypothesis (`app:ch_background:prop:bg-frame`, Plancherel step). -/
theorem fourierEnergy_zeroExtension_eq_fourierIntegral
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : OutputL2 n) :
    fourierEnergy A (toEuclidean (𝕜 := ℝ) f) = ∫ ξ,
      (inner ℂ (𝓕 (fun x ↦ euclideanComplexInclusion
          (toEuclidean (𝕜 := ℝ) f x)) ξ)
        (normalComplexAction A ((2 * Real.pi) • ξ)
          (𝓕 (fun x ↦ euclideanComplexInclusion
            (toEuclidean (𝕜 := ℝ) f x)) ξ))).re :=
  fourierEnergy_eq_fourierIntegral A _ (integrable_zeroExtension f)

end JanetCartan.ContinuumNormal.FrozenImageComparison
