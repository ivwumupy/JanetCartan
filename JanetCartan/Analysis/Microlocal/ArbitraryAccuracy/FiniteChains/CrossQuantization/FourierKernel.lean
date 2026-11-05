module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets

/-!
# The Fourier kernel for the opposite localizer composition

The product needed between complete residual factors is `(1-Ro) Li`.
Its physical Fourier kernel uses both original symbols at a common base,
and at distinct frequencies. This is different from the physical kernel of
`(1-Lo) Ri`. The plateau gives a frequency gap in this representation.
Consumer: `finiteChain_observation_rapidDecayAt.hleak`, via the intermediate
cross-quantization estimate (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph
open ResidualLocalization.IdentityDefect
open FiniteChain.Retarded.KernelDecay

variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal physical Fourier kernel of `(1-Ro) Li`. The factor agrees
with `channelFourierTransform`; neither quantization is changed
(`app:ch_regular:eq:chain-tail`). -/
def crossQuantizationFourierKernel (ρ : ℝ) (mi mo : LocalizerSymbol n)
    (ξ η : E) : ℂ :=
  (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) * ∫ z,
    Complex.exp (Complex.I * (-(inner ℝ z (ξ - η)) : ℝ)) *
      (((1 - mo (z, ρ⁻¹ • ξ)) * mi (z, ρ⁻¹ • η) : ℝ) : ℂ)

/-- The complementary Fourier amplitude has an explicit gap from the
normalized frequency diagonal. The premise is exactly a fixed plateau
buffer on the full input support; it can hold uniformly over a family.
Consumer: integration by parts in the common base variable for
`app:ch_regular:eq:chain-tail`. -/
theorem crossQuantization_amplitude_eq_zero_of_buffer
    (mi mo : LocalizerSymbol n) (δ : ℝ)
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1)
    (z ξ η : E) (hgap : ‖ξ - η‖ ≤ δ) :
    (1 - mo (z, ξ)) * mi (z, η) = 0 := by
  by_cases hi : mi (z, η) = 0
  · simp [hi]
  have hd : dist (z, ξ) (z, η) = ‖ξ - η‖ := by
    simp [dist_eq_norm, Prod.norm_def]
  rw [hbuffer (z, η) (subset_tsupport mi hi) (z, ξ) (hd ▸ hgap)]
  simp

/-- Exact cancellation of the actual Fourier kernel for frequencies within
the given plateau buffer. No integration estimate is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationFourierKernel_eq_zero_of_buffer
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (δ : ℝ)
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1)
    (ξ η : E) (hgap : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ ≤ δ) :
    crossQuantizationFourierKernel ρ mi mo ξ η = 0 := by
  simp only [crossQuantizationFourierKernel,
    crossQuantization_amplitude_eq_zero_of_buffer mi mo δ hbuffer _ _ _ hgap,
    Complex.ofReal_zero, mul_zero, integral_zero]

/-- Every joint frequency derivative of the same kernel vanishes inside
the strict plateau buffer. This covers both frequency positions before
conjugate transposition, and is the cancellation input for the differentiated
forward and literal-adjoint estimates (`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationFourierKernel_jet_eq_zero_of_buffer
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (δ : ℝ)
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1)
    (ξ η : E) (hgap : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ < δ) (k : ℕ) :
    iteratedFDeriv ℝ k
      (fun p : E × E ↦ crossQuantizationFourierKernel ρ mi mo p.1 p.2) (ξ, η) = 0 := by
  have he : (fun p : E × E ↦ crossQuantizationFourierKernel ρ mi mo p.1 p.2)
      =ᶠ[𝓝 (ξ, η)] fun _ ↦ (0 : ℂ) := by
    have hc : Continuous (fun p : E × E ↦ ‖ρ⁻¹ • p.1 - ρ⁻¹ • p.2‖) :=
      ((continuous_fst.const_smul ρ⁻¹).sub (continuous_snd.const_smul ρ⁻¹)).norm
    filter_upwards [(isOpen_lt hc continuous_const).eventually_mem hgap] with p hp
    exact crossQuantizationFourierKernel_eq_zero_of_buffer ρ mi mo δ hbuffer p.1 p.2 hp.le
  simpa using (he.iteratedFDeriv ℝ k).eq_of_nhds

/-- The input frequency of the cross kernel stays in the original scaled
symbol carrier. This supplies the fixed annular weight in the Sobolev
estimate (`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationFourierKernel_zero_off_input
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (ξ η : E)
    (hη : ρ⁻¹ • η ∉ Prod.snd '' tsupport mi) :
    crossQuantizationFourierKernel ρ mi mo ξ η = 0 := by
  have hm z : mi (z, ρ⁻¹ • η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hη ⟨(z, ρ⁻¹ • η), h, rfl⟩)
  simp [crossQuantizationFourierKernel, hm]

/-- The exact Fourier transform in the common base variable, with its
physical `2π` conversion. This is the integration-by-parts input for the
cross estimate, not an identification of left and right operators
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationFourierKernel_eq_fourier
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (ξ η : E) :
    crossQuantizationFourierKernel ρ mi mo ξ η =
      (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) *
        𝓕 (fun z ↦ (((1 - mo (z, ρ⁻¹ • ξ)) * mi (z, ρ⁻¹ • η) : ℝ) : ℂ))
          ((2 * Real.pi)⁻¹ • (ξ - η)) := by
  rw [crossQuantizationFourierKernel, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp : -2 * Real.pi * inner ℝ z ((2 * Real.pi)⁻¹ • (ξ - η)) =
      -inner ℝ z (ξ - η) := by
    rw [inner_smul_right]
    field_simp
  simp only [hp, smul_eq_mul, mul_comm _ Complex.I]

/-- Joint smoothness follows from the compact base projection of the input
symbol. It is used to identify differentiated forward and adjoint kernels
in the cross estimate (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_crossQuantizationFourierKernel
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi)
    (his : HasCompactSupport mi) (ho : ContDiff ℝ ∞ mo) :
    ContDiff ℝ ∞ (fun p : E × E ↦ crossQuantizationFourierKernel ρ mi mo p.1 p.2) := by
  let F : (E × E) × E → ℂ := fun p ↦
    Complex.exp (Complex.I * (-(inner ℝ p.2 (p.1.1 - p.1.2)) : ℝ)) *
      (((1 - mo (p.2, ρ⁻¹ • p.1.1)) * mi (p.2, ρ⁻¹ • p.1.2) : ℝ) : ℂ)
  have hp : ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      -(inner ℝ p.2 (p.1.1 - p.1.2))) :=
    (contDiff_snd.inner ℝ (contDiff_fst.fst.sub contDiff_fst.snd)).neg
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp.mul
      (Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.sub (ho.comp
          (contDiff_snd.prodMk (contDiff_fst.fst.const_smul ρ⁻¹)))).mul
          (hi.comp (contDiff_snd.prodMk (contDiff_fst.snd.const_smul ρ⁻¹)))))
  have hs p z (hz : z ∉ Prod.fst '' tsupport mi) : F (p, z) = 0 := by
    have hm : mi (z, ρ⁻¹ • p.2) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hz ⟨_, h, rfl⟩)
    simp [F, hm]
  have hI : ContDiff ℝ ∞ (fun p ↦ ∫ z, F (p, z)) :=
    contDiff_integral_commonCarrier hF (his.image continuous_fst) hs
  exact contDiff_const.mul hI

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
