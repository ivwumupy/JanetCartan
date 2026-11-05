module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WeakDerivatives.IntegralJets
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Cutoff raw fields and their literal integral jets

The measured field in `app:ch_waves:eq:individual-raw-slice` is the original
raw integral multiplied by the fixed physical cutoff. Its jets below integrate
the actual derivatives of that same cut demodulated atom. The cutoff is never
asserted to preserve Fourier support.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary

variable {X P F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [MeasurableSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Literal physical jets used for `app:ch_waves:eq:individual-raw-slice`:
the original Fourier density is integrated against derivatives of the cut atom.
This definition includes no derivative-interchange or weak-derivative premise. -/
def rawSliceIntegralJet (χ : X → ℝ) (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) (j : ℕ) (x : X) :
    X [×j]→L[ℝ] F :=
  ∫ η, f η • iteratedFDeriv ℝ j
    (fun y ↦ χ y • rawPrimaryDemodulatedAtom S A ζ τ (y, η)) x ∂μ

omit [NormedSpace ℝ X] in
/-- The measured field has support inside the fixed physical cutoff
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem hasCompactSupport_cut_rawPrimaryDemodulatedIntegral
    {χ : X → ℝ} (hχ : HasCompactSupport χ) (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) :
    HasCompactSupport (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ μ f x) :=
  hχ.smul_right

variable [FiniteDimensional ℝ X] [BorelSpace P] [CompleteSpace F]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [BorelSpace P] [CompleteSpace F] in
/-- Moving the physical cutoff inside the original integral changes neither
the density nor the measured field (`app:ch_waves:eq:individual-raw-slice`). -/
theorem cut_rawPrimaryDemodulatedIntegral_eq_compactIntegral
    (χ : X → ℝ) (S : X → P → ℝ) (A : X → P → F) (ζ : P) (τ : ℝ)
    {μ : Measure P} {f : P → ℂ} {T : Set P}
    (hfT : ∀ᵐ η ∂μ, η ∉ T → f η = 0) (x : X) :
    χ x • rawPrimaryDemodulatedIntegral S A ζ τ μ f x =
      ∫ η in T, f η • (χ x • rawPrimaryDemodulatedAtom S A ζ τ (x, η)) ∂μ := by
  rw [rawPrimaryDemodulatedIntegral_eq_compactSynthesis S A ζ τ hfT]
  unfold MeasureEnvelopes.synthesis
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  exact smul_comm _ _ _

omit [CompleteSpace F] in
/-- All physical derivatives of the measured field are the literal integrals
of the cut atom's derivatives (`app:ch_waves:eq:individual-raw-slice`).
Domination is proved locally from compactness, with no frequency-uniform bound. -/
theorem rawSliceIntegralJet_eq_iteratedFDeriv
    {U : Set X} {V T : Set P} (hU : IsOpen U) (hV : IsOpen V) (hT : IsCompact T)
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {χ : X → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    {ζ : P} {τ : ℝ} (hζ : ζ ∈ V) (hshift : ∀ η ∈ T, ζ + τ • η ∈ V)
    {μ : Measure P} [IsFiniteMeasure (μ.restrict T)] {f : P → ℂ}
    (hf : Integrable f μ) (hfT : ∀ᵐ η ∂μ, η ∉ T → f η = 0) (j : ℕ) :
    rawSliceIntegralJet χ S A ζ τ μ f j =
      iteratedFDeriv ℝ j (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ μ f x) := by
  let Ω : Set P := {η | ζ + τ • η ∈ V}
  have hΩ : IsOpen Ω := hV.preimage (by fun_prop)
  have hB : ContDiffOn ℝ ∞
      (fun p : X × P ↦ χ p.1 • rawPrimaryDemodulatedAtom S A ζ τ p) (U ×ˢ Ω) :=
    (hχ.comp contDiff_fst).contDiffOn.smul
      (contDiffOn_rawPrimaryDemodulatedAtom hS hA hζ (fun _ h ↦ h))
  have heq : (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ μ f x) =
      (fun x ↦ ∫ η in T, f η •
        (χ x • rawPrimaryDemodulatedAtom S A ζ τ (x, η)) ∂μ) :=
    funext (cut_rawPrimaryDemodulatedIntegral_eq_compactIntegral χ S A ζ τ hfT)
  funext x
  by_cases hx : x ∈ U
  · rw [heq, iteratedFDeriv_weightedCompactIntegral hU hΩ hT hshift hf.integrableOn hB j hx]
    unfold rawSliceIntegralJet
    exact (setIntegral_eq_integral_of_ae_compl_eq_zero
      (hfT.mono fun η hη hηT ↦ by rw [hη hηT, zero_smul])).symm
  · have hxχ : x ∉ tsupport χ := fun h ↦ hx (hχU h)
    have hz (g : X → F) : iteratedFDeriv ℝ j (fun y ↦ χ y • g y) x = 0 := by
      apply Function.notMem_support.mp
      exact fun h ↦ hxχ ((tsupport_smul_subset_left χ g) (support_iteratedFDeriv_subset j h))
    rw [hz]
    unfold rawSliceIntegralJet
    simp_rw [hz]
    simp

/-- The same measured field is globally smooth: the raw integral is smooth
on the buffered domain and the physical cutoff vanishes near its complement
(`app:ch_waves:thm:individual`). -/
theorem contDiff_cut_rawPrimaryDemodulatedIntegral
    {U : Set X} {V T : Set P} (hU : IsOpen U) (hV : IsOpen V) (hT : IsCompact T)
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {χ : X → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    {ζ : P} {τ : ℝ} (hζ : ζ ∈ V) (hshift : ∀ η ∈ T, ζ + τ • η ∈ V)
    {μ : Measure P} [IsFiniteMeasure (μ.restrict T)] {f : P → ℂ}
    (hf : Integrable f μ) (hfT : ∀ᵐ η ∂μ, η ∉ T → f η = 0) :
    ContDiff ℝ ∞ (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ μ f x) := by
  exact Localization.contDiff_of_contDiffOn_support_neighborhood hU
    (hχ.contDiffOn.smul
      (contDiffOn_rawPrimaryDemodulatedIntegral hU hV hT hS hA hζ hshift hf hfT))
    ((tsupport_smul_subset_left χ _).trans hχU)

end JanetCartan.RawPrimary
