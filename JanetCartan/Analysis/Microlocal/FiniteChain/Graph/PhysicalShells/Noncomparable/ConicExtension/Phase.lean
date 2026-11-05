module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PhysicalTransfer

/-!
# Local agreement of physical phase extensions

The extension is used only to differentiate the literal kernel. All quantitative
bounds in `app:ch_regular:eq:chain-tail` will be transferred from the original
phase on its open conic domain, using equality on neighborhoods of the actual
amplitude support, rather than bounds on the extension away from that support.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
open FourierIntegral KernelEstimates KernelEstimates.Noncomparable
  KernelEstimates.NoncomparableGeometry
variable {n : ℕ}

/-- Physical normalization of a constructed smooth phase. This is an exact
rescaling, so it needs no global homogeneity hypothesis on the original conic
phase (`app:ch_regular:eq:joint-kernel-phase`). -/
def normalizedPhysicalPhase (ρ : ℝ) (Φ : Euclidean n → Euclidean n → ℝ)
    (u ξ : Euclidean n) : ℝ := ρ⁻¹ * Φ u (ρ • ξ)

/-- Exact physical rescaling used in the Fourier change of variables
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedPhysicalPhase_rescale {ρ : ℝ} (hρ : ρ ≠ 0)
    (Φ : Euclidean n → Euclidean n → ℝ) (u ξ : Euclidean n) :
    Φ u (ρ • ξ) = ρ * normalizedPhysicalPhase ρ Φ u ξ := by
  simp [normalizedPhysicalPhase, hρ]

/-- Normalization preserves global smoothness of the constructed extension
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_normalizedPhysicalPhase (ρ : ℝ)
    (Φ : Euclidean n → Euclidean n → ℝ)
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ContDiff ℝ ∞ (Function.uncurry (normalizedPhysicalPhase ρ Φ)) :=
  contDiff_const.mul (hΦ.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ)))

/-- The equality locus for germs of the original and extended phases is open.
Intersecting it with the primitive base domain preserves the entire amplitude
support (`app:ch_regular:eq:chain-tail`). -/
def phaseEqualityDomain (Φ S : Euclidean n → Euclidean n → ℝ) :
    Set (Euclidean n × Euclidean n) :=
  {p | Function.uncurry Φ =ᶠ[𝓝 p] Function.uncurry S}

/-- Openness needed for the support-local integration-by-parts domain
(`app:ch_regular:eq:chain-tail`). -/
theorem isOpen_phaseEqualityDomain (Φ S : Euclidean n → Euclidean n → ℝ) :
    IsOpen (phaseEqualityDomain Φ S) := isOpen_setOfPred_eventually_nhds

/-- Germ agreement transfers the actual physical base slice, including its
first derivative used in covector comparison (`app:ch_regular:eq:chain-tail`). -/
theorem phaseSlice_eventuallyEq {Φ S : Euclidean n → Euclidean n → ℝ}
    {u ξ : Euclidean n} (h : (u, ξ) ∈ phaseEqualityDomain Φ S) :
    (fun t => Φ t ξ) =ᶠ[𝓝 u] (fun t => S t ξ) :=
  h.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt

/-- The same germ agreement transfers every derivative of the literal frozen
base phase in both orientations, for arbitrary external bases
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem basePhase_eventuallyEq (backward : Bool)
    {Φ S : Euclidean n → Euclidean n → ℝ} (x y ξ η ζ : Euclidean n)
    (b : Euclidean n × Euclidean n)
    (h : (b.1, ξ) ∈ phaseEqualityDomain Φ S) :
    basePhase backward Φ x y ξ η ζ =ᶠ[𝓝 b] basePhase backward S x y ξ η ζ := by
  have he := h.comp_tendsto (continuous_fst.prodMk continuous_const).continuousAt
  filter_upwards [he] with z hz
  change Φ z.1 ξ = S z.1 ξ at hz
  cases backward <;> simp only [basePhase, jointPhase, Bool.false_eq_true, ↓reduceIte,
    forwardPhase, reversePhase] <;> rw [hz]

/-- Smoothness of the frozen physical base phase of a smooth extension
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_basePhase (backward : Bool)
    (Φ : Euclidean n → Euclidean n → ℝ)
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (x y ξ η ζ : Euclidean n) :
    ContDiff ℝ ∞ (basePhase backward Φ x y ξ η ζ) :=
  (contDiff_jointPhase_of_contDiff_phase backward Φ hΦ x y).comp
    (contDiff_id.prodMk contDiff_const)

/-- Normalized first and higher phase grades follow from the original physical
phase grades at any point of germ agreement. No norm of the extension away
from that locus is used. Consumer: the support-local pair bound for
`app:ch_regular:eq:chain-tail`. -/
theorem normalizedPhysicalPhase_grades (backward : Bool) (ρ : ℝ) {R G : ℝ}
    (hR : 0 < R) (hρ : ρ ≠ 0)
    (Φ S : Euclidean n → Euclidean n → ℝ)
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (b : Euclidean n × Euclidean n)
    (heq : (b.1, ρ • w.1) ∈ phaseEqualityDomain Φ S)
    (hfirst : ‖fderiv ℝ
      (basePhase backward S x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b‖ ≤ R * G) :
    ‖fderiv ℝ (normalizedBasePhase backward ρ R (normalizedPhysicalPhase ρ Φ) x y w) b‖ ≤ G ∧
    ∀ (d : ℕ) (H : ℝ),
      ‖iteratedFDeriv ℝ d
        (basePhase backward S x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) b‖ ≤ R * H →
      ‖iteratedFDeriv ℝ d
        (normalizedBasePhase backward ρ R (normalizedPhysicalPhase ρ Φ) x y w) b‖ ≤ H := by
  have he := basePhase_eventuallyEq backward x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2) b heq
  have hs := contDiff_basePhase backward Φ hΦ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)
  constructor
  · apply norm_fderiv_normalizedBasePhase_le backward ρ hR Φ _ x y w b
      (fun u => normalizedPhysicalPhase_rescale hρ Φ u w.1)
      (hs.differentiable (by simp)).differentiableAt
    rwa [he.fderiv_eq]
  · intro d H hd
    apply norm_iteratedFDeriv_normalizedBasePhase_le backward ρ hR Φ _ x y w b d
      (fun u => normalizedPhysicalPhase_rescale hρ Φ u w.1)
      (hs.of_le (by simp)).contDiffAt
    rwa [(he.iteratedFDeriv ℝ d).eq_of_nhds]

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
