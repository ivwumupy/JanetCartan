module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FullLow.Literal

/-!
# Selected kernels, local phase extensions and the full reverse weight

Exact identifications consumed by the low realization and derivative leaves of
`app:ch_response:eq:direct-envelope-profile`. All statements concern the same
Lebesgue integrals, with their original physical normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierFullLow
open FourierIntegral FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Selection commutes with literal adjunction only after conjugating the
selector and exchanging both positions. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exchangedAdjointAmplitude_forwardSelectedAmplitude
    (A : FullAmplitude n r) (ζ : E) (ρ : ℝ) (q : E → ℂ) :
    exchangedAdjointAmplitude (forwardSelectedAmplitude A ζ ρ q) =
      forwardSelectedAmplitude (exchangedAdjointAmplitude A) ζ ρ
        (fun δ ↦ star (q δ)) := by
  funext x y δ
  simp [exchangedAdjointAmplitude, forwardSelectedAmplitude, selectedAmplitude]

/-- Smoothness of the exchanged full adjoint amplitude, for the actual reverse
low construction in `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_exchangedAdjointAmplitude (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (fun p : E × E × E ↦
      exchangedAdjointAmplitude A p.1 p.2.1 p.2.2) :=
  (starL ℝ : Matrix (Fin r) (Fin r) ℂ ≃L[ℝ] Matrix (Fin r) (Fin r) ℂ).contDiff.comp
    (hA.comp (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)))

/-- The reverse weighted selected amplitude is exactly the adjoint amplitude
of the exchanged, conjugate-transposed full weight. This keeps `j_S U⁻¹` and
all three physical/frequency cutoffs. It makes no identification with the
adjoint of the unweighted transport. Source:
`app:ch_regular_base:eq:actual-matrix-inverse` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exchangedAdjointAmplitude_selectedWeightedAmplitude
    (S : E → E → ℝ) (U : E → E → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : E → ℝ) (ζ : E) (ρ : ℝ) (q : E → ℂ) :
    exchangedAdjointAmplitude
      (forwardSelectedAmplitude
        (exchangedAdjointAmplitude (ReverseDerivative.literalAmplitude S U χs χt χg))
        ζ ρ (fun δ ↦ star (q δ))) =
      ReverseDerivative.selectedWeightedAmplitude S U χs χt χg ζ ρ q := by
  rw [exchangedAdjointAmplitude_forwardSelectedAmplitude,
    exchangedAdjointAmplitude_involutive]
  simp only [star_star]
  funext y x δ
  simp [forwardSelectedAmplitude, selectedAmplitude,
    ReverseDerivative.selectedWeightedAmplitude]

/-- A phase extension agreeing on the full supported carrier gives the SAME
literal forward graph, including both source and output masks. The equality
hypothesis is produced by `exists_nearCarrierPhaseExtension`. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem graphOperator_phaseIncrement_eq_of_supported_extension
    (S S' : E → E → ℝ) (ζ : E) (ρ : ℝ) (A : FullAmplitude n r)
    {X F : Set E} (hs : ∀ x y δ, x ∉ X ∨ δ ∉ F → A x y δ = 0)
    (he : ∀ x ∈ X, ∀ δ ∈ F,
      phaseIncrement S' ζ ρ x δ = phaseIncrement S ζ ρ x δ)
    (f : E → Fin r → ℂ) :
    graphOperator (phaseIncrement S' ζ ρ) A f =
      graphOperator (phaseIncrement S ζ ρ) A f := by
  funext x
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with δ
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hx : x ∈ X
  · by_cases hδ : δ ∈ F
    · simp only [graphOscillation, he x hx δ hδ]
    · simp [hs x y δ (Or.inr hδ)]
  · simp [hs x y δ (Or.inl hx)]

/-- The corresponding extension identity for the literal reverse integral;
the phase is evaluated at the source position. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem envelopeGraph_eq_of_supported_extension
    (S S' : E → E → ℝ) (ζ : E) (ρ : ℝ) (A : FullAmplitude n r)
    {X F : Set E} (hs : ∀ y x δ, x ∉ X ∨ δ ∉ F → A y x δ = 0)
    (he : ∀ x ∈ X, ∀ δ ∈ F,
      phaseIncrement S' ζ ρ x δ = phaseIncrement S ζ ρ x δ)
    (f : E → Fin r → ℂ) :
    ReverseDerivative.envelopeGraph S' ζ ρ A f =
      ReverseDerivative.envelopeGraph S ζ ρ A f := by
  funext y
  unfold ReverseDerivative.envelopeGraph
  congr 1
  apply integral_congr_ae
  filter_upwards [] with δ
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ X
  · by_cases hδ : δ ∈ F
    · simp only [ReverseDerivative.oscillation, he x hx δ hδ]
    · simp [hs y x δ (Or.inr hδ)]
  · simp [hs y x δ (Or.inl hx)]

/-- The selected forward identification requires phase compatibility only on
the actual output support. No hypothesis restricts the datum. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem demodulated_selected_graphOperator_of_support
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (ζ : E) (ρ : ℝ) (q : E → ℂ) {X : Set E}
    (hs : ∀ x y δ, x ∉ X → forwardSelectedAmplitude A ζ ρ q x y δ = 0)
    (hc : ∀ x ∈ X, S x (ρ • ζ) = ρ * φ x)
    (f : E → Fin r → ℂ) (x : E) :
    carrier (-ρ) φ x • graphOperator S (selectedAmplitude A ζ ρ q)
      (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • f y) x =
      graphOperator (phaseIncrement S ζ ρ) (forwardSelectedAmplitude A ζ ρ q) f x := by
  by_cases hx : x ∈ X
  · exact demodulated_selected_graphOperator S φ A ζ ρ q f x (hc x hx)
  · have hz (y η : E) : selectedAmplitude A ζ ρ q x y η = 0 := by
      simpa only [forwardSelectedAmplitude, show ρ • ζ + (η - ρ • ζ) = η by abel]
        using hs x y (η - ρ • ζ) hx
    simp [graphOperator, hz, hs x _ _ hx]

/-- The bounded test realization constructed below is the literal demodulated
selected graph on the original unprojected datum. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem realizes_demodulated_selected_forward
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (ζ : E) (ρ : ℝ) (q : E → ℂ) {X : Set E}
    (hs : ∀ x y δ, x ∉ X → forwardSelectedAmplitude A ζ ρ q x y δ = 0)
    (hc : ∀ x ∈ X, S x (ρ • ζ) = ρ * φ x)
    (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (phaseIncrement S ζ ρ) (forwardSelectedAmplitude A ζ ρ q) u)
    (u : graphTestSpace n r) :
    T (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (carrier (-ρ) φ x • graphOperator S (selectedAmplitude A ζ ρ q)
        (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • (u.val y).ofLp) x) := by
  filter_upwards [hT u] with x hx
  rw [demodulated_selected_graphOperator_of_support S φ A ζ ρ q hs hc]
  exact hx

/-- The adjoint of the realization of the exchanged full weighted amplitude
has the literal selected coordinate-inverse kernel. The low construction is
`exists_selectedFullGraphL2_of_primitive_inputs` applied to the exchanged
conjugate transpose, with the conjugated selector. Source:
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem realizes_selectedWeightedAmplitude_adjoint
    (S : E → E → ℝ) (U : E → E → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : E → ℝ) (ζ : E) (ρ : ℝ) (q : E → ℂ)
    (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace n r, T.adjoint (graphTestToLp u) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (exchangedAdjointAmplitude
          (forwardSelectedAmplitude
            (exchangedAdjointAmplitude (ReverseDerivative.literalAmplitude S U χs χt χg))
            ζ ρ (fun δ ↦ star (q δ)))) (fun x ↦ (u.val x).ofLp) y)) :
    ∀ u : graphTestSpace n r, T.adjoint (graphTestToLp u) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (ReverseDerivative.selectedWeightedAmplitude S U χs χt χg ζ ρ q)
        (fun x ↦ (u.val x).ofLp) y) := by
  simpa only [exchangedAdjointAmplitude_selectedWeightedAmplitude] using hT

end JanetCartan.ResponseTransfer.NearCarrierFullLow
