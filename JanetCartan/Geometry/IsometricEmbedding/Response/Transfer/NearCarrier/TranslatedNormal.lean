module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Geometry

/-!
# The normal chart of the literal phase increment

The low estimate used in `app:ch_response:eq:direct-envelope-profile` uses
spatially averaged gradients, with both output positions retained. This file
transports that actual chart to the carrier increment. It does not identify it
with the covector-segment matrix used in derivative transfer. The inputs are
the original primitive chart and membership of the central covector; no normal
identity, inverse for the translated chart, or operator estimate is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace JanetCartan.ResponseTransfer

open NormalComparison FourierIntegral FourierIntegral.LowBounds

variable {n : ℕ}
local notation "E" => Euclidean n

/-- Covectors in the original chart after the literal carrier translation,
for `app:ch_response:eq:direct-envelope-profile`. -/
def translatedCovectorDomain (D : Set E) (ζ : E) (ρ : ℝ) : Set E :=
  (fun δ ↦ ρ • ζ + δ) ⁻¹' D

/-- The inverse of the spatially averaged normal map after carrier removal.
The central averaged gradient depends on both output positions. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def translatedNormalInverse (S : E → E → ℝ) (η : E → E → E → E)
    (ζ : E) (ρ : ℝ) (x y ξ : E) : E :=
  η x y (ξ + averagedGradient S x y (ρ • ζ)) - ρ • ζ

/-- The original normal Jacobian at the translated physical covector, used
in `app:ch_response:eq:direct-envelope-profile`. -/
def translatedNormalJacobian (J : E → E → E → E →L[ℝ] E)
    (ζ : E) (ρ : ℝ) (x y δ : E) : E →L[ℝ] E :=
  J x y (ρ • ζ + δ)

/-- Exact spatial normal map of the phase increment, from the two primitive
segment differentials. This is the map required by the low normal calculus in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem averagedGradient_phaseIncrement
    (S : E → E → ℝ) (ζ : E) (ρ : ℝ) (x y δ : E)
    (h₁ : ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ S z (ρ • ζ + δ)) (y + t • (x - y)))
    (h₀ : ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ S z (ρ • ζ)) (y + t • (x - y)))
    (hi₁ : IntervalIntegrable (fun t : ℝ ↦
      fderiv ℝ (fun z ↦ S z (ρ • ζ + δ)) (y + t • (x - y))) volume 0 1)
    (hi₀ : IntervalIntegrable (fun t : ℝ ↦
      fderiv ℝ (fun z ↦ S z (ρ • ζ)) (y + t • (x - y))) volume 0 1) :
    averagedGradient (phaseIncrement S ζ ρ) x y δ =
      averagedGradient S x y (ρ • ζ + δ) - averagedGradient S x y (ρ • ζ) := by
  unfold averagedGradient
  rw [← map_sub]
  congr 1
  unfold averagedPhaseDifferential
  rw [← intervalIntegral.integral_sub hi₁ hi₀]
  apply intervalIntegral.integral_congr
  intro t ht
  exact fderiv_sub (h₁ t (by simpa using ht)) (h₀ t (by simpa using ht))

/-- The translated chart has exactly the translated image, including every
point of the original chart image. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem mem_averagedGradient_phaseIncrement_image
    {S : E → E → ℝ} {X D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {g : ℝ}
    (G : AveragedGradientChart S X D η J g)
    (ζ : E) (ρ : ℝ) (hcentral : ρ • ζ ∈ D)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) (ξ : E) :
    ξ ∈ averagedGradient (phaseIncrement S ζ ρ) x y '' translatedCovectorDomain D ζ ρ ↔
      ξ + averagedGradient S x y (ρ • ζ) ∈ averagedGradient S x y '' D := by
  have he (δ : E) (hδ : δ ∈ translatedCovectorDomain D ζ ρ) :=
    averagedGradient_phaseIncrement S ζ ρ x y δ
      (G.segment x hx y hy _ hδ) (G.segment x hx y hy _ hcentral)
      (G.integrable x hx y hy _ hδ) (G.integrable x hx y hy _ hcentral)
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨ρ • ζ + δ, hδ, by rw [he δ hδ, sub_add_cancel]⟩
  · rintro ⟨u, hu, huξ⟩
    have hd : u - ρ • ζ ∈ translatedCovectorDomain D ζ ρ := by
      simpa [translatedCovectorDomain, add_sub_cancel_left] using hu
    refine ⟨u - ρ • ζ, hd, ?_⟩
    rw [he _ hd, show ρ • ζ + (u - ρ • ζ) = u by abel, huξ, add_sub_cancel_right]

/-- Transport of every primitive normal-chart field to the phase increment.
The determinant gap is unchanged and the actual inverse is constructed, not
postulated. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem averagedGradientChart_phaseIncrement
    {S : E → E → ℝ} {X D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {g : ℝ}
    (G : AveragedGradientChart S X D η J g)
    (ζ : E) (ρ : ℝ) (hcentral : ρ • ζ ∈ D) :
    AveragedGradientChart (phaseIncrement S ζ ρ) X (translatedCovectorDomain D ζ ρ)
      (translatedNormalInverse S η ζ ρ) (translatedNormalJacobian J ζ ρ) g := by
  have he (x : E) (hx : x ∈ X) (y : E) (hy : y ∈ X)
      (δ : E) (hδ : δ ∈ translatedCovectorDomain D ζ ρ) :=
    averagedGradient_phaseIncrement S ζ ρ x y δ
      (G.segment x hx y hy _ hδ) (G.segment x hx y hy _ hcentral)
      (G.integrable x hx y hy _ hδ) (G.integrable x hx y hy _ hcentral)
  refine ⟨G.measurable.preimage (measurable_const.add measurable_id), G.gap_pos,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy δ hδ t ht
    exact (G.segment x hx y hy _ hδ t ht).sub (G.segment x hx y hy _ hcentral t ht)
  · intro x hx y hy δ hδ
    apply ((G.integrable x hx y hy _ hδ).sub
      (G.integrable x hx y hy _ hcentral)).congr
    intro t ht
    exact (fderiv_sub (G.segment x hx y hy _ hδ t (uIoc_subset_uIcc ht))
      (G.segment x hx y hy _ hcentral t (uIoc_subset_uIcc ht))).symm
  · intro x hx y hy δ hδ
    have hd := ((G.derivative x hx y hy _ hδ).comp δ
      ((hasFDerivAt_id δ).const_add (ρ • ζ)).hasFDerivWithinAt
      (fun _ h ↦ h)).sub_const (averagedGradient S x y (ρ • ζ))
    convert hd.congr' (fun v hv ↦ he x hx y hy v hv) hδ using 1
    · simp [translatedNormalJacobian]
    · rfl
  · intro x hx y hy u hu v hv huv
    apply add_left_cancel (a := ρ • ζ)
    apply G.injective x hx y hy hu hv
    exact sub_left_inj.mp (by simpa only [he x hx y hy u hu, he x hx y hy v hv] using huv)
  · intro x hx y hy δ hδ
    simp only [translatedNormalInverse, he x hx y hy δ hδ, sub_add_cancel,
      G.leftInverse x hx y hy _ hδ, add_sub_cancel_left]
  · intro x hx y hy δ hδ
    exact G.gap x hx y hy _ hδ

/-- Coverage of the whole buffered normal domain after translation. In
particular a fixed target chart cannot be substituted for this domain when
checking the shell hypotheses of `LowBounds`. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem mem_bufferedNormalDomain_phaseIncrement
    {S : E → E → ℝ} {X D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {g : ℝ}
    (G : AveragedGradientChart S X D η J g)
    (ζ : E) (ρ : ℝ) (hcentral : ρ • ζ ∈ D) (q : NormalVariables n) :
    q ∈ bufferedNormalDomain X (translatedCovectorDomain D ζ ρ) (phaseIncrement S ζ ρ) ↔
      (q.1, q.2.1, q.2.2 + averagedGradient S q.1 q.2.1 (ρ • ζ)) ∈
        bufferedNormalDomain X D S := by
  change (q.1 ∈ X ∧ q.2.1 ∈ X ∧ _) ↔ (q.1 ∈ X ∧ q.2.1 ∈ X ∧ _)
  constructor
  · rintro ⟨hx, hy, hξ⟩
    exact ⟨hx, hy, (mem_averagedGradient_phaseIncrement_image G ζ ρ hcentral hx hy _).mp hξ⟩
  · rintro ⟨hx, hy, hξ⟩
    exact ⟨hx, hy, (mem_averagedGradient_phaseIncrement_image G ζ ρ hcentral hx hy _).mpr hξ⟩

end JanetCartan.ResponseTransfer
