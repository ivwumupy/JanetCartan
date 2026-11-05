module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.DatumSpatialDerivatives
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.DatumProfiles

/-!
# Constructed mixed datum profiles

For `app:ch_response:eq:direct-envelope-profile`, take spatial derivatives of
the actual pure parameter datum jets. Their Sobolev membership and quantitative
profiles follow from the pure parameter profiles, with a shared total order.
The spatial weak-derivative identities are proved here. Parameter
differentiation of these representatives is a separate analytic obligation.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d m : ℕ} {Y : Type*}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Parameter letters in a mixed datum word for
`app:ch_response:eq:direct-envelope-profile`, retaining their order. -/
def datumParameterWord (z : List (Fin m ⊕ Fin d)) : List (Fin m) :=
  z.filterMap Sum.getLeft?

/-- Spatial letters in a mixed datum word for
`app:ch_response:eq:direct-envelope-profile`, retaining their order. -/
def datumSpatialWord (z : List (Fin m ⊕ Fin d)) : List (Fin d) :=
  z.filterMap Sum.getRight?

/-- Both kinds of datum derivatives use one total budget in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem datumWord_lengths (z : List (Fin m ⊕ Fin d)) :
    (datumParameterWord z).length + (datumSpatialWord z).length = z.length := by
  induction z with
  | nil => rfl
  | cons i z ih =>
    cases i <;> simp_all [datumParameterWord, datumSpatialWord, List.filterMap_cons] <;> omega

/-- Concrete mixed datum representative for
`app:ch_response:eq:direct-envelope-profile`: spatial derivatives are applied
to the pure parameter jet. Parameter differentiation of this expression must
still be justified before asserting `HasMixedDatumJets`. -/
def mixedDatumJet (G : List (Fin m) → Y → L2) (z : List (Fin m ⊕ Fin d)) (t : Y) : L2 :=
  datumSpatialJet (datumSpatialWord z) (G (datumParameterWord z) t)

/-- The constructed datum family has the correct root in
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem mixedDatumJet_nil (G : List (Fin m) → Y → L2) (t : Y) :
    mixedDatumJet G [] t = G [] t := rfl

/-- Actual weak spatial differentiation of the constructed datum family in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem mixedDatumJet_hasSpatialDerivative (G : List (Fin m) → Y → L2)
    (z : List (Fin m ⊕ Fin d)) (t : Y) (i : Fin d)
    (hf : MemFourierSobolev ((1 + (datumSpatialWord z).length : ℕ) : ℝ)
      (G (datumParameterWord z) t)) :
    HasEuclideanL2CoordinateDerivative i (mixedDatumJet G z t)
      (mixedDatumJet G (.inr i :: z) t) := by
  simpa [mixedDatumJet, datumParameterWord, datumSpatialWord, List.filterMap_cons] using
    datumSpatialJet_hasDerivative i (datumSpatialWord z) (G (datumParameterWord z) t) hf

/-- The mixed datum profile is derived from pure parameter Sobolev profiles,
as required in `app:ch_response:eq:direct-envelope-profile`. The source uses
only total orders through `s+N`; the result uses `p+z.length`, preserving the
physical `2π` cost for each spatial letter. -/
theorem mixedDatumJet_mem_and_profile (s N : ℕ)
    (D : ℕ → List (Fin m) → ℝ) (G : List (Fin m) → Y → L2) (A₀ K : ℝ) (t : Y)
    (hG : ∀ p b, p + b.length ≤ s + N →
      MemFourierSobolev (p : ℝ) (G b t) ∧
        fourierSobolevNorm (p : ℝ) (G b t) ≤ A₀ * D p b * K ^ (p + b.length))
    (z : List (Fin m ⊕ Fin d)) (hz : z.length ≤ N) (p : ℕ) (hp : p ≤ s) :
    MemFourierSobolev (p : ℝ) (mixedDatumJet G z t) ∧
      fourierSobolevNorm (p : ℝ) (mixedDatumJet G z t) ≤
        A₀ * ((2 * Real.pi) ^ (datumSpatialWord z).length *
          D (p + (datumSpatialWord z).length) (datumParameterWord z)) * K ^ (p + z.length) := by
  have hlen := datumWord_lengths z
  obtain ⟨hm, hn⟩ := hG (p + (datumSpatialWord z).length) (datumParameterWord z) (by omega)
  obtain ⟨hout, hbound⟩ := datumSpatialJet_mem_and_norm p (datumSpatialWord z)
    (G (datumParameterWord z) t) hm
  refine ⟨hout, hbound.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ (2 * Real.pi) ^ (datumSpatialWord z).length by positivity)
  have horder : p + (datumSpatialWord z).length + (datumParameterWord z).length =
      p + z.length := by omega
  simpa only [horder, mul_assoc, mul_left_comm, mul_comm] using h

end JanetCartan.IsometricEmbedding.Response.NearCarrier
