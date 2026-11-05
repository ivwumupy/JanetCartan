module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.MixedEvaluations

/-!
# Lebesgue L² norms of the retarded mixed jets

The norm comparison for `app:ch_response:eq:fixed-factor-transfer` uses the
literal product measure of `app:ch_osc:prop:osc-retarded-tube`. The coordinate
change and the time/transverse swap both preserve this measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- The coordinates in the argument order of `Spaces.jet` preserve Lebesgue
measure (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem measurePreserving_retardedJetCoordinates (d : ℕ) :
    MeasurePreserving (Prod.swap ∘ retardedCoordinates d) :=
  Measure.measurePreserving_swap.comp (measurePreserving_retardedCoordinates d)

/-- Exact L² transport for each ordered mixed jet
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem eLpNorm_retardedJet_comp_coordinates {d s : ℕ} (f : Test d) (i : JetIndex d s) :
    eLpNorm (jet i f ∘ (Prod.swap ∘ retardedCoordinates d)) 2 volume =
      eLpNorm (jet i f) 2 volume :=
  eLpNorm_comp_measurePreserving (jet_memLp volume i f).aestronglyMeasurable
    (measurePreserving_retardedJetCoordinates d)

/-- Every transported mixed jet is L², including all zero-dimensional transverse
cases (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem memLp_retardedJet_comp_coordinates {d s : ℕ} (f : Test d) (i : JetIndex d s) :
    MemLp (jet i f ∘ (Prod.swap ∘ retardedCoordinates d)) 2 volume :=
  (jet_memLp volume i f).comp_measurePreserving (measurePreserving_retardedJetCoordinates d)

/-- Each genuine mixed jet is bounded by the completed finite-product norm,
with all ordered multiplicities retained (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem retardedJet_l2Norm_le_ofTest {d s : ℕ} (f : Test d) (i : JetIndex d s) :
    (eLpNorm (jet i f ∘ (Prod.swap ∘ retardedCoordinates d)) 2 volume).toReal ≤
      ‖ofTest s volume f‖ := by
  rw [eLpNorm_retardedJet_comp_coordinates, ← Lp.norm_toLp _ (jet_memLp volume i f)]
  exact norm_le_pi_norm (jetMap s volume f) i

/-- Bounding the completed norm is exactly bounding every transported mixed
L² jet; no enumeration or multiplicity factor is lost
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem ofTest_norm_le_iff_retardedJet_l2Norm_le {d s : ℕ} (f : Test d)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖ofTest s volume f‖ ≤ C ↔ ∀ i : JetIndex d s,
      (eLpNorm (jet i f ∘ (Prod.swap ∘ retardedCoordinates d)) 2 volume).toReal ≤ C := by
  change ‖jetMap s volume f‖ ≤ C ↔ _
  rw [pi_norm_le_iff_of_nonneg hC]
  apply forall_congr'
  intro i
  rw [eLpNorm_retardedJet_comp_coordinates]
  change ‖(jet_memLp volume i f).toLp (jet i f)‖ ≤ C ↔ _
  rw [Lp.norm_toLp]

end JanetCartan.ResponseTransfer
