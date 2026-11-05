module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.IncidenceCoordinates

/-!
# Smooth domain of the literal incidence pullbacks

A fixed open domain contains the prescribed joint ball by elementary coordinate
containments. Smoothness is derived from the original frame and the canonical
carrier, as required by `exists_cNorm_incidence_root_le_reserve_six`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ConstructedCarrierJets
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Fixed open domain in the literal `((x,k),t)` variables
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidenceDomain (z : Euclidean 3) : Set ((Euclidean n × Euclidean n) × ℝ) :=
  (fun p ↦ p.1.1) ⁻¹' U ∩ (incidenceCarrierMap z) ⁻¹'
    (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))

/-- The incidence domain is open independently of every current frame
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem isOpen_incidenceDomain (z : Euclidean 3) : IsOpen (T.incidenceDomain z) :=
  (hU.preimage (continuous_fst.fst)).inter
    ((isOpen_ball.prod (isOpen_parameterInterior _)).preimage
      (incidenceCarrierMap_smooth z).continuous)

/-- Containment of the fixed joint ball follows solely from the stipulated
physical and scalar-coordinate buffers (`app:ch_seed:prop:seed-actual-menu`). -/
theorem closedBall_subset_incidenceDomain
    {a : (Euclidean n × Euclidean n) × ℝ} {ρ : ℝ}
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)} (z : Euclidean 3)
    (hKxU : Kx ⊆ U) (hKx : Kx ⊆ ball (0 : Euclidean n) T.physicalRadius)
    (hKz : Kz ⊆ parameterInterior (2 * P.radius))
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz) :
    closedBall a ρ ⊆ T.incidenceDomain z := by
  intro p hp
  have hc := incidenceCarrierMap_mapsTo z hx hz hp
  exact ⟨hKxU hc.1, hKx hc.1, hKz hc.2⟩

/-- The three primitive incidence fields are smooth on the same fixed open
domain. This uses the original smooth frame and the actual selected gradient
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem incidence_fields_smooth {c C : ℝ} (hP : P.IsValid c C) (z : Euclidean 3)
    (Q : _) :
    ContDiffOn ℝ ∞ (fun p : (Euclidean n × Euclidean n) × ℝ ↦ Q.1 p.1.1)
        (T.incidenceDomain z) ∧
      ContDiffOn ℝ ∞ (fun p : (Euclidean n × Euclidean n) × ℝ ↦
        T.carrierGradient Q p.1.1 (incidenceParameter z p.2)) (T.incidenceDomain z) ∧
      ContDiffOn ℝ ∞ (fun p : (Euclidean n × Euclidean n) × ℝ ↦ p.1.2)
        (T.incidenceDomain z) := by
  refine ⟨Q.2.1.comp (contDiff_fst.fst.contDiffOn) (fun _ h ↦ h.1), ?_,
    contDiff_fst.snd.contDiffOn⟩
  change ContDiffOn ℝ ∞
    ((fun q : Euclidean n × Euclidean 3 ↦ T.carrierGradient Q q.1 q.2) ∘
      incidenceCarrierMap z) (T.incidenceDomain z)
  apply (T.carrierGradient_smooth hP Q).comp
    ((incidenceCarrierMap_smooth z).contDiffOn)
  exact fun _ h ↦ h.2

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
