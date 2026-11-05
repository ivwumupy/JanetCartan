module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.FiniteCover
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.RetardedRadii

/-!
# Open margins for the retained retarded compact

The compact jet set includes its angular and time boundaries. Its open
smoothness domain therefore uses twice its radius. The original retained
radius has exactly this additional margin in the original chart. These
facts discharge the open-product and mixed-gap inputs of the separated
signed retarded constructor, on the same section and chart.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase FourierIntegral EvolutionIntegral
variable {d : ℕ}
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)

/-- The retained radius leaves room for the open neighborhood of the closed
jet compact required in `retarded-kernel`. -/
theorem four_mul_retainedRadius_le (b ρ : ℝ) : 4 * retainedRadius b ρ ≤ b := by
  dsimp [retainedRadius]
  linarith [min_le_left b ρ]

/-- Enlarge only the radial band, keeping the section and all physical
coordinates fixed (`fixed-time-representation`). -/
theorem retained_bufferedJetSet_mono_band (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z)
    (ε : ℝ) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    bufferedJetSet ℓ z ε a b ⊆ bufferedJetSet ℓ z ε a' b' := by
  rintro p ⟨hp, v, ⟨hv, hθ⟩, he⟩
  exact ⟨hp, v, ⟨⟨ha.trans hv.1, hv.2.trans hb⟩, hθ⟩, he⟩

/-- The actual closed compact has a strict margin inside the doubled open
phase product, including its angular boundary (`retarded-kernel`). -/
theorem retained_bufferedJetSet_subset_open_product
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε a b : ℝ}
    (hε : 0 < ε) (ha : 0 < a) :
    bufferedJetSet ℓ z ε a b ⊆ bufferedBase z (2 * ε) ×ˢ
      angularCone ℓ z.2.2 (2 * ε) := by
  intro p hp
  have hη := radialSectionBand_normalizes ha hp.2
  refine ⟨?_, hη.1, closedBall_subset_ball (by linarith) hη.2⟩
  have ht := hp.1
  change p.1 ∈ ball (z.1, (z.1, z.2.1)) (2 * (2 * ε))
  simp only [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨by have := ht.1; change dist p.1.1 z.1 ≤ 2 * ε at this; linarith,
    by have := ht.2.1; change dist p.1.2.1 z.1 ≤ 2 * ε at this; linarith,
    by have := ht.2.2; change dist p.1.2.2 z.2.1 ≤ 2 * ε at this; linarith⟩

/-- The original closed-buffer mixed estimate also holds on the doubled
open cone used around the jet compact. No new phase is selected
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem retained_mixed_half_gap_doubled (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : Z → ℝ} {Φ : Z × ℝ → Z} {C : OpenPartialHomeomorph T T}
    {z : Z} {b ε Δ : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b) (hΔ : Δ ≤ ε)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ p ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p)
    (hnear : ∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1 / 2) :
    ∀ r ∈ Icc 0 Δ, ∀ x ∈ elapsedPhysicalBox z ε,
      ∀ η ∈ angularCone ℓ z.2.2 (2 * ε),
        ‖mixedPhaseMatrix (curriedPhase ℓ C (x 0) (x 0 - r))
          (spatialPart x) η - 1‖ ≤ 1 / 2 := by
  have hsub : closedBall (z.1, z) (2 * (2 * ε)) ⊆ closedBall (z.1, z) b :=
    closedBall_subset_closedBall (by linarith)
  intro r hr x hx η hη
  exact norm_mixedPhaseMatrix_phase_sub_one_le ℓ (by positivity : 0 < 2 * ε)
    (hsub.trans hbuffer) hs hdiff (fun p hp ↦ hnear p (hsub hp))
    ⟨hr.1, by linarith [hr.2]⟩
    ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩ hη

end JanetCartan.RegularSector.Characteristic.UniformEvolution
