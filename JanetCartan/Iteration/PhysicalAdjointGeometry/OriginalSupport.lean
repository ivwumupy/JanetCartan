module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.PhysicalJets
public import JanetCartan.Iteration.PhysicalAdjointGeometry.FrequencyCaps
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains

/-!
# The original carrier support supplies the common trade compact

No carrier labels or physical cutoffs are reselected. The compact contains the
entire original carrier cube of radius `3 P.radius / 2` and the original given
physical source radius. The retained initial covector-buffer theorem supplies
one positive displacement width before every current map and frequency.

This closes the support premise of the actual joint inverse construction;
the original wide-input ceiling is admitted by the fine-band threshold.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalAdjointGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawPrimary.SliceGeometry RawPrimary.SliceBounds

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The original closed physical source, whole original carrier cube, and one
fixed displacement ball. Nothing here depends on a current immersion. -/
def originalTradeCompact (ρ ε : ℝ) : Set (Point (Spacetime (n - 1)) (n - 1)) :=
  closedBall 0 ρ ×ˢ
    ((T.reference.spatialPatch '' parameterCube (3 * P.radius / 2)) ×ˢ closedBall 0 ε)

/-- A common original-support compact inside the actual inverse domain.
The whole retained carrier cube remains; the only chosen quantity is a new
positive allowable Fourier displacement, not a new physical/carrier cutoff
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_original_joint_trade_support {c C ρ : ℝ} (hP : P.IsValid c C)
    (hρ : ρ < T.family.radius) :
    ∃ ε > (0 : ℝ), IsCompact (originalTradeCompact T ρ ε) ∧
      originalTradeCompact T ρ ε ⊆
        shiftDomain (covectorCenter T) T.family.radius := by
  let Z := parameterCube (3 * P.radius / 2)
  have hZi : Z ⊆ parameterInterior (2 * P.radius) := by
    intro z hz i
    exact (hz i).trans_lt (by linarith [hP.1])
  have hZc : Z ⊆ parameterCube (2 * P.radius) := fun z hz i ↦ (hZi hz i).le
  have hsp := (T.reference.spatialPatch_smooth hP).continuousOn.mono hZi
  have hc : ContinuousOn (fun z ↦ dist (T.reference.spatialPatch z) (covectorCenter T)) Z := by
    change ContinuousOn (fun z ↦ ‖T.reference.spatialPatch z - covectorCenter T‖) Z
    exact (hsp.sub continuousOn_const).norm
  have hZ : IsCompact Z := isCompact_parameterCube _
  obtain ⟨z₀, hz₀, hmax⟩ := hZ.exists_isMaxOn
    ⟨0, zero_mem_parameterCube (by linarith [hP.1])⟩ hc
  let d := dist (T.reference.spatialPatch z₀) (covectorCenter T)
  have hd : d < T.family.radius :=
    (mem_ball.mp (spatialPatch_mem_initial_covector_ball T (hZc hz₀))).trans_le (min_le_left _ _)
  let ε := (T.family.radius - d) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨ε, hε, (isCompact_closedBall _ _).prod ((hZ.image_of_continuousOn hsp).prod
    (isCompact_closedBall _ _)), ?_⟩
  rintro ⟨x, ζ, δ⟩ ⟨hx, ⟨⟨z, hz, rfl⟩, hδ⟩⟩
  have hx' : ‖x‖ ≤ ρ := by simpa using hx
  have hδ' : ‖δ‖ ≤ ε := by simpa using hδ
  have hz' : dist (T.reference.spatialPatch z) (covectorCenter T) ≤ d := hmax hz
  refine ⟨hx'.trans_lt hρ, ?_⟩
  change dist (T.reference.spatialPatch z) (covectorCenter T) + ‖δ‖ < T.family.radius
  dsimp only [ε] at hδ'
  linarith

/-- The actual original-support joint family, with primitive frame tolerance
and displacement width both chosen before current maps. This producer has no
inverse, smooth-extension, phase-identity, or support-containment success
hypothesis (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_original_joint_trade_family {c C ρ : ℝ} (hP : P.IsValid c C)
    (hρ : ρ < T.family.radius) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      (originalTradeCompact T ρ ε ⊆ shiftDomain (covectorCenter T) T.family.radius) ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ∃ Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1),
        ∃ L : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1) →L[ℝ] Spacetime (n - 1),
          ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ L ∧
          (∀ q ∈ originalTradeCompact T ρ ε, Y =ᶠ[𝓝 q] averagedCovector (current T Q)) ∧
          (∀ q ∈ originalTradeCompact T ρ ε,
            L =ᶠ[𝓝 q] tradeDirection transverseInsertion (averagedCovector (current T Q))) ∧
          ∀ q : Point (Euclidean n) (n - 1),
            jointCoordinateEquiv (adaptedSpacetimeEquiv T.data.adapted).symm q ∈
                originalTradeCompact T ρ ε →
            ∀ h η : Euclidean (n - 1),
              fderiv ℝ (fun x ↦ inner ℝ
                (physicalCovector (adaptedSpacetimeEquiv T.data.adapted) Y (x, q.2)) η) q.1
                (physicalTrade (adaptedSpacetimeEquiv T.data.adapted) L q h) = inner ℝ h η := by
  obtain ⟨ε, hε, hK, hKV⟩ := exists_original_joint_trade_support T hP hρ
  obtain ⟨δ, hδ, hfamily⟩ := exists_current_joint_trade_extension T
  refine ⟨ε, hε, δ, hδ, hKV, ?_⟩
  intro Q hQ
  obtain ⟨Y, L, hY, hL, heY, heL, hid⟩ := hfamily Q hQ _ hK hKV
  refine ⟨Y, L, hY, hL, heY, heL, ?_⟩
  intro q hq h η
  exact fderiv_phase_physicalTrade (adaptedSpacetimeEquiv T.data.adapted) hY L q h η
    (hid _ hq h η)

/-- One pre-history threshold admits every literal wide-band source point to
that very same fixed compact, including its full dyadic ceiling. The density
support theorem then covers the unchanged original Fourier integral
(`app:ch_waves:eq:individual-representation`). -/
theorem exists_originalWideInput_compact_threshold {ρ ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S, ∀ stage : ℕ,
      let R := historyScale R₀ growthExponent stage
      ∀ radial : ℝ, 1 ≤ radial →
      ∀ (x : Euclidean n), ‖x‖ ≤ ρ → ∀ z ∈ parameterCube (3 * P.radius / 2),
      ∀ η ∈ closedBall (0 : Euclidean (n - 1))
          ((2 : ℝ) ^ RawInputPartition.cutoffCount (R ^ fineExponent)),
        ((adaptedSpacetimeEquiv T.data.adapted).symm x, T.reference.spatialPatch z,
          (radial * R ^ carrierExponent)⁻¹ • η) ∈ originalTradeCompact T ρ ε := by
  obtain ⟨S, hS, hshift⟩ := InitialSourceLocalization.exists_originalScale_source_shift_threshold hε 4
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ stage R radial hradial x hx z hz η hη
  have hR₀one : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR₀)
  have hR : 1 ≤ R := hR₀one.trans (le_historyScale hR₀one stage)
  have hK : 1 ≤ R ^ fineExponent := Real.one_le_rpow hR (by norm_num [fineExponent, meanSlack])
  have hηnorm : ‖η‖ ≤ (2 : ℝ) ^ RawInputPartition.cutoffCount (R ^ fineExponent) := by
    simpa using hη
  have hb := hshift R₀ hR₀ stage radial hradial
    ((2 : ℝ) ^ RawInputPartition.cutoffCount (R ^ fineExponent))
    (by positivity) (RawInputPartition.cutoffCount_ceiling hK)
  refine ⟨by simpa using hx, ⟨⟨z, hz, rfl⟩, ?_⟩⟩
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hηnorm (abs_nonneg _)).trans hb

end JanetCartan.PhysicalAdjointGeometry
