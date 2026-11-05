module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.PhaseBudgets.JointBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.PhaseBudgets.Restriction

/-!
# Finite canonical slice phase and epsilon-jet budgets

This is the phase part of `UniformNormalData.input_jets` for the canonical raw
slice phase and zero reference amplitude. The constants are chosen before the
immersion from fixed domain data, metric/normal gaps and the primitive immersion
budget. Spatial order `k` and one epsilon derivative use full phase order
`k+2`, hence immersion order `k+5` by the sharp phase producer. No inverse
geometry or phase-jet hypothesis is imposed.

The parent construction supplies the actual inverse geometry and proves the
zero-amplitude fields. The fixed immersion budget is supplied by
`slicePhaseBudget_of_derivativeProfile`, within the original raw reserve.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts.ActualPhase ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

/-- Uniform finite phase budgets for the actual canonical raw slices, including
the ordinary epsilon derivative at zero and the upper endpoint. The SAME
projected stress and Hamilton phase are retained. Only the fixed immersion
budget at `20*((n-1)+1)+5` and the primitive projected-frame hypotheses are
used. This supplies the phase fields of `UniformNormalData.input_jets`
(`app:ch_seed:eq:seed-phase-tame`, `app:ch_seed:eq:seed-quotient-integral`,
`app:ch_waves:setup:oscillatory`). -/
theorem exists_canonicalSlicePhase_input_budgets (z : Euclidean 3)
    {a e b : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K (20 * ((n - 1) + 1) + 5) F ≤ M →
        (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ t ∈ Ioo (-a) a, ∀ ε ∈ Icc 0 e,
          ∀ w ∈ sliceSpatialDomain n a ×ˢ sliceInputDomain n,
          ∀ k ≤ 20 * ((n - 1) + 1),
            ‖iteratedFDeriv ℝ k (Function.uncurry (canonicalSlicePhase T Q z t ε)) w‖ +
              ‖deriv (fun ε' ↦ iteratedFDeriv ℝ k
                (Function.uncurry (canonicalSlicePhase T Q z t ε')) w) ε‖ ≤ C k := by
  obtain ⟨B, hB, hbound⟩ := exists_canonicalSlicePhase_joint_budgets
    T z ha ha' he heb hb hK hKU hball M hγ hκ
  refine ⟨fun k ↦ B k + B (k + 1), fun k ↦ add_pos (hB k) (hB (k + 1)), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow Q t ht ε hε w hw k hk
  have hq := sliceClosedCore_contains ht hε ⟨subset_closure hw.1, subset_closure hw.2⟩
  have hj := hbound F hF hi hrank hFM hmet hnormal hlow (ε, (t, w.1), w.2) hq
  exact (canonicalSlicePhase_inputJets_le_joint T Q z ha ha' he heb hb ht hε hw k).trans
    (add_le_add (hj k (by omega)) (hj (k + 1) (by omega)))

end JanetCartan.RawPrimary.SliceGeometry
