module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteIncidence.Cover

/-!
# The constructed finite incidence inputs for the frozen gap

The cover, conic geometry, minors, common tolerance and frame threshold are
constructed before the immersion. The SAME root family supplies the literal
root identities, positive weights and common-kernel detection required by
`exists_canonicalFrozenMatrixSymbol_unit_gap_of_incidence`. The final spectral
and Fourier assembly remains with that theorem's consumer
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open ProjectedStressFrame

/-- Construct all finite geometric inputs of the frozen spectral gap from the
original cover and primitive immersion hypotheses. Active patches are selected
using the normalized frequency in the NEW cover, and all roots come from ONE
family at the fixed tolerance. `RootAt` retains arbitrary allowed initial
multipliers; its unit specialization is exactly the root premise of `Gap`
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_finite_frozen_incidence_inputs {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b s : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hs : 0 < s) (hsradius : ∀ i, 3 * s < (T i).physicalRadius) (hsb : 3 * s < b)
    (M : ℝ) {κmet κnormal cap : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hcap : 0 < cap) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧
    ∃ c B ε δ cdet : ℝ, 0 < c ∧ 0 < B ∧ 0 < ε ∧ 0 < δ ∧ 0 < cdet ∧
    ∃ (m : ℕ) (chart : Fin m → Fin R.chartCount) (center : Fin m → Euclidean n)
      (ρ : Fin m → ℝ),
    ∃ d : (l : Fin m) → (a : Fin (D.patchCount (R.sourceChart (chart l)))) →
      FrozenIncidencePatchData (T ⟨R.sourceChart (chart l), a⟩)
        (D.roots (R.sourceChart (chart l)) a (center l))
        ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
          (center l)),
      (∀ l, center l ∈ sphere (0 : Euclidean n) 1) ∧
      (∀ l, 0 < ρ l) ∧
      (∀ l, ball (center l) (ρ l) ⊆ ball (R.center (chart l)) (R.radius (chart l))) ∧
      (sphere (0 : Euclidean n) 1 ⊆ ⋃ l, ball (center l) (ρ l)) ∧
      (∀ l a, 6 * (d l a).a < cap ∧ ε ≤ (d l a).rootTolerance) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm (closedBall (0 : Euclidean n) b) 4 F ≤ M →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v,
          κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∃ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R s c B ε (projectedStress F)
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g ∧
          (∀ l a, (d l a).Geometry ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩) ∧
          let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
          let T' := fun i : I ↦ T ⟨R.sourceChart (chart i.1), i.2⟩
          let G := fun i : I ↦ (d i.1 i.2).G
          ∃ (active : Euclidean n → Finset I) (z : Euclidean n → I → Euclidean 3),
            (∀ k i, i ∈ active k ↔ NormedSpace.normalize k ∈ ball (center i.1) (ρ i.1)) ∧
            (∀ k i, z k i =
              incidenceParameter (D.roots (R.sourceChart (chart i.1)) i.2 (R.center (chart i.1)))
                (g (chart i.1) i.2 (0, NormedSpace.normalize k))) ∧
            (∀ k, frozenFamilyHighFrequencyRadius T' G ≤ ‖k‖ → ∀ i ∈ active k,
              (d i.1 i.2).RootAt
                ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart i.1), i.2⟩⟩ F k (z k i)) ∧
            (∀ k, frozenFamilyHighFrequencyRadius T' G ≤ ‖k‖ → ∀ v : Euclidean n,
              imageChannel (pencil (projectedStress F 0) k) v = 0 →
              (∀ i ∈ active k, ⟪quadratic (projectedStress F 0)
                ((T' i).carrierGradient
                  ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart i.1), i.2⟩⟩ 0 (z k i)), v⟫_ℝ = 0) →
              v = 0) := by
  classical
  obtain ⟨R, hR, c, B, ε, δ, cdet, hc, hB, hε, hδ, hcdet, m, chart, center, ρ, d,
    hcenter, hρ, hchart, hcover, hcaproot, hconstruct⟩ :=
    exists_finite_frozen_incidence_cover hn hD T hBU hframe hs hsradius hsb
      M hκmet hκnormal hcap
  refine ⟨R, hR, c, B, ε, δ, cdet, hc, hB, hε, hδ, hcdet, m, chart, center, ρ, d,
    hcenter, hρ, hchart, hcover, hcaproot, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  obtain ⟨hlow, g, hg, hgeom, hroot, hdetect⟩ :=
    hconstruct F hF hi hrank hM hmet hnormal hclose
  refine ⟨hlow, g, hg, hgeom, ?_⟩
  let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
  let T' := fun i : I ↦ T ⟨R.sourceChart (chart i.1), i.2⟩
  let G := fun i : I ↦ (d i.1 i.2).G
  let active (k : Euclidean n) : Finset I :=
    Finset.univ.filter (fun i ↦ NormedSpace.normalize k ∈ ball (center i.1) (ρ i.1))
  let z (k : Euclidean n) (i : I) :=
    incidenceParameter (D.roots (R.sourceChart (chart i.1)) i.2 (R.center (chart i.1)))
      (g (chart i.1) i.2 (0, NormedSpace.normalize k))
  have hnorm {k : Euclidean n} (hk : frozenFamilyHighFrequencyRadius T' G ≤ ‖k‖) : 0 < ‖k‖ :=
    lt_of_lt_of_le zero_lt_one ((one_le_frozenFamilyHighFrequencyRadius T' G).trans hk)
  refine ⟨active, z, fun _ _ ↦ by simp only [active, Finset.mem_filter, Finset.mem_univ, true_and],
    fun _ _ ↦ rfl, ?_, ?_⟩
  · intro k hk i hi
    have hmem : NormedSpace.normalize k ∈ ball (center i.1) (ρ i.1) :=
      (Finset.mem_filter.mp hi).2
    have hh := hroot i.1 (NormedSpace.normalize k) hmem ‖k‖ (hnorm hk) i.2
      (by simpa only [NormedSpace.norm_smul_normalize] using
        (frozenHighFrequencyRadius_le_family T' G i).trans hk)
    simpa only [NormedSpace.norm_smul_normalize] using hh
  · intro k hk v himage hzero
    have hkn : k ≠ 0 := norm_pos_iff.mp (hnorm hk)
    have hunit : NormedSpace.normalize k ∈ sphere (0 : Euclidean n) 1 := by
      simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hkn
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcover hunit)
    have himage' : imageChannel (pencil (projectedStress F 0) (NormedSpace.normalize k)) v = 0 := by
      have hp : pencil (projectedStress F 0) (NormedSpace.normalize k) =
          ‖k‖⁻¹ • pencil (projectedStress F 0) k :=
        (pencilContinuousLinearMap (projectedStress F 0)).map_smul _ k
      have hh : imageChannel (pencil (projectedStress F 0) (NormedSpace.normalize k)) v =
          ‖k‖⁻¹ • imageChannel (pencil (projectedStress F 0) k) v := by
        ext i
        simp [ActualCarriers.imageChannel, hp, Matrix.smul_mulVec]
      rw [hh, himage, smul_zero]
    have hpatch (a : Fin (D.patchCount (R.sourceChart (chart l)))) :
        ⟪quadratic (projectedStress F 0)
          ((T ⟨R.sourceChart (chart l), a⟩).carrierGradient ⟨projectedStress F, hQ, hlow _⟩ 0
            (incidenceParameter (D.roots (R.sourceChart (chart l)) a (R.center (chart l)))
              (g (chart l) a (0, NormedSpace.normalize k)))), v⟫_ℝ = 0 :=
      hzero ⟨l, a⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
    have hb : cdet * ‖v‖ ^ 2 ≤ 0 := by
      simpa only [himage', norm_zero, zero_pow (by omega : 2 ≠ 0), hpatch,
        Finset.sum_const_zero, add_zero] using hdetect l (NormedSpace.normalize k) hl v
    have hv : ‖v‖ ^ 2 ≤ 0 := by
      by_contra! hh
      exact (not_lt_of_ge hb) (mul_pos hcdet hh)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

end JanetCartan.ContinuumNormal.FrozenModel
