module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.DensityAdjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.DirectSum

/-!
# Uniform finite local adjoints and their full initial-variable norm

Apply the actual local construction to a prescribed finite incidence list on
one compact immersion domain, then choose one frame threshold and sum the
constants before the varying immersion and original densities. The carrier
Hilbert norm contains every carrier and initial derivative. All density outputs
use the same constructed operators and their fixed footpoint cutoffs.

This closes the finite summation in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` for this constructed local family.
The final source row still requires common measurement restriction, its image
and exterior summands, and matching to the same initialized leading family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DensityMultiplier PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Finite summation preserves one additive high scalar budget
(`app:ch_background:prop:bg-adjoint`). Also used for the retained row. -/
theorem sum_single_high_bound (f C a : ι → ℝ) (p q g : ℝ)
    (hC : ∀ i, 0 ≤ C i) (ha : ∀ i, 0 ≤ a i) (hq : 0 ≤ q)
    (hf : ∀ i, f i ≤ C i * (p + (1 + g + a i) * q)) :
    ∑ i, f i ≤ (∑ i, C i) * (p + (1 + g + ∑ i, a i) * q) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply (hf i).trans
  apply mul_le_mul_of_nonneg_left _ (hC i)
  gcongr
  exact Finset.single_le_sum (fun j _ ↦ ha j) (Finset.mem_univ i)

/-- The full carrier Hilbert norm is bounded by the sum of its component norms
(`app:ch_background:prop:bg-adjoint`). Also used for the retained row. -/
theorem carrierFamily_norm_le_sum (s : ℕ) (u : CarrierFamilySobolevSpace n ι s) :
    ‖u‖ ≤ ∑ i, ‖u i‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg u) (Finset.sum_nonneg fun i _ ↦ norm_nonneg (u i))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ i, ‖u i‖ * (∑ j, ‖u j‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ ↦ norm_nonneg (u j)) (Finset.mem_univ i))
        (norm_nonneg (u i))
    _ = _ := by rw [← Finset.sum_mul, pow_two]

/-- Construct the finite local family and its uniform real-adjoint and density
bounds from primitive geometry and the original positive-density class. The
same immersion norm and the sum of original initial-scalar norms occur once.
No per-channel estimate is assumed; all are instantiated from the actual
canonical construction. Constants precede the immersion, densities and datum
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_finite_projected_densityAdjoints (hn : 2 ≤ n)
    (P : ι → Patch n) {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {O : Set (Euclidean n)} {hO : IsOpen O}
    (T : (i : ι) → PatchQuantitativeFamily (P i) O hO)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKO : K ⊆ O)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    (z : ι → Euclidean 3) (hz : ∀ i, z i ∈ parameterInterior (P i).radius)
    (k : ι → Euclidean n) (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i) ((P i).toFun w)) (z i)
      (EuclideanSpace.single 0 1) ≠ 0)
    {M κmet κ σ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ row col : ι → Fin n, ∃ R a b : ι → ℝ,
      (∀ i, 0 < R i) ∧ ∃ ha : ∀ i, 0 < a i,
      ∃ hcell : ∀ i, 4*a i < 1/2, ∃ hb : ∀ i, 0 < b i,
      ∃ δ > (0 : ℝ), ∃ χy : ι → ContDiffBump (0 : CarrierVariable n),
      ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F O)
        (hi : IsImmersionOn F O) (hrank : HasFullNormalRankOn F O),
        cNorm K (2*(n+1)+13) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        let Q := fun i ↦ ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hO hF hi hrank), hlow i⟩
        (∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
          (p.2, CanonicalCarrier.transportPosition (T i) (Q i) p))
          (supportedChart (z i) (a i)) (interior {q | χy i q = 1})) ∧
        ∃ Φ Y : ι → ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3,
          ∀ v₀ : ι → Euclidean (n-1) × Euclidean 3 → ℝ,
            (∀ i, ContDiffOn ℝ ∞ (v₀ i) (ball ((0 : Euclidean (n-1)), z i) (R i/4))) →
            (∀ i, ∀ p ∈ ball ((0 : Euclidean (n-1)), z i) (R i/4), 0 < 1 + v₀ i p) →
            (∀ i, ∀ p ∈ closedBall ((0 : Euclidean (n-1)), z i) (R i/8),
              1 + v₀ i p ∈ Icc (1/2 : ℝ) (3/2)) →
            (∀ i, cNorm (closedBall ((0 : Euclidean (n-1)), z i) (R i/8)) (2*(n+1)) (v₀ i) ≤ 1) →
            let initial := fun i p ↦ positiveDensityAmplitude σ (v₀ i p)
            let ηb := fun i ↦ (T i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
            let d := fun i ↦ CanonicalCarrier.data (T i) (Q i) F (row i) (col i) (Φ i) (Y i)
              (initial i) (ha i) (hcell i)
              (CanonicalConic.angularMask (z i) (NormedSpace.normalize (ηb i)) (ha i) (hb i))
              FixedCutoffs.highFrequency
            let H := fun m ↦ 1 + cNorm K m F +
              ∑ i, cNorm (closedBall ((0 : Euclidean (n-1)), z i) (R i/8)) m (initial i)
            ∃ U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
              (∀ i w, (U i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
              (∀ i, ∀ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ w, V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) → V = U i) ∧
              ∃ hraw : ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) s, ∀ i,
                MemRawSobolev s ((carrierChannel (U i)).adjoint (PeriodicSobolevSpace.toL2 s v)),
              (∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
                ∃ u : CarrierFamilySobolevSpace n ι s,
                  carrierFamilyToL2 s u = (carrierRow U).adjoint (PeriodicSobolevSpace.toL2 s v) ∧
                  ‖u‖ ≤ Cbound s * (‖v‖ + H (s+2*(n+1)+13) * ‖PeriodicSobolevSpace.toL2 s v‖)) ∧
              ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) (s+1),
                let f := fun i ↦ (carrierChannel (U i)).adjoint (PeriodicSobolevSpace.toL2 (s+1) v)
                let hf := fun i ↦ (hraw (s+1) v i).mono (by omega : 1 ≤ s+1)
                (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
                    (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha i) (hb i) (f i) (hf i))) ∧
                  MemPhysicalSobolev s (physicalComplexifyL2
                    (density (z i) (NormedSpace.normalize (ηb i)) (ha i) (hb i) (χy i) (f i) (hf i)))) ∧
                (∑ i, physicalSobolevNorm s (physicalComplexifyL2
                  (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha i) (hb i) (f i) (hf i)))) ≤
                    Lbound s * (‖v‖ + H (s+2*(n+1)+14) * ‖PeriodicSobolevSpace.toL2 (s+1) v‖) ∧
                (∑ i, physicalSobolevNorm s (physicalComplexifyL2
                  (density (z i) (NormedSpace.normalize (ηb i)) (ha i) (hb i) (χy i) (f i) (hf i)))) ≤
                    Lbound s * (‖v‖ + H (s+2*(n+1)+14) * ‖PeriodicSobolevSpace.toL2 (s+1) v‖) := by
  classical
  choose row col R a b δ hR ha hcell hb hδ χy Cbound Lbound hCbound hLbound hlocal using
    fun i ↦ exists_projected_uniform_densityAdjoint (T i) (N := N) hn (hP i) (hz i)
      (hk i) (hinc i) (hd i) hK hKO (hball i) hM hκmet hκ hσ
  obtain ⟨δ₀, hδ₀, hδi⟩ := Pi.exists_forall_pos_add_lt hδ
  refine ⟨row, col, R, a, b, hR, ha, hcell, hb, δ₀, hδ₀, χy,
    (fun s ↦ ∑ i, Cbound i s), (fun s ↦ ∑ i, Lbound i s),
    (fun s ↦ Finset.sum_nonneg fun i _ ↦ hCbound i s),
    (fun s ↦ Finset.sum_nonneg fun i _ ↦ hLbound i s), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  choose hlow hplateau Φ Y hscalar using fun i ↦
    hlocal i F hF hi hrank hFM hmet hnormal (hclose.trans (by simpa using hδi i))
  refine ⟨hlow, hplateau, Φ, Y, ?_⟩
  intro v₀ hv₀ hpos hinterval hvlow
  choose U hrep hunique hraw hrawBound hdensity using
    fun i ↦ hscalar i (v₀ i) (hv₀ i) (hpos i) (hinterval i) (hvlow i)
  refine ⟨U, hrep, hunique, (fun s v i ↦ hraw i s v), ?_, ?_⟩
  · intro s v
    let u : CarrierFamilySobolevSpace n ι s := WithLp.toLp 2
      (fun i ↦ RawSobolevSpace.ofRawL2 s
        ((carrierChannel (U i)).adjoint (PeriodicSobolevSpace.toL2 s v)) (hraw i s v))
    refine ⟨u, ?_, ?_⟩
    · rw [carrierRow_adjoint_apply]
      apply PiLp.ext
      intro i
      exact RawSobolevSpace.toRawL2_ofRawL2 s _ (hraw i s v)
    · apply (carrierFamily_norm_le_sum s u).trans
      have he (i : ι) : ‖u i‖ = rawSobolevNorm s
          ((carrierChannel (U i)).adjoint (PeriodicSobolevSpace.toL2 s v)) := by
        rw [RawSobolevSpace.norm_eq, RawSobolevSpace.toRawL2_ofRawL2]
      simp_rw [he]
      exact sum_single_high_bound _ (fun i ↦ Cbound i s)
        (fun i ↦ cNorm (closedBall ((0 : Euclidean (n-1)), z i) (R i/8))
          (s+2*(n+1)+13) (fun p ↦ positiveDensityAmplitude σ (v₀ i p)))
        ‖v‖ ‖PeriodicSobolevSpace.toL2 s v‖ (cNorm K (s+2*(n+1)+13) F)
        (fun i ↦ hCbound i s) (fun _ ↦ cNorm_nonneg ..) (norm_nonneg _)
        (fun i ↦ hrawBound i s v)
  · intro s v
    refine ⟨fun i ↦ ⟨(hdensity i s v).1, (hdensity i s v).2.1⟩, ?_, ?_⟩
    · exact sum_single_high_bound _ (fun i ↦ Lbound i s)
        (fun i ↦ cNorm (closedBall ((0 : Euclidean (n-1)), z i) (R i/8))
          (s+2*(n+1)+14) (fun p ↦ positiveDensityAmplitude σ (v₀ i p)))
        ‖v‖ ‖PeriodicSobolevSpace.toL2 (s+1) v‖ (cNorm K (s+2*(n+1)+14) F)
        (fun i ↦ hLbound i s) (fun _ ↦ cNorm_nonneg ..) (norm_nonneg _)
        (fun i ↦ (hdensity i s v).2.2.1)
    · exact sum_single_high_bound _ (fun i ↦ Lbound i s)
        (fun i ↦ cNorm (closedBall ((0 : Euclidean (n-1)), z i) (R i/8))
          (s+2*(n+1)+14) (fun p ↦ positiveDensityAmplitude σ (v₀ i p)))
        ‖v‖ ‖PeriodicSobolevSpace.toL2 (s+1) v‖ (cNorm K (s+2*(n+1)+14) F)
        (fun i ↦ hLbound i s) (fun _ ↦ cNorm_nonneg ..) (norm_nonneg _)
        (fun i ↦ (hdensity i s v).2.2.2)

end JanetCartan.ContinuumAdjoint.Canonical
