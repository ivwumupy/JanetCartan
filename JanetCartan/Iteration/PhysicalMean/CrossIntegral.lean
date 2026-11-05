module

public import JanetCartan.Iteration.PhysicalMean.NativeCross
public import JanetCartan.Iteration.PhysicalForwardMean.MatrixBranches
public import JanetCartan.Iteration.PhysicalSamplingShells.Space

/-!
# The actual modified cross row on the original disjoint annular space

The constructed native vector row is identified with the measured Hermitian
cross of the SAME full matrix forward integrals. The lower field may vary with
every original retained sample label, but never with its frequency variable.
All original masks, square-root sample weights and native input coefficients
stay inside their original integrals (`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CanonicalRowComparison CurrentMean PhysicalSamplingShells RawInputRealization
open PhysicalForwardMean NormalComparison Pseudodifferential AmplitudeBound

/-- Real part commutes through the actual measured varying-background cross
sum. Both the background and full forward matrix are unchanged at each retained
sample label; no common background or principal amplitude is substituted. -/
theorem measured_varying_cross_sum_integral {n N : ℕ} {ι X : Type*}
    [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) (C : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : ι → Matrix (Fin N) (Fin n) ℂ) (f : ι → X → ℂ)
    (G : ι → X → Matrix (Fin N) (Fin n) ℂ)
    (hint : ∀ i, Integrable (fun η ↦ f i η • G i η) (μ i)) :
    euclideanRealPart (∑ i, ∫ η, f i η • complexCrossMeasurement C (B i) (G i η) ∂μ i) =
      C (∑ i, mixedHermitianTensor (B i) (∫ η, f i η • G i η ∂μ i)) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∫ η, f i η • complexCrossMeasurement C (B i) (G i η) ∂μ i) =
      complexCrossMeasurement C (B i) (∫ η, f i η • G i η ∂μ i) := by
    simpa only [map_smul] using (complexCrossMeasurement C (B i)).integral_comp_comm (hint i)
  rw [he, complexCrossMeasurement_realPart]

section Annular

variable {n N : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
    [MeasurableSpace ι] [BorelSpace ι]
    (radius : ι → ℝ)
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (G : (ι × Euclidean (n-1)) → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C)
    (hBc : Continuous (fun q : (ι × Euclidean (n-1)) × Euclidean n ↦ B q.1.1 q.2))
    (hGc : Continuous (Function.uncurry G))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hGK : ∀ u, tsupport (G u) ⊆ K)

local notation "μshell" => annularShellMeasure (n := n) radius
local notation "Mat" => Matrix (Fin N) (Fin n) ℂ

include hφ hm hms hC hBc hGc hK hGK in
/-- The real native FULL cross integral is exactly the measured sum of the
same full matrix forward fields on the ORIGINAL separate annuli. This is an
identity of physical values. No weight is divided out, no overlapping annuli
are merged, and integrability is derived from the primitive compact kernels. -/
theorem nativeCrossIntegral_annular_eq (w : Lp ℂ 2 μshell) (x : Euclidean n) :
    euclideanRealPart (nativeCrossIntegral μshell φ m C (fun u ↦ B u.1) G w x) =
      C x (∑ i, mixedHermitianTensor (B i x)
        (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*w (i,η)) • G (i,η) x)
          ∂annularMeasure n (radius i) : Mat)) := by
  let f : (ι × Euclidean (n-1)) → ℂ := fun u ↦
    (m u : ℂ)*oscillatoryFactor 1 (φ u x)*w u
  have hAc (a : Fin N) (c : Fin n) : Continuous (fun q : (ι × Euclidean (n-1)) × Euclidean n ↦
      G q.1 q.2 a c) := (matrixEntryEvaluation a c).continuous.comp hGc
  have hAK (a : Fin N) (c : Fin n) (u : ι × Euclidean (n-1)) :
      tsupport (fun y ↦ G u y a c) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    apply hGK u
    apply subset_tsupport
    intro hzero
    apply hy
    exact congrArg (fun M : Mat ↦ M a c) hzero
  have hmraw := (physicalMatrixForwardIntegral_integrable_apply φ m
    (fun a c u y ↦ G u y a c) hφ hm hms hAc hK hAK
    (fun u ↦ w u) (Lp.memLp w) x).1
  have hmatrix : Integrable (fun u ↦ f u • G u x) μshell := by
    convert hmraw using 1
    funext u
    ext a c
    simp only [f, Matrix.smul_apply, smul_eq_mul, physicalForwardKernel,
      sampledMomentKernel, star_star]
    ring
  have hpart (i : ι) : Integrable (fun η ↦ f (i,η) • G (i,η) x) (annularMeasure n (radius i)) := by
    exact (measurableEmbedding_prodMk_left i).integrable_map_iff.mp
      (hmatrix.mono_measure (show (annularMeasure n (radius i)).map (Prod.mk i) ≤ μshell from
        Measure.le_sum (fun j ↦ (annularMeasure n (radius j)).map (Prod.mk j)) i))
  have hcross := nativeCrossIntegral_integrable μshell φ m hφ hm hms C (fun u ↦ B u.1) G
    hC hBc hGc hK hGK w x
  change euclideanRealPart (∫ u, f u • complexCrossMeasurement (C x) (B u.1 x) (G u x) ∂μshell) = _
  change euclideanRealPart (∫ u, f u • complexCrossMeasurement (C x) (B u.1 x) (G u x)
    ∂Measure.sum (fun i ↦ (annularMeasure n (radius i)).map (Prod.mk i))) = _
  rw [integral_sum_measure hcross, tsum_fintype]
  simp_rw [(measurableEmbedding_prodMk_left _).integral_map]
  exact measured_varying_cross_sum_integral (fun i ↦ annularMeasure n (radius i)) (C x)
    (fun i ↦ B i x) (fun i η ↦ f (i,η)) (fun i η ↦ G (i,η) x) hpart

/-- Almost-everywhere physical realization of the actual native row by the
original weighted full Hermitian cross. This supplies the missing identity in
the quadratic branch consumer without assuming a successful modified row. -/
theorem nativeCrossRow_realPart_annular_ae (w : Lp ℂ 2 μshell) :
    (fun x ↦ euclideanRealPart
      (nativeCrossRow μshell φ m hφ hm hms C (fun u ↦ B u.1) G hC hBc hGc hK hGK w x)) =ᵐ[volume]
      fun x ↦ C x (∑ i, mixedHermitianTensor (B i x)
        (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*w (i,η)) • G (i,η) x)
          ∂annularMeasure n (radius i) : Mat)) := by
  filter_upwards [nativeCrossRow_ae_kernel μshell φ m hφ hm hms C (fun u ↦ B u.1) G
    hC hBc hGc hK hGK w] with x hx
  rw [hx]
  exact nativeCrossIntegral_annular_eq radius φ m hφ hm hms C B G hC hBc hGc hK hGK w x

/-- The actual measured cross of the original separate full matrix forward
fields. Native masks retain their own square-root sample weights. -/
def annularMeasuredCross (w : Lp ℂ 2 μshell) (x : Euclidean n) : Euclidean n :=
  C x (∑ i, mixedHermitianTensor (B i x)
    (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*w (i,η)) • G (i,η) x)
      ∂annularMeasure n (radius i) : Mat))

/-- The actual physical cross has genuine L² membership and its norm is at
most that of the constructed original native complex row applied to the SAME
input. The contraction has constant one: this is `Re`, not the row's `2 Re`,
and therefore matches the quadratic tensor without an artificial factor two. -/
theorem annularMeasuredCross_memLp_norm (w : Lp ℂ 2 μshell) :
    MemLp (annularMeasuredCross radius φ m C B G w) 2 volume ∧
      lpNorm (annularMeasuredCross radius φ m C B G w) 2 volume ≤
        ‖nativeCrossRow μshell φ m hφ hm hms C (fun u ↦ B u.1) G hC hBc hGc hK hGK‖*‖w‖ := by
  let S := nativeCrossRow μshell φ m hφ hm hms C (fun u ↦ B u.1) G hC hBc hGc hK hGK
  have hrow := nativeCrossRow_realPart_annular_ae radius φ m hφ hm hms C B G hC hBc hGc hK hGK w
  change (fun x ↦ euclideanRealPart (S w x)) =ᵐ[volume] annularMeasuredCross radius φ m C B G w at hrow
  have hrep : l2RealPart volume (S w) =ᵐ[volume] annularMeasuredCross radius φ m C B G w := by
    have he := (euclideanRealPart (ι := Fin n)).coeFn_compLpL (p := 2)
      (μ := (volume : Measure (Euclidean n))) (S w)
    exact he.trans hrow
  refine ⟨(memLp_congr_ae hrep).mp (Lp.memLp (l2RealPart volume (S w))), ?_⟩
  have hn : lpNorm (annularMeasuredCross radius φ m C B G w) 2 volume = ‖l2RealPart volume (S w)‖ := by
    rw [← toReal_eLpNorm, eLpNorm_congr_ae hrep.symm]
    exact (Lp.norm_def _).symm
  rw [hn]
  exact ((l2RealPart volume).le_opNorm (S w)).trans
    (((mul_le_mul_of_nonneg_right (l2RealPart_norm_le volume) (norm_nonneg (S w))).trans_eq
      (one_mul _)).trans (S.le_opNorm w))

/-- Place the original square-root-weighted annular inputs in their SAME
native disjoint shell Hilbert space. This is an isometry, not a samplewise
estimate or a division by any sample weight. -/
def weightedAnnularInput (weight : ι → ℝ)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) : Lp ℂ 2 μshell :=
  (annularShellEquiv radius).symm (WithLp.toLp 2 (fun i ↦ Real.sqrt (weight i) • f i))

/-- Exact original weighted input norm, with no finite-label cardinality. -/
theorem norm_weightedAnnularInput (weight : ι → ℝ)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) :
    ‖weightedAnnularInput radius weight f‖ =
      ‖(WithLp.toLp 2 (fun i ↦ Real.sqrt (weight i) • f i) :
        PiLp 2 (fun i ↦ Lp ℂ 2 (annularMeasure n (radius i))))‖ := by
  exact (annularShellEquiv radius).symm.norm_map _

/-- Every original annular component has its literal square-root sample
weight. Zero weights are included and no inverse weight is used. -/
theorem weightedAnnularInput_ae (weight : ι → ℝ)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ι) :
    (fun η ↦ weightedAnnularInput radius weight f (i,η)) =ᵐ[annularMeasure n (radius i)]
      fun η ↦ Real.sqrt (weight i) • f i η := by
  have he := (annularShellEquiv_ae radius (weightedAnnularInput radius weight f) i).symm
  simp only [weightedAnnularInput, LinearIsometryEquiv.apply_symm_apply] at he
  exact he.trans (Lp.coeFn_smul (Real.sqrt (weight i)) (f i))

/-- Putting one square-root weight in the original mask and one in the
original input gives EXACTLY the weighted Hermitian quadratic branch. This
proves the original sample-weight identity even when a weight is zero. -/
theorem annularMeasuredCross_weighted_eq (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (x : Euclidean n) :
    annularMeasuredCross radius φ (fun u ↦ Real.sqrt (weight u.1)*m u) C B G
      (weightedAnnularInput radius weight f) x =
    C x (∑ i, weight i • mixedHermitianTensor (B i x)
      (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*f i η) • G (i,η) x)
        ∂annularMeasure n (radius i) : Mat)) := by
  unfold annularMeasuredCross
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (∫ η, (((Real.sqrt (weight i)*m (i,η) : ℝ) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*
        weightedAnnularInput radius weight f (i,η)) • G (i,η) x ∂annularMeasure n (radius i) : Mat) =
      weight i • (∫ η, (((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*f i η) • G (i,η) x)
        ∂annularMeasure n (radius i) : Mat) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [weightedAnnularInput_ae radius weight f i] with η hη
    rw [hη]
    ext a c
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    have hs : (Real.sqrt (weight i) : ℂ)*(Real.sqrt (weight i) : ℂ) = (weight i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hweight i)]
    calc
      _ = ((Real.sqrt (weight i) : ℂ)*(Real.sqrt (weight i) : ℂ))*
          ((m (i,η) : ℂ)*oscillatoryFactor 1 (φ (i,η) x)*f i η*G (i,η) x a c) := by ring
      _ = _ := by rw [hs]
  rw [he]
  change hermitianContinuousBilinear (B i x) (weight i • _) = weight i • hermitianContinuousBilinear (B i x) _
  exact map_smul _ _ _

end Annular
end JanetCartan.PhysicalMean
