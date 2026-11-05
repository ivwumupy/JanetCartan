module

public import JanetCartan.Iteration.PhysicalBackground.FieldProfiles
public import JanetCartan.Analysis.ContDiff.DerivativeBounds.Composition
public import JanetCartan.Analysis.ContDiff.DerivativeBounds.Products

/-!
# Profiles of the SAME physical current base and its full strain

The image covector is the uncut Bessel lift of the actual raw datum. Actual
physical map/raising profiles combine with it through fixed smooth bilinear
operations. The final strain spends one derivative of base reserve. Constants
precede all current maps, raw data and scales. The consumers are the same-field
mean correction and `app:ch_background:eq:bg-current-profile`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev CurrentMean AuxiliaryRawBand DerivativeBounds PositiveBackground
open ResponseTransfer.GradedPrimitives

private theorem bilinear_profiles
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set X} (hK : IsCompact K) (B : E →L[ℝ] F →L[ℝ] G)
    (A D : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) (hD : ∀ s, 0 ≤ D s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (f : X → E) (g : X → F),
      (∀ x ∈ K, ContDiffAt ℝ ∞ f x) → (∀ x ∈ K, ContDiffAt ℝ ∞ g x) →
      ∀ (r₀ : ℕ) (T : ℝ), 1 ≤ T → HasDerivativeProfile K f r₀ T A →
      HasDerivativeProfile K g r₀ T D →
      HasDerivativeProfile K (fun x ↦ B (f x) (g x)) r₀ T C := by
  let S := closedBall (0 : E × F) (1 + A 0 + D 0)
  let Φ : E × F → G := fun p ↦ B p.1 p.2
  have hΦ : ContDiff ℝ ∞ Φ := B.isBoundedBilinearMap.contDiff
  let L := fun s ↦ cNorm S s Φ
  let P := fun s : ℕ ↦ (s + 1 : ℝ) * (A s + D s)
  have hL (s) : 0 ≤ L s := cNorm_nonneg ..
  have hP (s) : 0 ≤ P s := mul_nonneg (by positivity) (add_nonneg (hA s) (hD s))
  refine ⟨fun s ↦ ∑ j ∈ Finset.range (s + 1), compositionConstant L P j,
    fun s ↦ Finset.sum_nonneg (fun j _ ↦ compositionConstant_nonneg hL hP j), ?_⟩
  intro f g hf hg r₀ T hT hfp hgp
  have hp := hasDerivativeProfile_prodMk hK hf hg A D hA hD hT r₀ hfp hgp
  have hrange (x) (hx : x ∈ K) : (f x, g x) ∈ S := by
    have hf0 := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf y hy).of_le (by simp : (0 : ℕ∞ω) ≤ ∞)) hx (Nat.zero_le 0)).trans (hfp 0)
    have hg0 := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hg y hy).of_le (by simp : (0 : ℕ∞ω) ≤ ∞)) hx (Nat.zero_le 0)).trans (hgp 0)
    simp only [norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] at hf0 hg0
    change dist (f x, g x) 0 ≤ 1 + A 0 + D 0
    rw [dist_zero_right, Prod.norm_def]
    apply max_le <;> linarith [hA 0, hD 0]
  exact hasDerivativeProfile_fixed_smooth_comp hK
    (fun x hx ↦ (hf x hx).prodMk (hg x hx)) (fun _ _ ↦ hΦ.contDiffAt)
    L P hL hP hT r₀ hp (fun j x hx ↦
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun _ _ ↦ hΦ.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞)) (hrange x hx) le_rfl)

private def strainBilinear (n N : ℕ) :
    (Euclidean n →L[ℝ] Euclidean N) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n := by
  let L : (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ] MetricTensor n := LinearMap.mk₂ ℝ
    (fun A B ↦ (fun i j ↦ inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1)) +
      inner ℝ (B (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1)) : MetricTensor n))
    (by intros; ext i j; simp only [add_apply, inner_add_left, inner_add_right, Matrix.add_apply]; ring)
    (by intros; ext i j; simp only [smul_apply, real_inner_smul_left, inner_smul_right, Matrix.smul_apply, smul_eq_mul]; ring)
    (by intros; ext i j; simp only [add_apply, inner_add_left, inner_add_right, Matrix.add_apply]; ring)
    (by intros; ext i j; simp only [smul_apply, real_inner_smul_left, inner_smul_right, Matrix.smul_apply, smul_eq_mul]; ring)
  exact L.mkContinuous₂ (2 * n) (by
    intro A B
    apply (metricTensor_norm_le_of_entries
      (show 0 ≤ 2 * (‖A‖ * ‖B‖) by positivity) ?_).trans_eq
    · ring
    · intro i j
      have hb (i j : Fin n) :
          ‖inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1))‖ ≤ ‖A‖ * ‖B‖ :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul
          (by simpa [PiLp.norm_single] using A.le_opNorm (EuclideanSpace.single i 1))
          (by simpa [PiLp.norm_single] using B.le_opNorm (EuclideanSpace.single j 1))
          (norm_nonneg _) (norm_nonneg _))
      change ‖inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1)) +
        inner ℝ (B (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))‖ ≤ _
      rw [real_inner_comm (A (EuclideanSpace.single j 1)) (B (EuclideanSpace.single i 1))]
      exact (norm_add_le _ _).trans (by linarith [hb i j, hb j i]))

/-- Physical map and raising-coefficient profiles, together with the actual
uncorrected raw inverse profile, produce the base and its FULL strain profile.
The input map/raising profiles are proved by `PhysicalHistory` and
`exists_history_halfTangent_profile`; raw estimates are from task22 applied to
the measured source. There is no base-field/strain success premise. Reserve
`r₀+1+n` of the raw image suffices, including the final strain derivative
(`app:ch_background:eq:bg-current-profile`). -/
theorem exists_baseVariation_strain_profile {n N : ℕ} {ι : Type*} [Fintype ι]
    {K W : Set (Euclidean n)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiffOn ℝ ∞ X₀ W)
    (A C D : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) (hC : ∀ s, 0 ≤ C s) (hD : ∀ s, 0 ≤ D s) :
    ∃ E : ℕ → ℝ, (∀ s, 0 ≤ E s) ∧
      ∀ (F : Euclidean n → Euclidean N), ContDiff ℝ ∞ F → IsImmersionOn F W →
      ∀ (raw : AugmentedInput n ι), (∀ s, raw ∈ augmentedInputLevel n ι s) →
      ∀ (r₀ : ℕ) (T : ℝ), 1 ≤ T →
      HasDerivativeProfile K F (r₀ + 2) T A →
      HasDerivativeProfile K (halfTangentCoefficient F) (r₀ + 1) T C →
      (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s raw ≤
        D s * T ^ (s - (r₀ + 1 + n))) →
      ∀ s, cNorm K s (baseVariation χsrc raw F X₀) +
        cNorm K s (linearizedMetric F (baseVariation χsrc raw F X₀)) ≤ E s * T ^ (s - r₀) := by
  have hx (x) (hx : x ∈ K) := hX₀.contDiffAt (hW.mem_nhds (hKW hx))
  obtain ⟨Cu, hCu, hcov⟩ := exists_uncut_covector_profile (ι := ι) χsrc hs D hD
  obtain ⟨Ct, hCt, htan⟩ := bilinear_profiles hK
    (ContinuousLinearMap.id ℝ (Euclidean n →L[ℝ] Euclidean N))
    (fun s ↦ A (s + 1)) (fun s ↦ cNorm K s X₀) (fun _ ↦ hA _) (fun _ ↦ cNorm_nonneg ..)
  obtain ⟨Ci, hCi, himage⟩ := bilinear_profiles hK
    (ContinuousLinearMap.id ℝ (Euclidean n →L[ℝ] Euclidean N)) C Cu hC hCu
  let Cv := fun s ↦ Ct s + Ci s
  have hCv (s) : 0 ≤ Cv s := add_nonneg (hCt s) (hCi s)
  obtain ⟨Cs, hCs, hstrain⟩ := bilinear_profiles hK (strainBilinear n N)
    (fun s ↦ A (s + 1)) (fun s ↦ Cv (s + 1)) (fun _ ↦ hA _) (fun _ ↦ hCv _)
  refine ⟨fun s ↦ Cv s + Cs s, fun s ↦ add_nonneg (hCv s) (hCs s), ?_⟩
  intro F hF hi raw hreg r₀ T hT hFp hCp hraw s
  have hdF : HasDerivativeProfile K (fderiv ℝ F) (r₀ + 1) T (fun j ↦ A (j + 1)) := by
    intro j
    apply ((GeometricProfile.cNorm_fderiv_le K j F).trans (hFp (j + 1))).trans
    apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hA _)
  have hXp : HasDerivativeProfile K X₀ (r₀ + 1) T (fun j ↦ cNorm K j X₀) := by
    intro j
    exact le_mul_of_one_le_right (cNorm_nonneg ..) (one_le_pow₀ hT)
  have htp := htan (fderiv ℝ F) X₀ (fun _ _ ↦ (hF.fderiv_right (by simp)).contDiffAt) hx
    (r₀ + 1) T hT hdF hXp
  have hu := isSmoothPeriodic_preparationCovector χsrc hs raw.fst.fst
    (fun j ↦ ((mem_augmentedInputLevel_iff j raw).mp (hreg j)).1)
  have hraise := HistoryAuxiliaryCoefficients.contDiffOn_halfTangentCoefficient hF hi
  have hip := himage (halfTangentCoefficient F) (periodicLift (preparationCovector χsrc raw.fst.fst))
    (fun x hx ↦ hraise.contDiffAt (hW.mem_nhds (hKW hx))) (fun _ _ ↦ hu.2.contDiffAt)
    (r₀ + 1) T hT hCp (hcov raw hreg T (r₀ + 1) hraw K)
  simp only [ContinuousLinearMap.id_apply] at htp hip
  change HasDerivativeProfile K (tangentVariation F X₀) (r₀ + 1) T Ct at htp
  have hv := contDiffOn_baseVariation χsrc hs raw hreg hW hF.contDiffOn hX₀ hi
  have hVp : HasDerivativeProfile K (baseVariation χsrc raw F X₀) (r₀ + 1) T Cv := by
    intro j
    have ht : ∀ x ∈ K, ContDiffAt ℝ j (tangentVariation F X₀) x :=
      fun x hx ↦ ((contDiffOn_tangentVariation hW hF.contDiffOn hX₀).contDiffAt
        (hW.mem_nhds (hKW hx))).of_le (by simp)
    have himg : ∀ x ∈ K, ContDiffAt ℝ j
        (AuxiliaryRealization.tangentialField F (periodicLift (preparationCovector χsrc raw.fst.fst))) x :=
      fun x hx ↦ ((AuxiliaryRealization.contDiffOn_tangentialField hW hF.contDiffOn
        hu.2.contDiffOn hi).contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp)
    have hb := cNorm_add_le_of_contDiffAt hK ht himg
    change cNorm K j (baseVariation χsrc raw F X₀) ≤ _ at hb
    have hiEq : (fun x ↦ halfTangentCoefficient F x
        (periodicLift (preparationCovector χsrc raw.fst.fst) x)) =
        AuxiliaryRealization.tangentialField F (periodicLift (preparationCovector χsrc raw.fst.fst)) := by
      funext x
      exact halfTangentCoefficient_apply F _ x
    rw [hiEq] at hip
    apply hb.trans
    calc
      _ ≤ Ct j * T ^ (j - (r₀ + 1)) + Ci j * T ^ (j - (r₀ + 1)) :=
        add_le_add (htp j) (hip j)
      _ = Cv j * T ^ (j - (r₀ + 1)) := by dsimp only [Cv]; ring
  have hdF' : HasDerivativeProfile K (fderiv ℝ F) r₀ T (fun j ↦ A (j + 1)) := by
    intro j
    exact (hdF j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hA _))
  have hdV : HasDerivativeProfile K (fderiv ℝ (baseVariation χsrc raw F X₀)) r₀ T
      (fun j ↦ Cv (j + 1)) := by
    intro j
    apply ((GeometricProfile.cNorm_fderiv_le K j _).trans (hVp (j + 1))).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hCv _)
  have hsp := hstrain (fderiv ℝ F) (fderiv ℝ (baseVariation χsrc raw F X₀))
    (fun _ _ ↦ (hF.fderiv_right (by simp)).contDiffAt)
    (fun x hx ↦ (hv.contDiffAt (hW.mem_nhds (hKW hx))).fderiv_right (by simp))
    r₀ T hT hdF' hdV s
  change cNorm K s (linearizedMetric F (baseVariation χsrc raw F X₀)) ≤ _ at hsp
  have hvp : cNorm K s (baseVariation χsrc raw F X₀) ≤ Cv s * T ^ (s - r₀) :=
    (hVp s).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hCv s))
  simpa only [add_mul] using add_le_add hvp hsp

end JanetCartan.PhysicalBackground
