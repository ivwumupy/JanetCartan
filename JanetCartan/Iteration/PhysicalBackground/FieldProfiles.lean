module

public import JanetCartan.Iteration.PhysicalBackground.Field
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.HistoryAuxiliaryCoefficients.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationFieldBounds

/-!
# Physical raising coefficients and the uncut current image profile

The half-tangent coefficient is evaluated on the actual revised physical
Schwartz prefix. Its profile follows from the actual compact second-jet range,
not a periodic-history surrogate. The original image multiplier and Bessel
inverse convert task22's raw profile to the SAME physical uncut covector.
These are quantitative ingredients of `app:ch_background:eq:bg-current-profile`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open GeometricProfile ProjectedStressFrame HistoryAuxiliaryCoefficients
open ContinuumRow CarrierSobolev CurrentMean AuxiliaryRawBand

/-- Actual physical history admissibility gives the half-tangent coefficient
profile with reserve two, before all histories and derivative orders. This
coefficient is the one in `baseVariation`, not a new lifting operator. -/
theorem exists_history_halfTangent_profile {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      IsImmersionOn F (ball 0 R) ∧ ContDiffOn ℝ ∞ (halfTangentCoefficient F) (ball 0 R) ∧
      HasDerivativeProfile (closedBall 0 r) (halfTangentCoefficient F)
        reserve (currentCoefficientScale R₀ j) C := by
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G hr hrR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L, hL, hunit, Sj, hSj, hjet⟩ :=
    PhysicalGeometry.exists_history_jet_range G hR hB hStar horder
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) r) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  choose D hD hbound using fun s ↦ exists_physicalAuxiliaryCoefficientNorm_le
    (0 : Euclidean n) hr hL (fun J hJ ↦ (hunit J hJ).1) s
  refine ⟨max Sg Sj, hSg.trans (le_max_left _ _), (fun s ↦ D s * (1 + A (s + 2))),
    (fun s ↦ mul_nonneg (hD s).le (by linarith [hA (s + 2)])), ?_⟩
  intro R₀ hR₀ j u ell hu F
  have hRg := (le_max_left Sg Sj).trans hR₀
  have hRj := (le_max_right Sg Sj).trans hR₀
  have htwo := hSg.trans hRg
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hi := (hgeom R₀ hRg j u ell hu).1
  have hLmap : MapsTo (stressJet F) (closedBall 0 r) L :=
    (hjet R₀ hRj j u ell hu).mono_left (closedBall_subset_closedBall hrR.le)
  have hp := hprofile R₀ htwo j u ell hu _ Subset.rfl
  refine ⟨hi, contDiffOn_halfTangentCoefficient hF hi, ?_⟩
  intro s
  have hraise : cNorm (closedBall (0 : Euclidean n) r) s (halfTangentCoefficient F) ≤
      D s * (1 + cNorm (closedBall 0 r) (s + 2) F) := by
    apply le_trans _ (hbound s F hF hLmap)
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦
      Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ cNorm_nonneg ..))))
  exact JointBudget.fixed_profile_transfer_bound
    (one_le_currentCoefficientScale (by linarith) j) (hA (s + 2)) (hD s).le
    hreserve (hp (s + 2)) hraise

private theorem image_grade_le {n : ℕ} {ι : Type*} [Fintype ι]
    {s : ℕ} {u : AugmentedInput n ι} (hu : u ∈ augmentedInputLevel n ι s) :
    periodicSobolevNorm s u.fst.fst ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  exact (PeriodicSobolevSpace.norm_eq s v.fst.fst).symm.le.trans
    ((WithLp.norm_fst_le _ v.fst).trans (WithLp.norm_fst_le _ v))

/-- The SAME original source multiplier and Bessel image lift have a physical
profile with the explicit fixed reserve `n`. The raw input may be the current
uncorrected inverse applied to the literal measured source. Constants precede
the raw input, derivative order, physical set and coefficient scale. -/
theorem exists_uncut_covector_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (D : ℕ → ℝ) (hD : ∀ s, 0 ≤ D s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (u : AugmentedInput n ι), (∀ s, u ∈ augmentedInputLevel n ι s) →
      ∀ (T : ℝ) (r₀ : ℕ),
        (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s u ≤ D s * T ^ (s - (r₀ + n))) →
      ∀ K : Set (Euclidean n),
        HasDerivativeProfile K (periodicLift (preparationCovector χsrc u.fst.fst)) r₀ T C := by
  choose A hA hbound using fun s ↦ exists_preparationCovector_cNorm_bound (n := n) s
    (cNorm_nonneg (fundamentalCell n) (s + n) (periodicLift χsrc))
  refine ⟨fun s ↦ A s * D (s + n), fun s ↦ mul_nonneg (hA s) (hD _), ?_⟩
  intro u hu T r₀ hraw K s
  have him (j : ℕ) : u.fst.fst ∈ periodicSobolevLevel n (Euclidean n) j :=
    ((mem_augmentedInputLevel_iff j u).mp (hu j)).1
  have hc := isSmoothPeriodic_preparationCovector χsrc hs u.fst.fst him
  have hlocal : cNorm K s (periodicLift (preparationCovector χsrc u.fst.fst)) ≤
      cNorm (fundamentalCell n) s (periodicLift (preparationCovector χsrc u.fst.fst)) := by
    apply cNorm_le_sum_of_bounds
      (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) j _)
    intro j hj x _
    apply norm_iteratedFDeriv_periodicLift_le _ j _ x
    intro y hy
    exact le_csSup (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n)
      (hc.2.of_le (by simp) : ContDiff ℝ s _) hj) (mem_image_of_mem _ hy)
  calc
    _ ≤ A s * periodicSobolevNorm (s + n : ℕ) u.fst.fst :=
      hlocal.trans (hbound s χsrc hs le_rfl u.fst.fst him)
    _ ≤ A s * (D (s + n) * T ^ (s + n - (r₀ + n))) :=
      mul_le_mul_of_nonneg_left ((image_grade_le (hu _)).trans (hraw _)) (hA s)
    _ = _ := by rw [Nat.add_sub_add_right]; ring

end JanetCartan.PhysicalBackground
