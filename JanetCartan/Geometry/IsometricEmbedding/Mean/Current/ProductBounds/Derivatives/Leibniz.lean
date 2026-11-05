module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.Jets
open scoped ContDiff
/-!
# Weighted Leibniz bounds with separate derivative orders

The pointwise derivative step for `main:lem:mean-recurrence`. The following
estimates retain each coefficient and input derivative order, and weighted
Cauchy–Schwarz introduces no sample-count constant or division by weights.
-/

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
variable {d : ℕ} {ι F G H : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- `main:lem:mean-recurrence`: smoothness of the actual weighted bilinear field. -/
theorem isSmoothPeriodic_weightedBilinear (B : F →L[ℝ] G →L[ℝ] H) (D : Torus d → ι → F) (E : Torus d → ι → G)
    (μ : ι → ℝ) (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i)) :
    IsSmoothPeriodic (fun x ↦ ∑ i, μ i • B (D x i) (E x i)) := by
  constructor
  · apply continuous_finsetSum
    intro i _
    exact (B.isBoundedBilinearMap.continuous.comp ((hD i).1.prodMk (hE i).1)).const_smul _
  · apply ContDiff.sum
    intro i _
    exact (B.isBoundedBilinearMap.contDiff.comp ((hD i).2.prodMk (hE i).2)).const_smul _

private theorem sum_weight_mul_le_sqrt_mul_sqrt (μ a b : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    (∑ i, μ i * a i * b i) ≤ Real.sqrt (∑ i, μ i * a i ^ 2) *
      Real.sqrt (∑ i, μ i * b i ^ 2) := by
  have h := Real.le_sqrt_of_sq_le (WeightedFamily.sum_weight_mul_sq_le Finset.univ μ
    (fun i _ ↦ hμ i) a b)
  simpa only [Real.sqrt_mul (Finset.sum_nonneg
    (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg (a i))))] using h

private theorem norm_iteratedFDeriv_weightedBilinear_le (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i)) (s : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ s (fun y ↦ ∑ i, μ i •
      B (periodicLift (fun x ↦ D x i) y) (periodicLift (fun x ↦ E x i) y)) y‖ ≤
      ∑ r ∈ Finset.range (s + 1), (s.choose r : ℝ) *
        ∑ i, μ i * ‖iteratedFDeriv ℝ r (periodicLift (fun x ↦ D x i)) y‖ *
          ‖iteratedFDeriv ℝ (s-r) (periodicLift (fun x ↦ E x i)) y‖ := by
  have hprod (i : ι) : ContDiff ℝ ∞ (fun y ↦
      B (periodicLift (fun x ↦ D x i) y) (periodicLift (fun x ↦ E x i) y)) :=
    B.isBoundedBilinearMap.contDiff.comp ((hD i).2.prodMk (hE i).2)
  rw [iteratedFDeriv_sum (fun i _ ↦ (hprod i).const_smul (μ i) |>.of_le (by simp))]
  simp only [Finset.sum_apply]
  simp_rw [iteratedFDeriv_const_smul_apply' ((hprod _).of_le (by simp)).contDiffAt]
  apply (WeightedFamily.norm_sum_weight_smul_le Finset.univ μ (fun i _ ↦ hμ i) _).trans
  calc
    _ ≤ ∑ i, μ i * ∑ r ∈ Finset.range (s + 1), (s.choose r : ℝ) *
        ‖iteratedFDeriv ℝ r (periodicLift (fun x ↦ D x i)) y‖ *
        ‖iteratedFDeriv ℝ (s-r) (periodicLift (fun x ↦ E x i)) y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one (hD i).2 (hE i).2 y (by simp) hB)
        (hμ i)
    _ = _ := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; congr 1; funext r; congr 1; funext i; ring

/-- `main:lem:mean-recurrence`: weighted Leibniz and Cauchy–Schwarz,
placing only the lower factor in `Cʳ` and retaining the higher derivative's
pointwise weighted energy at the complementary order `s-r`. -/
theorem norm_periodicJet_weightedBilinear_le (B : F →L[ℝ] G →L[ℝ] H)
    (hB : ‖B‖ ≤ 1) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i)) (s : ℕ) (x : Torus d) :
    ‖periodicJet s (fun x ↦ ∑ i, μ i • B (D x i) (E x i)) x‖ ≤
      ∑ r ∈ Finset.range (s + 1), (s.choose r : ℝ) * weightedPeriodicCNorm μ r D *
        Real.sqrt (∑ i, μ i * ‖periodicJet (s-r) (fun x ↦ E x i) x‖ ^ 2) := by
  obtain ⟨y, rfl⟩ := exists_torusQuotient_eq x
  change ‖periodicLift (periodicJet s _) y‖ ≤ _
  rw [(periodicJet_spec (isSmoothPeriodic_weightedBilinear B D E μ hD hE) s).2]
  apply (norm_iteratedFDeriv_weightedBilinear_le B hB D E μ hμ hD hE s y).trans
  apply Finset.sum_le_sum
  intro r _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have heq (i : ι) : iteratedFDeriv ℝ (s-r) (periodicLift (fun x ↦ E x i)) y =
      periodicJet (s-r) (fun x ↦ E x i) (torusQuotient y) :=
    congr_fun (periodicJet_spec (hE i) (s-r)).2.symm y
  simp_rw [heq]
  calc
    _ ≤ ∑ i, μ i * cNorm (fundamentalCell d) r (periodicLift (fun x ↦ D x i)) *
        ‖periodicJet (s-r) (fun x ↦ E x i) (torusQuotient y)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (hμ i)
      rw [← (periodicJet_spec (hD i) r).2]
      exact norm_periodicJet_le_cNorm (hD i) r (torusQuotient y)
    _ ≤ _ := sum_weight_mul_le_sqrt_mul_sqrt μ _ _ hμ

/-- `main:lem:mean-recurrence`: periodic form of the bilinear Leibniz
inequality, also used for applying the variable measurement coefficient. -/
theorem norm_periodicJet_bilinear_le (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    {f : Torus d → F} {g : Torus d → G}
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (s : ℕ) (x : Torus d) :
    ‖periodicJet s (fun x ↦ B (f x) (g x)) x‖ ≤
      ∑ a ∈ Finset.range (s + 1), (s.choose a : ℝ) * ‖periodicJet a f x‖ *
        ‖periodicJet (s-a) g x‖ := by
  have hfg : IsSmoothPeriodic (fun x ↦ B (f x) (g x)) :=
    ⟨B.isBoundedBilinearMap.continuous.comp (hf.1.prodMk hg.1),
      B.isBoundedBilinearMap.contDiff.comp (hf.2.prodMk hg.2)⟩
  obtain ⟨y, rfl⟩ := exists_torusQuotient_eq x
  have hf' (r : ℕ) := congr_fun (periodicJet_spec hf r).2 y
  have hg' (r : ℕ) := congr_fun (periodicJet_spec hg r).2 y
  have hfg' := congr_fun (periodicJet_spec hfg s).2 y
  change periodicJet s _ (torusQuotient y) = _ at hfg'
  change ∀ r, periodicJet r f (torusQuotient y) = _ at hf'
  change ∀ r, periodicJet r g (torusQuotient y) = _ at hg'
  simp_rw [hfg', hf', hg']
  exact B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf.2 hg.2 y (by simp) hB

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `main:lem:mean-recurrence`: the actual variable measurement contraction,
with joint derivative budget `a + r + (s-a-r) = s`. This is a proved Leibniz
bound; no nonlinear contraction assumption is made. -/
theorem norm_periodicJet_contracted_weightedBilinear_le
    (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i))
    (C : Torus d → H →L[ℝ] V) (hC : IsSmoothPeriodic C) (s : ℕ) (x : Torus d) :
    ‖periodicJet s (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i))) x‖ ≤
      ∑ a ∈ Finset.range (s + 1), ∑ r ∈ Finset.range (s-a+1),
        (s.choose a : ℝ) * ((s-a).choose r : ℝ) *
          cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
            Real.sqrt (∑ i, μ i * ‖periodicJet (s-a-r) (fun x ↦ E x i) x‖ ^ 2) := by
  let A : (H →L[ℝ] V) →L[ℝ] H →L[ℝ] V := (ContinuousLinearMap.apply ℝ V).flip
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound₂ zero_le_one
    intro L v
    change ‖L v‖ ≤ 1 * ‖L‖ * ‖v‖
    simpa only [one_mul] using L.le_opNorm v
  apply (norm_periodicJet_bilinear_le A hA hC
    (isSmoothPeriodic_weightedBilinear B D E μ hD hE) s x).trans
  apply Finset.sum_le_sum
  intro a _
  calc
    _ ≤ (s.choose a : ℝ) * cNorm (fundamentalCell d) a (periodicLift C) *
        (∑ r ∈ Finset.range (s-a+1), ((s-a).choose r : ℝ) *
          weightedPeriodicCNorm μ r D *
            Real.sqrt (∑ i, μ i * ‖periodicJet (s-a-r) (fun x ↦ E x i) x‖ ^ 2)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_periodicJet_le_cNorm hC a x) (Nat.cast_nonneg _))
        (norm_periodicJet_weightedBilinear_le B hB μ hμ D E hD hE (s-a) x)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

end JanetCartan.CurrentMean
