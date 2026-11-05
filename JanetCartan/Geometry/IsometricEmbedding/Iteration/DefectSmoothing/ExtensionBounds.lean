module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.Extension

/-!
# All-order bounds for the fixed tensor extension

The extension in `main:lem:smoothing` is bounded at every integer order in the
actual Frobenius tensor norm. These are the input bounds for the cutoff tail in
`main:eq:smoothing-high`. The scalar Seeley estimate is applied to each real
entry, with intrinsic core jets identified with ambient jets using smoothness
on the larger chart, including at the core boundary.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius Topology
open Set Metric

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

private def entryMap (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

private def entryInsertion (i j : Fin n) : ℝ →L[ℝ] MetricTensor n :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Matrix.single i j 1)

private theorem sum_entryInsertion (A : MetricTensor n) :
    (∑ i, ∑ j, entryInsertion i j (entryMap i j A)) = A := by
  ext a b
  simp [entryInsertion, entryMap, Matrix.sum_apply, Matrix.single_apply, ite_and]

-- Used twice below: extraction on the core and insertion on the closed cell.
private theorem cNorm_postLinear_local {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set (Euclidean n)} (hs : IsCompact s) (r : ℕ)
    (L : F →L[ℝ] G) {f : Euclidean n → F}
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x) :
    cNorm s r (L ∘ f) ≤ ‖L‖ * cNorm s r f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg s j f))
  intro j hj x hx
  apply (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hj)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hs hf hj)
      (mem_image_of_mem _ hx)) (norm_nonneg _)

private theorem closedBallCNorm_eq_core (D : LocalDomain)
    {g : Euclidean n → ℝ} (hg : ContDiffOn ℝ ∞ g (D.chart n)) (r : ℕ) :
    (extensionParameters D).closedBallCNorm r g = cNorm (D.core n) r g := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro x hx
  have hsub : D.core n ⊆ D.chart n :=
    closedBall_subset_ball D.coreRadius_lt_chartRadius
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (extensionParameters D).uniqueDiffOn_closedBall
    ((hg.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).of_le (by simp)) hx]

-- Compact support supplies the boundedness required for the real supremum
-- over all of Euclidean space in the scalar Seeley estimate.
private theorem cNorm_seeleyExtension_cell_le_univ (D : LocalDomain) (r : ℕ)
    {g : Euclidean n → ℝ} (hg : ContDiffOn ℝ ∞ g (D.core n)) :
    cNorm (fundamentalCell n) r ((extensionParameters D).seeleyExtension g) ≤
      cNorm univ r ((extensionParameters D).seeleyExtension g) := by
  obtain ⟨B, _, hB⟩ :=
    ((extensionParameters D).hasCompactSupport_seeleyExtension g).exists_bound_iteratedFDeriv
      ((extensionParameters D).contDiff_seeleyExtension hg) r
  apply cNorm_mono_set_of_bddAbove (subset_univ _)
  intro j hj
  exact ⟨B, by rintro _ ⟨x, _, rfl⟩; exact hB j hj x⟩

private theorem cNorm_periodicLift_extendToTorus_eq (D : LocalDomain)
    (f : MetricField n) (r : ℕ) :
    cNorm (fundamentalCell n) r (periodicLift (extendToTorus D f)) =
      cNorm (fundamentalCell n) r (tensorExtension D f) := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro x hx
  exact congrArg norm ((tensorPeriodization_eventuallyEq D.chartRadius_lt_half
    (tsupport_tensorExtension_subset D f) hx).iteratedFDeriv ℝ j).eq_of_nhds

/-- The concrete extension of `main:lem:smoothing` satisfies all `C^r` bounds
in the Frobenius norm. The same domain-fixed operator works for every order
and input; this estimate feeds the high cutoff tail `main:eq:smoothing-high`.
Smoothness on the chart justifies ambient derivatives even on the core sphere. -/
theorem exists_cNorm_extendToTorus_le (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : MetricField n),
      ContDiffOn ℝ ∞ f (D.chart n) →
      cNorm (fundamentalCell n) r (periodicLift (extendToTorus D f)) ≤
        C * cNorm (D.core n) r f := by
  obtain ⟨C, hC, hb⟩ := (extensionParameters D).exists_cNorm_seeleyExtension_le r
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖entryInsertion i j‖ * C * ‖entryMap i j‖,
    Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg
      (fun j _ ↦ mul_nonneg (mul_nonneg (norm_nonneg _) hC.le) (norm_nonneg _))), ?_⟩
  intro f hf
  have hsub : D.core n ⊆ D.chart n :=
    closedBall_subset_ball D.coreRadius_lt_chartRadius
  have he := contDiff_tensorExtension D (hf.mono hsub)
  have hentry (i j : Fin n) : ContDiffOn ℝ ∞ (entryMap i j ∘ f) (D.chart n) :=
    (entryMap i j).contDiff.comp_contDiffOn hf
  have hscalar (i j : Fin n) :
      cNorm (fundamentalCell n) r (entryMap i j ∘ tensorExtension D f) ≤
        C * (‖entryMap i j‖ * cNorm (D.core n) r f) := by
    have hmap := (extensionParameters D).seeleyExtension_map (entryMap i j).toLinearMap f
    change (extensionParameters D).seeleyExtension (entryMap i j ∘ f) =
      entryMap i j ∘ tensorExtension D f at hmap
    rw [← hmap]
    apply (cNorm_seeleyExtension_cell_le_univ D r ((hentry i j).mono hsub)).trans
    apply (hb _ ((hentry i j).mono hsub)).trans
    rw [closedBallCNorm_eq_core D (hentry i j) r]
    exact mul_le_mul_of_nonneg_left
      (cNorm_postLinear_local (isCompact_closedBall _ _) r (entryMap i j)
        (fun x hx ↦ (hf.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).of_le (by simp))) hC.le
  rw [cNorm_periodicLift_extendToTorus_eq]
  have hsplit : tensorExtension D f = fun x ↦
      ∑ i : Fin n, ∑ j : Fin n,
        entryInsertion i j (entryMap i j (tensorExtension D f x)) := by
    funext x
    exact (sum_entryInsertion _).symm
  calc
    _ = cNorm (fundamentalCell n) r (fun x ↦ ∑ i : Fin n, ∑ j : Fin n,
        entryInsertion i j (entryMap i j (tensorExtension D f x))) := congrArg _ hsplit
    _ ≤ ∑ i : Fin n, cNorm (fundamentalCell n) r (fun x ↦ ∑ j : Fin n,
        entryInsertion i j (entryMap i j (tensorExtension D f x))) :=
      cNorm_sum_le _ (isCompact_fundamentalCell n) (fun i _ ↦
        ContDiff.sum (fun j _ ↦ ((entryInsertion i j).contDiff.comp
          ((entryMap i j).contDiff.comp he)).of_le (by simp)))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, cNorm (fundamentalCell n) r
        (entryInsertion i j ∘ (entryMap i j ∘ tensorExtension D f)) := by
      apply Finset.sum_le_sum
      intro i _
      exact cNorm_sum_le _ (isCompact_fundamentalCell n) (fun j _ ↦
        ((entryInsertion i j).contDiff.comp
          ((entryMap i j).contDiff.comp he)).of_le (by simp))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        (‖entryInsertion i j‖ * C * ‖entryMap i j‖) * cNorm (D.core n) r f := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖entryInsertion i j‖ *
            cNorm (fundamentalCell n) r (entryMap i j ∘ tensorExtension D f) :=
          cNorm_postLinear_local (isCompact_fundamentalCell n) r (entryInsertion i j)
            (fun _ _ ↦ ((entryMap i j).contDiff.comp he).contDiffAt.of_le (by simp))
        _ ≤ ‖entryInsertion i j‖ * (C * (‖entryMap i j‖ * cNorm (D.core n) r f)) :=
          mul_le_mul_of_nonneg_left (hscalar i j) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_mul]

end JanetCartan.DefectSmoothing
