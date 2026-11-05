module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Symbols

/-!
# Finite derivative budgets for freezing

For `app:ch_background:prop:bg-frame`, Step 3, the actual Taylor integral loses
exactly one primitive derivative. The bounds retain the fixed physical cutoff.
Here the symbol is a fixed smooth extension of the locally defined, low-frequency
completed symbol. Its existence and its primitive budgets are inputs to be
supplied by the normal-reduction construction, before choosing the radius `r`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumNormal

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin d)

private def freezingSegmentMap (t : ℝ) : (E × E) →L[ℝ] E × E :=
  (t • ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)

private theorem norm_freezingSegmentMap_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖freezingSegmentMap (d := d) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖(t • p.1, p.2)‖ ≤ 1 * ‖p‖
  rw [one_mul, Prod.norm_def]
  refine max_le ?_ (norm_snd_le p)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_fst_le p)

private theorem fderiv_physical_eq (a : E → E → F)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (p : E × E) :
    fderiv ℝ (fun z ↦ a z p.2) p.1 =
      (fderiv ℝ (Function.uncurry a) p).comp (ContinuousLinearMap.inl ℝ E E) := by
  have hi : HasFDerivAt (fun z : E ↦ (z, p.2))
      (ContinuousLinearMap.inl ℝ E E) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  exact (((ha.differentiable (by simp)) p).hasFDerivAt.comp p.1 hi).fderiv

private theorem contDiff_freezingDerivative (a : E → E → F)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) :
    ContDiff ℝ ∞ (fun p : E × E ↦ fderiv ℝ (fun z ↦ a z p.2) p.1) := by
  simp_rw [fderiv_physical_eq a ha]
  exact (ha.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

private theorem contDiff_freezingIntegrand (a : E → E → F)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (i : Fin d) :
    ContDiff ℝ ∞ (fun q : (E × E) × ℝ ↦
      fderiv ℝ (fun z ↦ a z q.1.2) (q.2 • q.1.1)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
  ((contDiff_freezingDerivative a ha).comp
    ((contDiff_snd.smul contDiff_fst.fst).prodMk contDiff_fst.snd)).clm_apply contDiff_const

/-- `app:ch_background:prop:bg-frame`, Step 3: the constructed Taylor symbols
are jointly smooth in physical position and frequency. -/
theorem contDiff_freezingTaylorCoefficient (a : E → E → F)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (i : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (freezingTaylorCoefficient a i)) :=
  contDiff_unitIntervalIntegral _ (contDiff_freezingIntegrand a ha i)

/-- `app:ch_background:prop:bg-frame`, Step 3: fixed smooth physical cutoffs
preserve joint smoothness of the actual coefficient symbols. -/
theorem contDiff_extendedFreezingTaylorCoefficient (a : E → E → F) (β : E → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hβ : ContDiff ℝ ∞ β) (i : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (extendedFreezingTaylorCoefficient a β i)) :=
  (hβ.comp contDiff_fst).smul (contDiff_freezingTaylorCoefficient a ha i)

/-- `app:ch_background:prop:bg-frame`, Step 3: each joint derivative of the
literal Taylor coefficient costs one derivative of the primitive symbol, with
constant one. No bound on a proposed Taylor operator is assumed. -/
theorem norm_iteratedFDeriv_freezingTaylorCoefficient_le (a : E → E → F)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (i : Fin d) (p : E × E)
    (n : ℕ) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) (Function.uncurry a) (t • p.1, p.2)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (Function.uncurry (freezingTaylorCoefficient a i)) p‖ ≤ M := by
  apply norm_iteratedFDeriv_unitIntervalIntegral_le n _ (contDiff_freezingIntegrand a ha i)
  intro t ht
  let D := fun q : E × E ↦ fderiv ℝ (fun z ↦ a z q.2) q.1
  have hD : ContDiff ℝ ∞ D := contDiff_freezingDerivative a ha
  have happly := norm_iteratedFDeriv_clm_apply_const
    (c := EuclideanSpace.basisFun (Fin d) ℝ i) (x := p)
    (hD.comp (freezingSegmentMap t).contDiff).contDiffAt
    (show (n : WithTop ℕ∞) ≤ ∞ by simp)
  simp only [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one, one_mul] at happly
  apply happly.trans
  have hcomp := norm_iteratedFDeriv_comp_linear_le (freezingSegmentMap t) D hD n p
  apply hcomp.trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_freezingSegmentMap_le t ht))).trans
  dsimp [D]
  simp_rw [fderiv_physical_eq a ha]
  have hinl : ‖ContinuousLinearMap.inl ℝ E E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [Prod.norm_def]
  exact (norm_iteratedFDeriv_partialFDeriv_le (ContinuousLinearMap.inl ℝ E E)
    (Function.uncurry a) ha n _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hinl).trans (hM t ht))

/-- `app:ch_background:prop:bg-frame`, Step 3: the finite Leibniz budget for
the fixed extension. Its constants depend on the fixed cutoff and primitive
symbol jets, and are chosen independently of the eventual small support radius. -/
theorem norm_iteratedFDeriv_extendedFreezingTaylorCoefficient_le
    (a : E → E → F) (β : E → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hβ : ContDiff ℝ ∞ β)
    (i : Fin d) (p : E × E) (n : ℕ) (M : ℕ → ℝ)
    (hM : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry a) (t • p.1, p.2)‖ ≤ M k) :
    ‖iteratedFDeriv ℝ n (Function.uncurry (extendedFreezingTaylorCoefficient a β i)) p‖ ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        ‖iteratedFDeriv ℝ k β p.1‖ * M (n - k) := by
  apply (norm_iteratedFDeriv_smul_le (hβ.comp contDiff_fst)
    (contDiff_freezingTaylorCoefficient a ha i) p (by simp)).trans
  apply Finset.sum_le_sum
  intro k _
  have hproj : ‖iteratedFDeriv ℝ k (fun q : E × E ↦ β q.1) p‖ ≤
      ‖iteratedFDeriv ℝ k β p.1‖ := by
    have hfst : ‖ContinuousLinearMap.fst ℝ E E‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q ↦ by simpa using norm_fst_le q)
    exact (norm_iteratedFDeriv_comp_linear_le (ContinuousLinearMap.fst ℝ E E) β hβ k p).trans
      (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hfst))
  calc
    _ ≤ (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k β p.1‖ *
        ‖iteratedFDeriv ℝ (n - k) (Function.uncurry (freezingTaylorCoefficient a i)) p‖ := by
      gcongr
      exact hproj
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_freezingTaylorCoefficient_le a ha i p (n - k) _
        (hM (n - k) (Nat.sub_le _ _))) (by positivity)

end JanetCartan.ContinuumNormal
