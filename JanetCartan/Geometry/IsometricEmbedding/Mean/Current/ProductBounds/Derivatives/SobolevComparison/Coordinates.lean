module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.Jets

/-!
# Coordinate evaluations of periodic jets

The bridge between the actual multilinear jets and Cartesian derivative energies
for `main:lem:mean-recurrence` in paper.tex.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.CurrentMean

section Normed
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- `main:lem:mean-recurrence`: coordinate evaluations of the actual jet are
ordered Cartesian derivatives. This identifies the derivatives used by Parseval. -/
theorem periodicJet_apply_basis {f : Torus d → F} (hf : IsSmoothPeriodic f)
    (r : ℕ) (is : Fin r → Fin d) (x : Torus d) :
    periodicJet r f x (fun a ↦ EuclideanSpace.single (is a) 1) =
      periodicCoordinateDerivList (List.ofFn is) f x := by
  induction r generalizing x with
  | zero => simp [periodicJet, periodicCoordinateDerivList]
  | succ r ih =>
    rw [periodicJet, continuousMultilinearCurryLeftEquiv_symm_apply,
      periodicFDeriv_single, List.ofFn_succ, periodicCoordinateDerivList]
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin r ↦ EuclideanSpace ℝ (Fin d)) F
      (fun a ↦ EuclideanSpace.single (is a.succ) 1)
    have he : (fun y ↦ L (periodicJet r f y)) =
        periodicCoordinateDerivList (List.ofFn (fun a ↦ is a.succ)) f :=
      funext (ih (fun a ↦ is a.succ))
    have h := congr_fun (periodicCoordinateDeriv_comp_clm
      (periodicJet_spec hf r).1 L (is 0)) x
    rw [he] at h
    exact h.symm

/-- `main:lem:mean-recurrence`: evaluating on coordinate unit vectors costs at most
the operator norm of the jet, for the reverse Sobolev comparison. -/
theorem norm_periodicCoordinateDerivList_le_periodicJet {f : Torus d → F}
    (hf : IsSmoothPeriodic f) (is : List (Fin d)) (x : Torus d) :
    ‖periodicCoordinateDerivList is f x‖ ≤ ‖periodicJet is.length f x‖ := by
  conv_lhs => rw [← List.ofFn_get is]
  rw [← periodicJet_apply_basis hf]
  simpa using (periodicJet is.length f x).le_opNorm_mul_prod_of_le
    (b := fun _ ↦ (1 : ℝ)) (m := fun a ↦ EuclideanSpace.single (is.get a) 1)
    (fun a ↦ by simp [EuclideanSpace.single, PiLp.norm_single])

/-- `main:lem:mean-recurrence`: expansion in the Euclidean coordinate basis bounds
the operator norm by the sum of coordinate evaluations. Used by
`periodicL2Norm_periodicJet_le_sobolev`. -/
theorem norm_multilinear_le_sum_basis (r : ℕ)
    (A : (EuclideanSpace ℝ (Fin d)) [×r]→L[ℝ] F) :
    ‖A‖ ≤ ∑ is : Fin r → Fin d, ‖A (fun a ↦ EuclideanSpace.single (is a) 1)‖ := by
  classical
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  intro v
  have hv : v = fun a ↦ ∑ i : Fin d, (v a i) • EuclideanSpace.single i 1 := by
    funext a
    simpa using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v a)).symm
  calc
    ‖A v‖ = ‖∑ is : Fin r → Fin d,
        (∏ a, v a (is a)) • A (fun a ↦ EuclideanSpace.single (is a) 1)‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp_rw [A.map_smul_univ]
    _ ≤ ∑ is : Fin r → Fin d,
        ‖(∏ a, v a (is a)) • A (fun a ↦ EuclideanSpace.single (is a) 1)‖ :=
      norm_sum_le _ _
    _ ≤ (∑ is : Fin r → Fin d, ‖A (fun a ↦ EuclideanSpace.single (is a) 1)‖) *
        ∏ a, ‖v a‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro is _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      gcongr with a
      exact PiLp.norm_apply_le (v a) (is a)

open MeasureTheory

omit [NormedSpace ℝ F] in
/-- `main:lem:mean-recurrence`: a continuous pointwise norm majorant controls L².
Used to pass from coordinate derivative energies to jet energies. -/
theorem periodicL2Norm_le_of_norm_le {G : Type*} [NormedAddCommGroup G]
    (f : Torus d → F) (g : Torus d → G) (hg : Continuous g)
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : periodicL2Norm f ≤ periodicL2Norm g := by
  apply Real.sqrt_le_sqrt
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
    ((hg.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (h x) 2))

/-- `main:lem:mean-recurrence`: each ordered coordinate derivative energy is
bounded by the actual jet energy of the same order. -/
theorem periodicL2Norm_coordinateDerivList_le_periodicJet {f : Torus d → F}
    (hf : IsSmoothPeriodic f) (is : List (Fin d)) :
    periodicL2Norm (periodicCoordinateDerivList is f) ≤
      periodicL2Norm (periodicJet is.length f) :=
  periodicL2Norm_le_of_norm_le _ _ (periodicJet_spec hf _).1.1
    (norm_periodicCoordinateDerivList_le_periodicJet hf is)

end Normed

end JanetCartan.CurrentMean
