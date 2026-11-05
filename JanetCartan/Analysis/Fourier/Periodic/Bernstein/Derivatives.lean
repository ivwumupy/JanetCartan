module

public import JanetCartan.Analysis.Fourier.Periodic.Deriv

/-!
# Band-limited periodic derivatives

For paper.tex, `main:lem:history`, the Fréchet derivative descends to the unit
torus and preserves exact Fourier support. Iteration and the canonical currying
isometries give the same assertions for every multilinear derivative.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`, `app:not:fourier`: the Fréchet derivative on the torus,
assembled from the shared Cartesian derivatives. -/
def periodicFDeriv (f : Torus n → F) (x : Torus n) : EuclideanSpace ℝ (Fin n) →L[ℝ] F :=
  ∑ i : Fin n, (EuclideanSpace.proj i).smulRight (periodicCoordinateDeriv i f x)

/-- `app:not:fourier`: evaluation on a coordinate vector recovers the coordinate derivative. -/
theorem periodicFDeriv_single (f : Torus n → F) (x : Torus n) (i : Fin n) :
    periodicFDeriv f x (EuclideanSpace.single i 1) = periodicCoordinateDeriv i f x := by
  classical
  simp [periodicFDeriv, sum_apply, eq_comm]

/-- `main:lem:history`: the torus derivative lifts to the ordinary Fréchet derivative. -/
theorem periodicLift_fderiv {f : Torus n → F} (hf : IsSmoothPeriodic f) :
    periodicLift (periodicFDeriv f) = fderiv ℝ (periodicLift f) := by
  funext x
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro i
  simpa only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, periodicLift, Function.comp_apply, periodicFDeriv_single]
    using congr_fun (periodicLift_coordinateDeriv hf.2 i) x

/-- `main:lem:history`: the torus Fréchet derivative preserves smooth periodicity. -/
theorem IsSmoothPeriodic.fderiv {f : Torus n → F} (hf : IsSmoothPeriodic f) :
    IsSmoothPeriodic (periodicFDeriv f) := by
  constructor
  · apply continuous_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n)) F
      (EuclideanSpace.proj i)).continuous.comp (hf.coordinateDeriv i).1
  · rw [periodicLift_fderiv hf]
    exact hf.2.fderiv_right (by simp)

variable [CompleteSpace F]

/-- `main:lem:history`: Cartesian differentiation preserves exact Fourier support. -/
theorem HasFourierSupport.coordinateDeriv {f : Torus n → F} {L : ℝ}
    (hs : HasFourierSupport L f) (hf : IsSmoothPeriodic f) (i : Fin n) :
    HasFourierSupport L (periodicCoordinateDeriv i f) := by
  intro k hk
  rw [periodicFourierCoeff_coordinateDeriv_smul hf, hs k hk]
  simp

/-- `main:lem:history`: the full Fréchet derivative preserves exact Fourier support,
as follows by testing its Fourier coefficients on the coordinate basis. -/
theorem HasFourierSupport.fderiv {f : Torus n → F} {L : ℝ}
    (hs : HasFourierSupport L f) (hf : IsSmoothPeriodic f) :
    HasFourierSupport L (periodicFDeriv f) := by
  intro k hk
  have heq (i : Fin n) := periodicFourierCoeff_map
    (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i 1)) hf.fderiv.1 k
  simp only [ContinuousLinearMap.apply_apply, periodicFDeriv_single] at heq
  have he (i : Fin n) := (heq i).symm.trans (hs.coordinateDeriv hf i k hk)
  apply Prod.ext
  · apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    simpa using congrArg Prod.fst (he i)
  · apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    simpa using congrArg Prod.snd (he i)

/-- `main:lem:history`: a real continuous linear map preserves exact Fourier support. -/
theorem HasFourierSupport.comp_clm {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : Torus n → F} {L : ℝ} (hs : HasFourierSupport L f) (hf : Continuous f)
    (A : F →L[ℝ] G) : HasFourierSupport L (fun x ↦ A (f x)) := by
  intro k hk
  rw [periodicFourierCoeff_map A hf, hs k hk]
  simp

/-- `main:lem:history`: every iterated derivative has a smooth periodic lift with
the original Fourier support. No additional analytic premise is required. -/
theorem IsSmoothPeriodic.exists_iteratedFDeriv {f : Torus n → F} {L : ℝ}
    (hf : IsSmoothPeriodic f) (hs : HasFourierSupport L f) (j : ℕ) :
    ∃ g : Torus n → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F,
      IsSmoothPeriodic g ∧ HasFourierSupport L g ∧
        periodicLift g = iteratedFDeriv ℝ j (periodicLift f) := by
  induction j with
  | zero =>
    let A := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n)) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    exact ⟨fun x ↦ A (f x), hf.comp_clm A, hs.comp_clm hf.1 A, rfl⟩
  | succ j ih =>
    obtain ⟨g, hg, hgs, hglift⟩ := ih
    let A := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin n)) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨fun x ↦ A (periodicFDeriv g x), hg.fderiv.comp_clm A,
      (hgs.fderiv hg).comp_clm hg.fderiv.1 A, ?_⟩
    change A ∘ periodicLift (periodicFDeriv g) = _
    rw [periodicLift_fderiv hg, hglift, iteratedFDeriv_succ_eq_comp_left]
    rfl

end JanetCartan
