module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.ZeroOrder
public import JanetCartan.Analysis.Fourier.Periodic.Bernstein.Derivatives
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# Periodic jets for the mixed mean estimate

Actual multilinear derivatives on the unit torus, used by the integer product
estimate in `main:lem:mean-recurrence`. The norm is the operator norm on jets;
matrix values retain their Frobenius norm. No Fourier support premise is needed.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.CurrentMean

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:mean-recurrence`: the actual order `r` Fréchet derivative,
descended to the unit torus by the canonical currying isometries. -/
def periodicJet : (r : ℕ) → (Torus d → F) →
    Torus d → (EuclideanSpace ℝ (Fin d)) [×r]→L[ℝ] F
  | 0, f => fun x ↦ (continuousMultilinearCurryFin0 ℝ
      (EuclideanSpace ℝ (Fin d)) F).symm (f x)
  | r + 1, f => fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (r + 1) ↦ EuclideanSpace ℝ (Fin d)) F).symm
        (periodicFDeriv (periodicJet r f) x)

/-- `main:lem:mean-recurrence`: the descended jet is smooth and lifts to
the ordinary iterated Fréchet derivative. This is the interface consumed by
the weighted Leibniz and derivative-energy estimates. -/
theorem periodicJet_spec {f : Torus d → F} (hf : IsSmoothPeriodic f) (r : ℕ) :
    IsSmoothPeriodic (periodicJet r f) ∧
      periodicLift (periodicJet r f) = iteratedFDeriv ℝ r (periodicLift f) := by
  induction r with
  | zero =>
    let A := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin d)) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    exact ⟨hf.comp_clm A, rfl⟩
  | succ r ih =>
    let A := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (r + 1) ↦ EuclideanSpace ℝ (Fin d)) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨ih.1.fderiv.comp_clm A, ?_⟩
    change A ∘ periodicLift (periodicFDeriv (periodicJet r f)) = _
    rw [periodicLift_fderiv ih.1, ih.2, iteratedFDeriv_succ_eq_comp_left]
    rfl

/-- `main:lem:mean-recurrence`: every torus point has a Euclidean lift;
used to transfer the ordinary Leibniz formula to periodic jets. -/
theorem exists_torusQuotient_eq (x : Torus d) :
    ∃ y : EuclideanSpace ℝ (Fin d), torusQuotient y = x := by
  classical
  choose a ha using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  exact ⟨WithLp.toLp 2 a, funext ha⟩

/-- `main:lem:mean-recurrence`: the lower factor's derivative of order `r`
costs precisely its `Cʳ` norm, with no derivative loss. -/
theorem norm_periodicJet_le_cNorm {f : Torus d → F}
    (hf : IsSmoothPeriodic f) (r : ℕ) (x : Torus d) :
    ‖periodicJet r f x‖ ≤ cNorm (fundamentalCell d) r (periodicLift f) := by
  obtain ⟨y, rfl⟩ := exists_torusQuotient_eq x
  change ‖periodicLift (periodicJet r f) y‖ ≤ _
  rw [(periodicJet_spec hf r).2]
  exact norm_iteratedFDeriv_periodicLift_le f r
    (fun z hz ↦ norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell d)
      (hf.2.of_le (by simp)) hz le_rfl) y

end JanetCartan.CurrentMean
