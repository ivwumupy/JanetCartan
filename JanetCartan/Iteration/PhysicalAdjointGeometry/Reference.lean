module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Difference
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.ReferenceJoint

/-!
# Exact frozen transverse coefficient

The reference phase is the original affine Hamilton phase `t H(ζ) + y · ζ`.
Its actual averaged transverse mixed transpose is the identity for every
admissible displacement, not just at zero displacement. This closes the base
inverse used by the current-phase comparison in `new:lem:mean-recurrence`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace JanetCartan.PhysicalAdjointGeometry
open FullPhaseCharts.Comparison

variable {m : ℕ}

/-- The complete adapted physical spacetime, with its Hilbert norm. -/
abbrev Spacetime (m : ℕ) := WithLp 2 (ℝ × Euclidean m)

/-- Original transverse inclusion; the remaining physical coordinate is still
part of every ambient derivative (`app:ch_seed:prop:seed-phase-charts`). -/
def transverseInsertion : Euclidean m →L[ℝ] Spacetime m :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean m)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ ℝ (Euclidean m))

@[simp] theorem transverseInsertion_apply (h : Euclidean m) :
    transverseInsertion h = WithLp.toLp 2 ((0 : ℝ), h) := rfl

/-- The original transverse inclusion costs no norm factor. -/
theorem norm_transverseInsertion_le : ‖transverseInsertion (m := m)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simp only [transverseInsertion_apply, WithLp.norm_toLp_snd, one_mul, le_refl]

/-- The averaged frozen covector has the exact affine physical form, at the
same carrier and displacement (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem averagedCovector_reference {H : Euclidean m → ℝ} {D : Set (Euclidean m)}
    (hD : IsOpen D) (hH : ContDiffOn ℝ ∞ H D)
    {ζ δ : Euclidean m} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + t • δ ∈ D)
    (x : Spacetime m) :
    averagedCovector (referencePhase H) (x, ζ, δ) =
      x.ofLp.1 • (∫ t in (0 : ℝ)..1, gradient H (ζ + t • δ)) + x.ofLp.2 := by
  have hS : ContDiffOn ℝ ∞ (referencePhase H) (univ ×ˢ D) :=
    contDiffOn_referencePhase hH (fun _ hp ↦ hp.2)
  have hc : ContinuousOn (fun t : ℝ ↦ gradient H (ζ + t • δ)) (Icc 0 1) :=
    (continuousOn_gradient_of_contDiffOn hD (hH.of_le (by simp))).comp
      (by fun_prop) hseg
  unfold averagedCovector
  calc
    _ = ∫ t in (0 : ℝ)..1, (x.ofLp.1 • gradient H (ζ + t • δ) + x.ofLp.2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [covectorGradient_eq_gradient
        ((hS.contDiffAt ((isOpen_univ.prod hD).mem_nhds
          ⟨mem_univ x, hseg t (by simpa using ht)⟩)).differentiableAt (by simp))]
      exact gradient_referencePhase_covector
        ((hH.contDiffAt (hD.mem_nhds (hseg t (by simpa using ht)))).differentiableAt (by simp)) x
    _ = _ := by
      have his : IntervalIntegrable (fun t : ℝ ↦ x.ofLp.1 • gradient H (ζ + t • δ)) volume 0 1 := by
        exact (hc.const_smul x.ofLp.1).intervalIntegrable_of_Icc (μ := volume) zero_le_one
      rw [intervalIntegral.integral_add his intervalIntegrable_const,
        intervalIntegral.integral_smul]
      simp

/-- The actual frozen averaged transverse mixed transpose is exactly the
identity for every admissible shift. Its differentiability input is furnished
by `contDiffOn_averagedCovector` on the original phase buffer
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem mixedTranspose_reference {H : Euclidean m → ℝ} {D : Set (Euclidean m)}
    (hD : IsOpen D) (hH : ContDiffOn ℝ ∞ H D) (q : Point (Spacetime m) m)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, q.2.1 + t • q.2.2 ∈ D)
    (hY : DifferentiableAt ℝ (averagedCovector (referencePhase H)) q) :
    mixedTranspose transverseInsertion (averagedCovector (referencePhase H)) q = 1 := by
  let Z : Euclidean m := ∫ t in (0 : ℝ)..1, gradient H (q.2.1 + t • q.2.2)
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean m)).toContinuousLinearMap
  let A : Spacetime m →L[ℝ] Euclidean m :=
    ((ContinuousLinearMap.fst ℝ ℝ (Euclidean m)).comp e).smulRight Z +
      (ContinuousLinearMap.snd ℝ ℝ (Euclidean m)).comp e
  have he : (fun x ↦ averagedCovector (referencePhase H) (x, q.2)) = A := by
    funext x
    exact averagedCovector_reference hD hH hseg x
  have hd := hY.hasFDerivAt.comp q.1
    ((hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) q.2 q.1))
  dsimp only [Function.comp_def, id_eq] at hd
  apply ContinuousLinearMap.ext
  intro h
  calc
    _ = fderiv ℝ (fun x ↦ averagedCovector (referencePhase H) (x, q.2)) q.1
        (transverseInsertion h) := by
      rw [hd.fderiv]
      simp [mixedTranspose, physicalInjection]
    _ = A (transverseInsertion h) := by rw [he, A.fderiv]
    _ = h := by simp [A, e, transverseInsertion]

end JanetCartan.PhysicalAdjointGeometry
