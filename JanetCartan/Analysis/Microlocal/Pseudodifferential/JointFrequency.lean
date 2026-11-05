module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointTaylor

/-!
# Joint derivative estimates for frequency divergence

The contraction in `app:ch_regular_base:eq:actual-pdo-remainder` costs one extra
joint derivative, with explicit dimension and unit-frequency normalization.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the frequency derivative is a restriction of the joint derivative. -/
theorem fderiv_frequency_eq_joint (B : (V × V × V) → V →L[ℝ] F)
    (hB : ContDiff ℝ ∞ B) (p : V × V × V) :
    fderiv ℝ (fun ξ ↦ B (p.1, p.2.1, ξ)) p.2.2 =
      (fderiv ℝ B p).comp frequencyCoordinateInclusion := by
  have hi : HasFDerivAt (fun ξ : V ↦ (p.1, p.2.1, ξ))
      frequencyCoordinateInclusion p.2.2 :=
    (hasFDerivAt_const p.1 p.2.2).prodMk
      ((hasFDerivAt_const p.2.1 p.2.2).prodMk (hasFDerivAt_id p.2.2))
  exact ((hB.differentiable (by simp) p).hasFDerivAt.comp p.2.2 hi).fderiv

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the actual frequency contraction expressed in joint variables. -/
theorem frequencyDivergence_eq_joint {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : (V × V × V) → V →L[ℝ] F) (hB : ContDiff ℝ ∞ B) :
    (fun p : V × V × V ↦ frequencyDivergence b (fun ξ ↦ B (p.1, p.2.1, ξ)) p.2.2) =
      fun p ↦ ∑ j, (fderiv ℝ B p (frequencyCoordinateInclusion (b j))) (b j) := by
  funext p
  unfold frequencyDivergence
  rw [fderiv_frequency_eq_joint B hB]
  rfl

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: joint smoothness of the finite frequency contraction. -/
theorem contDiff_frequencyDivergence_joint {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : (V × V × V) → V →L[ℝ] F) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun p : V × V × V ↦ frequencyDivergence b (fun ξ ↦ B (p.1, p.2.1, ξ)) p.2.2) := by
  rw [frequencyDivergence_eq_joint b B hB]
  apply ContDiff.sum
  intro j _
  exact ((hB.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply contDiff_const

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the joint contraction costs exactly one derivative. -/
theorem norm_iteratedFDeriv_frequencyDivergence_joint_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : (V × V × V) → V →L[ℝ] F)
    (hB : ContDiff ℝ ∞ B) (n : ℕ) (p : V × V × V) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦
      frequencyDivergence b (fun ξ ↦ B (q.1, q.2.1, ξ)) q.2.2) p‖ ≤
      Fintype.card ι * ‖iteratedFDeriv ℝ (n + 1) B p‖ := by
  rw [frequencyDivergence_eq_joint b B hB]
  have hD := hB.fderiv_right (m := ∞) (by simp)
  have hj (j : ι) : ContDiff ℝ (n : WithTop ℕ∞) (fun q ↦
      (fderiv ℝ B q (frequencyCoordinateInclusion (b j))) (b j)) :=
    ((hD.clm_apply contDiff_const).clm_apply contDiff_const).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hj j).contDiffAt)]
  calc
    _ ≤ ∑ j, ‖iteratedFDeriv ℝ n (fun q ↦
        (fderiv ℝ B q (frequencyCoordinateInclusion (b j))) (b j)) p‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, ‖iteratedFDeriv ℝ (n + 1) B p‖ := by
      apply Finset.sum_le_sum
      intro j _
      have h₁ := norm_iteratedFDeriv_clm_apply_const (c := b j) (x := p)
        (hD.clm_apply (g := fun _ ↦ frequencyCoordinateInclusion (b j)) contDiff_const).contDiffAt
        (show (n : WithTop ℕ∞) ≤ ∞ by simp)
      have h₂ := norm_iteratedFDeriv_clm_apply_const
        (c := frequencyCoordinateInclusion (b j)) (x := p) hD.contDiffAt
        (show (n : WithTop ℕ∞) ≤ ∞ by simp)
      simp only [frequencyCoordinateInclusion, ContinuousLinearMap.prod_apply,
        zero_apply, ContinuousLinearMap.id_apply, Prod.norm_def,
        norm_zero, b.norm_eq_one, max_eq_right zero_le_one, one_mul,
        norm_iteratedFDeriv_fderiv] at h₁ h₂
      exact h₁.trans h₂
    _ = _ := by simp [nsmul_eq_mul]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the joint contraction bound includes the unit-torus normalization. -/
theorem norm_iteratedFDeriv_normalizedFrequencyDivergence_joint_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : (V × V × V) → V →L[ℝ] F) (hB : ContDiff ℝ ∞ B)
    (n : ℕ) (p : V × V × V) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦
      normalizedFrequencyDivergence b (fun ξ ↦ B (q.1, q.2.1, ξ)) q.2.2) p‖ ≤
      ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ‖iteratedFDeriv ℝ (n + 1) B p‖ := by
  let L : F →L[ℝ] F := (2 * Real.pi * Complex.I)⁻¹ • ContinuousLinearMap.id ℝ F
  have hD := contDiff_frequencyDivergence_joint b B hB
  change ‖iteratedFDeriv ℝ n (L ∘ (fun q : V × V × V ↦
    frequencyDivergence b (fun ξ ↦ B (q.1, q.2.1, ξ)) q.2.2)) p‖ ≤ _
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦
        frequencyDivergence b (fun ξ ↦ B (q.1, q.2.1, ξ)) q.2.2) p‖ :=
      L.norm_iteratedFDeriv_comp_left hD.contDiffAt (by simp)
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ *
        (Fintype.card ι * ‖iteratedFDeriv ℝ (n + 1) B p‖) := by
      gcongr
      · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
      · exact norm_iteratedFDeriv_frequencyDivergence_joint_le b B hB n p
    _ = _ := by ring
end JanetCartan.Pseudodifferential
