module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Forward
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Differential
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The mixed differential in the transport segment integral

The integrand in `app:ch_background:eq:bg-Psi`, retaining both positions,
carrier coordinates and transverse covector. These identities are consumed by
`ForwardJets` to derive forward bounds from `app:ch_background:eq:bg-mixed-input`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Segment evaluation in the primitive domain of `Y`
(`app:ch_background:eq:bg-Psi`). -/
def transportSegmentInput (n : ℕ) (t : ℝ) :
    InputVariables n →L[ℝ] Euclidean n × (ℝ × Euclidean 2) :=
  let xy := ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n)
    ((ℝ × Euclidean 2) × Euclidean (n - 1))
  let x := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp xy
  let y := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp xy
  let z := (ContinuousLinearMap.fst ℝ (ℝ × Euclidean 2) (Euclidean (n - 1))).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n)
      ((ℝ × Euclidean 2) × Euclidean (n - 1)))
  (y + t • (x - y)).prod z

/-- Evaluation formula for the primitive segment (`app:ch_background:eq:bg-Psi`). -/
@[simp] theorem transportSegmentInput_apply (n : ℕ) (t : ℝ) (p : InputVariables n) :
    transportSegmentInput n t p = (p.1.2 + t • (p.1.1 - p.1.2), p.2.1) := rfl

/-- Uniform operator norm for the segment evaluation (`app:ch_background:eq:bg-Psi`). -/
theorem norm_transportSegmentInput_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖transportSegmentInput n t‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  change max ‖p.1.2 + t • (p.1.1 - p.1.2)‖ ‖p.2.1‖ ≤ 3 * ‖p‖
  have hx := (norm_fst_le p.1).trans (norm_fst_le p)
  have hy := (norm_snd_le p.1).trans (norm_fst_le p)
  have hz := (norm_fst_le p.2).trans (norm_snd_le p)
  apply max_le
  · calc
      _ ≤ ‖p.1.2‖ + ‖t • (p.1.1 - p.1.2)‖ := norm_add_le _ _
      _ = ‖p.1.2‖ + t * ‖p.1.1 - p.1.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖p.1.2‖ + 1 * (‖p.1.1‖ + ‖p.1.2‖) := by
        exact add_le_add le_rfl (mul_le_mul ht.2 (norm_sub_le _ _)
          (norm_nonneg _) zero_le_one)
      _ ≤ 3 * ‖p‖ := by linarith
  · nlinarith [norm_nonneg p]

/-- Restrict the full mixed differential to physical directions and transpose
it against the transverse covector (`app:ch_background:eq:bg-Psi`). -/
def transportSpatialAdjoint (n : ℕ) :
    ((Euclidean n × (ℝ × Euclidean 2)) →L[ℝ] Euclidean (n - 1)) →L[ℝ]
      Euclidean (n - 1) →L[ℝ] Euclidean n :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclidean n)
    (F := Euclidean (n - 1))).toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    ((ContinuousLinearMap.compL ℝ (Euclidean n)
      (Euclidean n × (ℝ × Euclidean 2)) (Euclidean (n - 1))).flip
        (ContinuousLinearMap.inl ℝ (Euclidean n) (ℝ × Euclidean 2)))

/-- The differential pairing is a contraction (`app:ch_background:eq:bg-Psi`). -/
theorem norm_transportSpatialAdjoint_le (n : ℕ) : ‖transportSpatialAdjoint n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖ContinuousLinearMap.adjoint
    (A.comp (ContinuousLinearMap.inl ℝ (Euclidean n) (ℝ × Euclidean 2)))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa using A.le_opNorm (v, 0)

/-- The bilinear expression is the literal physical gradient, with no forward
regularity assumed (`app:ch_background:eq:bg-Psi`). -/
theorem transportSpatialAdjoint_fderiv
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {z : Euclidean n × (ℝ × Euclidean 2)} (hY : DifferentiableAt ℝ Y z)
    (η : Euclidean (n - 1)) :
    transportSpatialAdjoint n (fderiv ℝ Y z) η =
      gradient (fun x ↦ inner ℝ (Y (x, z.2)) η) z.1 := by
  have hd := hY.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have hi := (innerSL ℝ η).hasFDerivAt.comp z.1 hd
  have he : (fun x ↦ inner ℝ η (Y (x, z.2))) =
      (fun x ↦ inner ℝ (Y (x, z.2)) η) := by funext x; exact real_inner_comm _ _
  change HasFDerivAt (fun x ↦ inner ℝ η (Y (x, z.2))) _ z.1 at hi
  rw [he] at hi
  rw [hi.hasGradientAt.gradient]
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ v η

/-- The full mixed integrand of `app:ch_background:eq:bg-Psi`. -/
def transportSegmentGradient
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (t : ℝ) (p : InputVariables n) : Euclidean n :=
  transportSpatialAdjoint n (fderiv ℝ Y (transportSegmentInput n t p)) p.2.2

/-- Mixed smoothness of the integrand follows from that of `Y`
(`app:ch_background:eq:bg-mixed-input`). -/
theorem transportSegmentGradient_contDiffAt
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {z : ℝ × InputVariables n}
    (hY : ContDiffAt ℝ ∞ Y (transportSegmentInput n z.1 z.2)) :
    ContDiffAt ℝ ∞ (fun w : ℝ × InputVariables n ↦
      transportSegmentGradient Y w.1 w.2) z := by
  have hs : ContDiffAt ℝ ∞ (fun w : ℝ × InputVariables n ↦
      transportSegmentInput n w.1 w.2) z :=
    (contDiffAt_snd.fst.snd.add (contDiffAt_fst.smul
      (contDiffAt_snd.fst.fst.sub contDiffAt_snd.fst.snd))).prodMk contDiffAt_snd.snd.fst
  exact ((transportSpatialAdjoint n).contDiff.contDiffAt.comp z
    ((hY.fderiv_right (m := ∞) (by simp)).comp z hs)).clm_apply contDiffAt_snd.snd.snd

end JanetCartan.ContinuumNormalReduction.TransportSymbol
