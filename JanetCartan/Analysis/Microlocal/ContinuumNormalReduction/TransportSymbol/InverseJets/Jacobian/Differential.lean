module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Restricting the forward differential to the transport slice

The single derivative cost in `app:ch_background:eq:bg-jacobian`.
These estimates are consumed by the absolute-Jacobian shell bounds.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Fixed insertion of slice tangent vectors into the joint input variables
(`app:ch_background:eq:bg-Psi`). -/
def transportSliceInsertion (c : TransportSliceCoordinates n) :
    Euclidean n →L[ℝ] InputVariables n :=
  let S := (ContinuousLinearMap.fst ℝ ℝ (Euclidean (n - 1))).comp
    c.equiv.toContinuousLinearMap
  let H := (ContinuousLinearMap.snd ℝ ℝ (Euclidean (n - 1))).comp
    c.equiv.toContinuousLinearMap
  (0 : Euclidean n →L[ℝ] Euclidean n × Euclidean n).prod
    ((S.prod (0 : Euclidean n →L[ℝ] Euclidean 2)).prod H)

/-- Fixed restriction operator on forward differentials
(`app:ch_background:eq:bg-jacobian`). -/
def transportDifferentialRestriction (c : TransportSliceCoordinates n) :
    (InputVariables n →L[ℝ] Euclidean n) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean n) :=
  (ContinuousLinearMap.compL ℝ (Euclidean n) (InputVariables n) (Euclidean n)).flip
    (transportSliceInsertion c)

/-- The literal slice derivative equals restriction of the full joint
forward derivative. No positions or spectator are frozen in the resulting
field (`app:ch_background:eq:bg-jacobian`). -/
theorem transportSliceDifferential_eq_restriction (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {p : InputVariables n} (hp : DifferentiableAt ℝ (transportAveragedGradient Y) p) :
    transportSliceDifferential c Y p =
      transportDifferentialRestriction c (fderiv ℝ (transportAveragedGradient Y) p) := by
  let z := c.equiv.symm (p.2.1.1, p.2.2)
  have hi : HasFDerivAt
      (fun w : Euclidean n ↦ (p.1, ((c.equiv w).1, p.2.1.2), (c.equiv w).2))
      (transportSliceInsertion c) z :=
    (hasFDerivAt_const p.1 z).prodMk
      (((c.equiv.hasFDerivAt.fst).prodMk (hasFDerivAt_const p.2.1.2 z)).prodMk
        c.equiv.hasFDerivAt.snd)
  have he : (p.1, ((c.equiv z).1, p.2.1.2), (c.equiv z).2) = p := by
    simp [z]
  have houter : HasFDerivAt (transportAveragedGradient Y)
      (fderiv ℝ (transportAveragedGradient Y) p)
      (p.1, ((c.equiv z).1, p.2.1.2), (c.equiv z).2) := he.symm ▸ hp.hasFDerivAt
  exact (houter.comp z hi).fderiv

/-- Joint smoothness of the slice differential follows from joint forward
smoothness on the open chart (`app:ch_background:eq:bg-mixed-input`). -/
theorem transportSliceDifferential_contDiffOn (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hY : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W) :
    ContDiffOn ℝ ∞ (transportSliceDifferential c Y) W := by
  have he : EqOn (transportSliceDifferential c Y)
      (transportDifferentialRestriction c ∘ fderiv ℝ (transportAveragedGradient Y)) W :=
    fun p hp ↦ transportSliceDifferential_eq_restriction c Y
      ((hY.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp))
  intro p hp
  have hh := (transportDifferentialRestriction c).contDiff.contDiffAt.comp p
    ((hY.contDiffAt (hW.mem_nhds hp)).fderiv_right (m := ∞) (by simp))
  exact (hh.congr_of_eventuallyEq
    ((hW.eventually_mem hp).mono (fun q hq ↦ he hq))).contDiffWithinAt

/-- Every joint jet of the actual slice differential costs one forward jet.
This estimate feeds the one-high determinant and reciprocal estimates of
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem norm_iteratedFDeriv_transportSliceDifferential_le
    (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hY : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W)
    {p : InputVariables n} (hp : p ∈ W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (transportSliceDifferential c Y) p‖ ≤
      ‖transportDifferentialRestriction c‖ *
        ‖iteratedFDeriv ℝ (k + 1) (transportAveragedGradient Y) p‖ := by
  have he : transportSliceDifferential c Y =ᶠ[𝓝 p]
      transportDifferentialRestriction c ∘ fderiv ℝ (transportAveragedGradient Y) :=
    (hW.eventually_mem hp).mono (fun q hq ↦ transportSliceDifferential_eq_restriction c Y
      ((hY.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)))
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have h := (transportDifferentialRestriction c).norm_iteratedFDeriv_comp_left
    ((hY.contDiffAt (hW.mem_nhds hp)).fderiv_right (m := ∞) (by simp))
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simpa only [norm_iteratedFDeriv_fderiv] using h

/-- Summing the pointwise restriction bounds gives a one-derivative cost
for shell seminorms (`app:ch_background:eq:bg-mixed-input`). -/
theorem cNorm_transportSliceDifferential_le (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {W K : Set (InputVariables n)} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hY : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W) (k : ℕ) :
    cNorm K k (transportSliceDifferential c Y) ≤
      ((k + 1 : ℕ) : ℝ) * ‖transportDifferentialRestriction c‖ *
        cNorm K (k + 1) (transportAveragedGradient Y) := by
  have h := cNorm_le_sum_of_bounds (s := K) (r := k)
    (C := fun _ ↦ ‖transportDifferentialRestriction c‖ *
      cNorm K (k + 1) (transportAveragedGradient Y))
    (fun _ _ ↦ mul_nonneg (norm_nonneg (transportDifferentialRestriction c)) (cNorm_nonneg _ _ _)) (by
      intro j hj p hp
      apply (norm_iteratedFDeriv_transportSliceDifferential_le c Y hW hY (hKW hp) j).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg (transportDifferentialRestriction c))
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun q hq ↦ (hY.contDiffAt (hW.mem_nhds (hKW hq))).of_le (by simp)) hp
        (Nat.add_le_add_right hj 1))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using h

end JanetCartan.ContinuumNormalReduction.TransportSymbol
