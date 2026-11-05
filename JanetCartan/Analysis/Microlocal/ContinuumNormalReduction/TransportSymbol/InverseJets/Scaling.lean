module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian

/-!
# Regularity and scaling of the supplied transport Jacobian

The coefficient in `app:ch_background:eq:bg-full-complex-amplitude` is the
actual absolute determinant of `bg-jacobian`. Its smoothness and degree-one
law follow from that identity and the genuine forward map. These lemmas
supply the Jacobian regularity and scaling inputs of `inputDensity_contDiffOn`
and `extendedDensity_homogeneous` in the parent transport-symbol construction.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

private theorem slice_differentiableAt (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {p : InputVariables n} (hp : DifferentiableAt ℝ (transportAveragedGradient Y) p) :
    DifferentiableAt ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, p.2.2)) := by
  let z := c.equiv.symm (p.2.1.1, p.2.2)
  have hi : DifferentiableAt ℝ
      (fun w : Euclidean n ↦ (p.1, ((c.equiv w).1, p.2.1.2), (c.equiv w).2)) z :=
    (differentiableAt_const p.1).prodMk
      ((c.equiv.differentiableAt.fst.prodMk (differentiableAt_const p.2.1.2)).prodMk
        c.equiv.differentiableAt.snd)
  have he : (p.1, ((c.equiv z).1, p.2.1.2), (c.equiv z).2) = p := by simp [z]
  exact (he.symm ▸ hp).comp z hi

/-- The supplied absolute Jacobian and its reciprocal are smooth wherever
its determinant is nonzero. This proves, rather than assumes, the Jacobian
regularity required by the literal amplitude (`app:ch_background:eq:bg-jacobian`). -/
theorem suppliedTransportJacobian_contDiffOn
    (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {J : InputVariables n → ℝ} {W : Set (InputVariables n)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W)
    (hJ : EqOn J (transportAbsoluteJacobian c Y) W)
    (hne : ∀ p ∈ W, J p ≠ 0) :
    ContDiffOn ℝ ∞ J W ∧ ContDiffOn ℝ ∞ (fun p ↦ (J p)⁻¹) W := by
  have hA := transportSliceDifferential_contDiffOn c Y hW hf
  have hj : ContDiffOn ℝ ∞ J W := by
    intro p hp
    have hd : (transportSliceDifferential c Y p).det ≠ 0 := by
      intro he
      apply hne p hp
      rw [hJ hp]
      simp [transportAbsoluteJacobian, he]
    have hh : ContDiffAt ℝ ∞ (transportAbsoluteJacobian c Y) p :=
      (NormalComparison.contDiff_normalJacobianDet.contDiffAt.abs hd).comp p
        (hA.contDiffAt (hW.mem_nhds hp))
    exact (hh.congr_of_eventuallyEq
      ((hW.eventually_mem hp).mono (fun q hq ↦ hJ hq))).contDiffWithinAt
  exact ⟨hj, hj.inv hne⟩

/-- Degree-one positive homogeneity of the supplied `J` follows from the
actual forward scaling law and the literal Jacobian identity on the chart.
There is no Jacobian scaling hypothesis. This discharges the `hJ` premise
of `extendedDensity_homogeneous` once the parent supplies the conic chart
containments (`app:ch_background:eq:bg-jacobian`). -/
theorem suppliedTransportJacobian_pos_smul
    (c : TransportSliceCoordinates n) (hn : 0 < n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    {J : InputVariables n → ℝ} {W : Set (InputVariables n)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (transportAveragedGradient Y) W)
    (hJ : EqOn J (transportAbsoluteJacobian c Y) W)
    {p : InputVariables n} (hp : p ∈ W) {t : ℝ} (ht : 0 < t)
    (htp : scaleInput t p ∈ W) : J (scaleInput t p) = t * J p := by
  rw [hJ htp, hJ hp]
  exact transportAbsoluteJacobian_pos_smul c hn Y p ht
    (slice_differentiableAt c Y ((hf.contDiffAt (hW.mem_nhds hp)).differentiableAt
      (by simp)))
    (slice_differentiableAt c Y ((hf.contDiffAt (hW.mem_nhds htp)).differentiableAt
      (by simp)))

end JanetCartan.ContinuumNormalReduction.TransportSymbol
