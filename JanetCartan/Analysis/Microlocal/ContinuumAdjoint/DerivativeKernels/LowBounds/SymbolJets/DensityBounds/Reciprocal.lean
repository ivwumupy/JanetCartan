module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds

/-!
# Reciprocal Jacobian jets with the inverse frequency weight

The determinant in `app:ch_background:eq:bg-Psi` has degree one. Freezing the
input frequency scale, normalizing the columns, and applying the finite
composition estimate twice retains its reciprocal weight in every joint jet.
The consumer is `norm_iteratedFDeriv_weightedPair_le`, the product step in
`app:ch_background:prop:bg-adjoint`.

The image-buffer inclusion is explicit: it is supplied by
`PrimitiveAmplitudeReserve.buffered.image_subset` in the parent construction,
and is not a field of `PrimitiveJetGeometry`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow NormalComparison

variable {n : ℕ}

/-- Smoothness of the literal reciprocal determinant after inverse substitution
in `app:ch_background:eq:bg-Psi`, for the density product estimate. -/
theorem PrimitiveRegularity.reciprocalJacobian_contDiffOn
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ (fun q : JointVariables n ↦
      |(g.jacobian q.1.1 q.1.2.1 q.2
        (g.inverse q.1.1 q.1.2.1 q.2 q.1.2.2)).det|⁻¹) g.outputDomain := by
  have hj : ContDiffOn ℝ ∞ (fun q : JointVariables n ↦
      |(g.jacobian q.1.1 q.1.2.1 q.2 q.1.2.2).det|⁻¹) g.inputDomain := by
    apply ((contDiff_normalJacobianDet.comp_contDiffOn h.jacobian).abs
      h.determinant_ne_zero).inv
    exact fun q hq ↦ abs_ne_zero.mpr (h.determinant_ne_zero q hq)
  exact hj.comp h.pull_contDiffOn h.inverse_mem

/-- Exact recovery with a frozen scale of the reciprocal degree-one Jacobian
in `app:ch_background:eq:bg-Psi`. The equality holds as a function, so it
preserves all joint derivatives used in the density estimate. -/
theorem JetRescaling.reciprocalJacobian_eq {g : Chart n} (s : JetRescaling g)
    {r : ℝ} (hr : 0 < r) (q : JointVariables n) :
    |(g.jacobian q.1.1 q.1.2.1 q.2
      (g.inverse q.1.1 q.1.2.1 q.2 q.1.2.2)).det|⁻¹ =
      r⁻¹ * |(s.normalizedJacobian r (s.normalizedPull r q)).det|⁻¹ := by
  rw [s.normalizedJacobian_det hr]
  simp only [JetRescaling.normalizedPull, ContinuousLinearEquiv.apply_symm_apply,
    Chart.pull, abs_mul, abs_inv, abs_of_pos hr, mul_inv_rev, inv_inv]
  rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- The degree-one determinant gap becomes a fixed gap after normalization
at the input frequency. This supplies the compact reciprocal-determinant
estimate for `app:ch_background:prop:bg-adjoint`. -/
theorem PrimitiveJetGeometry.normalizedJacobian_gap
    {g : Chart n} {s : JetRescaling g} {N : ℕ} {ρ B c : ℝ}
    {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
    (hG : PrimitiveJetGeometry g s N ρ B c L K)
    {p : JointVariables n} (hp : g.pull p ∈ g.inputDomain)
    (hr : 0 < ‖(g.carrier (g.pull p)).2‖) :
    c ≤ |(s.normalizedJacobian ‖(g.carrier (g.pull p)).2‖
      (s.normalizedPull ‖(g.carrier (g.pull p)).2‖ p)).det| := by
  rw [s.normalizedJacobian_det hr]
  simp only [JetRescaling.normalizedPull, ContinuousLinearEquiv.apply_symm_apply,
    abs_mul, abs_inv, abs_of_pos hr]
  rw [← div_eq_mul_inv, le_div_iff₀ hr]
  exact hG.determinant_gap _ hp

/-- A constant depending only on dimension, finite order, primitive jet
budget and normalized determinant gap controls every reciprocal Jacobian jet
by `D/r`. It is chosen before the chart, amplitudes and regularizers.
The image-buffer inclusion is produced by `BufferedSupport.image_subset`;
the consumer is `norm_iteratedFDeriv_weightedPair_le` in
`app:ch_background:prop:bg-adjoint`. -/
theorem exists_reciprocalJacobian_jet_bound (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ D ≥ 0, ∀ {g : Chart n} {s : JetRescaling g} {ρ : ℝ}
      {L : Set (JointVariables n)} {K : Set (Euclidean 2)},
      PrimitiveJetGeometry g s N ρ B c L K →
      ∀ {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ},
      PrimitiveRegularity g a m → g.push '' L ⊆ g.outputDomain →
      ∀ p ∈ g.push '' L, p.2 ∈ K → ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun q : JointVariables n ↦
        |(g.jacobian q.1.1 q.1.2.1 q.2
          (g.inverse q.1.1 q.1.2.1 q.2 q.1.2.2)).det|⁻¹) p‖ ≤
        D / ‖(g.carrier (g.pull p)).2‖ := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_reciprocalAbsNormalJacobian_jet_bound (n := n) N B hc
  let C := (N.factorial : ℝ) * A * (max 1 B)^N
  let D := (N.factorial : ℝ) * C * (max 1 B)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro g s ρ L K hG a m h hL p hp hpK j hj
  let r := ‖(g.carrier (g.pull p)).2‖
  have hr : 0 < r := hG.threshold_pos.trans_le (hG.high_frequency p hp hpK)
  have hpΩ : p ∈ g.outputDomain := hL hp
  let U := (s.input r) ⁻¹' g.inputDomain
  let V : Set (Euclidean n →L[ℝ] Euclidean n) := {T | T.det ≠ 0}
  let J := s.normalizedJacobian r
  let T := s.normalizedPull r
  let F := fun Q : Euclidean n →L[ℝ] Euclidean n ↦ |Q.det|⁻¹
  have hU : IsOpen U := hG.input_open.preimage (s.input r).continuous
  have hV : IsOpen V := isOpen_ne.preimage ContinuousLinearMap.continuous_det
  have hJ : ContDiffOn ℝ ∞ J U :=
    (h.jacobian.comp (s.input r).contDiff.contDiffOn (fun _ hq ↦ hq)).clm_comp
      contDiffOn_const
  have hT : ContDiffOn ℝ ∞ T g.outputDomain :=
    (s.input r).symm.contDiff.comp_contDiffOn h.pull_contDiffOn
  have hTU : MapsTo T g.outputDomain U := by
    intro q hq
    change s.input r ((s.input r).symm (g.pull q)) ∈ g.inputDomain
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.inverse_mem hq
  have hJV : MapsTo J U V := by
    intro q hq
    change (s.normalizedJacobian r q).det ≠ 0
    rw [s.normalizedJacobian_det hr]
    exact mul_ne_zero (h.determinant_ne_zero _ hq) (inv_ne_zero hr.ne')
  have hF : ContDiffOn ℝ ∞ F V := fun Q hQ ↦
    (contDiffAt_reciprocalAbsNormalJacobian hQ).contDiffWithinAt
  have hgap : c ≤ |(J (T p)).det| :=
    hG.normalizedJacobian_gap (h.inverse_mem hpΩ) hr
  have hJjet (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i J (T p)‖ ≤ B :=
    hG.jacobian_jets p hp hpK i hi
  have hFJjet (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (F ∘ J) (T p)‖ ≤ C := by
    have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
      hU hV hJ hF hJV (hTU hpΩ) i
      (fun k hk ↦ hbound (J (T p))
        (by simpa using hJjet 0 (Nat.zero_le N)) hgap k (hk.trans hi))
      (fun k _ hk ↦ hJjet k (hk.trans hi))
    apply hb.trans
    have hf : (i.factorial : ℝ) ≤ N.factorial := by
      exact_mod_cast Nat.factorial_le hi
    dsimp [C]
    gcongr
    exact le_max_left _ _
  have hFJ := hF.comp hJ hJV
  have hcomp := hFJ.comp hT hTU
  have hjet : ‖iteratedFDeriv ℝ j ((F ∘ J) ∘ T) p‖ ≤ D := by
    have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
      h.output_open hU hT hFJ hTU hpΩ j
      (fun i hi ↦ hFJjet i (hi.trans hj))
      (fun i hi hij ↦ hG.inverse_jets p hp hpK i hi (hij.trans hj))
    apply hb.trans
    have hf : (j.factorial : ℝ) ≤ N.factorial := by
      exact_mod_cast Nat.factorial_le hj
    dsimp [D]
    gcongr
    exact le_max_left _ _
  have he : (fun q : JointVariables n ↦
      |(g.jacobian q.1.1 q.1.2.1 q.2
        (g.inverse q.1.1 q.1.2.1 q.2 q.1.2.2)).det|⁻¹) =
      fun q ↦ r⁻¹ • (((F ∘ J) ∘ T) q) := by
    funext q
    exact s.reciprocalJacobian_eq hr q
  rw [he, iteratedFDeriv_const_smul_apply' (i := j) (a := r⁻¹)
    ((hcomp.contDiffAt (h.output_open.mem_nhds hpΩ)).of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  calc
    r⁻¹ * ‖iteratedFDeriv ℝ j ((F ∘ J) ∘ T) p‖ ≤ r⁻¹ * D :=
      mul_le_mul_of_nonneg_left hjet (inv_nonneg.mpr hr.le)
    _ = D / ‖(g.carrier (g.pull p)).2‖ := by rw [div_eq_mul_inv, mul_comm]

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
