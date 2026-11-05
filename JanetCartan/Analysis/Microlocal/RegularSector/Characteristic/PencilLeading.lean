module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilComplement

/-!
# Compatibility of the actual leading characteristic amplitude

This is the transport cancellation `lᵀPW₀=0` in `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`. The normalized pencil
identities supply the coefficients of the physical transport derivative.
The actual signed row has potential `lᵀPk`, with the phase covector already
substituted, so the product rule cancels every column. The concluding local
existence theorem constructs the row and discharges the transport equation;
it does not take the cancellation as a premise. Symbol estimates and the
integrated complete residual are separate remaining obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d : ℕ}

/-- One literal column of `W₀=ka` for the direct characteristic kernel
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilLeadingColumn (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (j : Fin n)
    (q : TwoTimePoint (Euclidean d)) : Fin n → ℝ :=
  pencilSignedRow e Q B h Φ C r c σ q j • pencilChartRight e Q h Φ C r c q

/-- The real column `b₋₁PW₀`; the physical correction `W₁` is `i` times
this column after complexification. Both factors use the same chart and
minor (`app:ch_regular_base:eq:two-term-null-identity`). -/
def pencilCorrectionColumn (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (j : Fin n)
    (q : TwoTimePoint (Euclidean d)) : Fin n → ℝ :=
  pencilChartComplement e Q h Φ C r c q *ᵥ
    adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q

/-- The physical product rule in the exact adapted coordinates. This retains
the zeroth-order term and is used only for the columns of `W₀`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem adaptedPencilApply_left_smul
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    {α : TwoTimePoint (Euclidean d) → ℝ} {k : TwoTimePoint (Euclidean d) → Fin n → ℝ}
    {q : TwoTimePoint (Euclidean d)}
    (hα : DifferentiableAt ℝ α q) (hk : DifferentiableAt ℝ k q)
    (l : Fin n → ℝ) (v : Euclidean d)
    (ht : l ⬝ᵥ (adaptedPencilCoefficient e Q q (1, 0) *ᵥ k q) = 1)
    (hy : ∀ j, l ⬝ᵥ (adaptedPencilCoefficient e Q q (0, EuclideanSpace.single j 1) *ᵥ k q) = v j) :
    l ⬝ᵥ adaptedPencilApply e Q B (fun w ↦ α w • k w) q =
      fderiv ℝ α q (1, (0, (v, 0))) + α q * (l ⬝ᵥ adaptedPencilApply e Q B k q) := by
  have hd (w : TwoTimePoint (Euclidean d)) :
      fderiv ℝ (fun z ↦ α z • k z) q w =
        α q • fderiv ℝ k q w + fderiv ℝ α q w • k q := by
    change fderiv ℝ (α • k) q w = _
    rw [fderiv_smul hα hk]
    rfl
  have hsum : (∑ j, v j * fderiv ℝ α q (0, (0, (EuclideanSpace.single j 1, 0)))) =
      fderiv ℝ α q (0, (0, (v, 0))) := by
    let L : Euclidean d →L[ℝ] ℝ := (fderiv ℝ α q).comp
      ((ContinuousLinearMap.inr ℝ ℝ (RootState (Euclidean d))).comp
        ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
          (ContinuousLinearMap.inl ℝ (Euclidean d) (Euclidean d))))
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, smul_eq_mul, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply] using
      congrArg L ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v)
  have hv : ((1, (0, (v, 0))) : TwoTimePoint (Euclidean d)) =
      (1, (0, (0, (0 : Euclidean d)))) + (0, (0, (v, (0 : Euclidean d)))) := by simp
  simp only [adaptedPencilApply, hd, mulVec_add, mulVec_smul, dotProduct_add,
    dotProduct_sum, dotProduct_smul, smul_eq_mul, ht, hy, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hv, map_add, ← hsum]
  simp only [mul_comm (fderiv ℝ α q _) (v _)]
  ring

/-- The actual minor normalization gives exactly the coefficients of the
Hamilton transport field on the phase chart. Both the time normalization
and the sign of the spatial velocity are derived from the pencil
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem pencilChart_transport_coefficients
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, (rootPencil e Q h w).det = 0)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target)
    (hstate : twoTimeState Φ (C.symm q) ∈ D)
    (hclock : (twoTimeState Φ (C.symm q)).1 = q.1) {r c : Fin n}
    (hm : (rootPencil e Q h (twoTimeState Φ (C.symm q))).adjugate r c ≠ 0)
    (hgap : fderiv ℝ Matrix.det (rootPencil e Q h (twoTimeState Φ (C.symm q)))
      (rootTimeCoefficient e Q (twoTimeState Φ (C.symm q))) ≠ 0) :
    pencilChartLeft e Q h Φ C r c q ⬝ᵥ
      (adaptedPencilCoefficient e Q q (1, 0) *ᵥ pencilChartRight e Q h Φ C r c q) = 1 ∧
    ∀ j, pencilChartLeft e Q h Φ C r c q ⬝ᵥ
      (adaptedPencilCoefficient e Q q (0, EuclideanSpace.single j 1) *ᵥ
        pencilChartRight e Q h Φ C r c q) =
      (-rootMomentumGradient h (twoTimeState Φ (C.symm q))) j := by
  have hy := (twoTimeChart_inverse_coordinates hC hq).2.2.2
  have hn := (minor_normalization (hroot _ hstate) hm
    (minorTransportCoefficient_ne_zero_of_root (hroot _ hstate) hm hgap)).2.2.1
  refine ⟨?_, ?_⟩
  · simpa only [pencilChartLeft, pencilChartRight, adaptedPencilCoefficient,
      rootTimeCoefficient, hclock, hy] using hn
  · intro j
    have hsp := rootPencil_normalized_spatial_coefficient e Q hD hh hroot hstate hm
      (by rwa [rootPencil_time_derivative] at hgap) (EuclideanSpace.single j 1)
    simpa only [pencilChartLeft, pencilChartRight, adaptedPencilCoefficient,
      EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul,
      hclock, hy, PiLp.neg_apply] using hsp

/-- Construct the local leading amplitude and prove both its null equation
and `lᵀPW₀=0` from the actual signed row. The root, minor, phase, flow,
inverse, potential and row equation are all constructed from the primitive
smooth pencil and its simple characteristic point. The same chart is chosen
before the scalar source mask. This is the local leading-amplitude step,
not the finite-sector operator or its Sobolev estimate
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_pencil_leading_amplitude
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} {B : Euclidean n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (z : RootState (Euclidean d)) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      ∃ r c : Fin n, ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
      ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      ∃ δ > (0 : ℝ),
      let I := ball z.1 δ
      let U := ball z.2 δ
      let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        (rootPencil e Q h w).det = 0 ∧
        fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
        (rootPencil e Q h w).adjugate r c ≠ 0 ∧
        minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0) ∧
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
        (twoTimeState Φ (C.symm q)).1 = q.1) ∧
      ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target ∧
      ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) C.target ∧
      ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) C.target ∧
      ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) C.target ∧
      ContDiffOn ℝ ∞ (pencilChartComplement e Q h Φ C r c) C.target ∧
      IsOpen V ∧ (z.1, z) ∈ V ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ w ∈ I ×ˢ U, (w.1, w) ∈ V ∧ twoTimeState Φ (C.symm (w.1, w)) = w ∧
        twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
      ∀ σ : RootState (Euclidean d) → ℝ, ContDiffOn ℝ ∞ σ D →
        ∀ j : Fin n, ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j) V ∧
          ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c σ j) V ∧
          (∀ w ∈ I ×ˢ U, pencilLeadingColumn e Q B h Φ C r c σ j (w.1, w) =
            (σ w * minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c j) •
              minorRightNullvector (rootPencil e Q h w) r c) ∧
          ∀ q ∈ V,
            rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
              pencilLeadingColumn e Q B h Φ C r c σ j q = 0 ∧
            pencilChartLeft e Q h Φ C r c q ⬝ᵥ
              adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q = 0 ∧
            rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
              pencilCorrectionColumn e Q B h Φ C r c σ j q =
              adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q := by
  obtain ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hroot, hC, hphase, hdiff,
    hstate, hstateSmooth, hk, hl, hpot, hV, hzV, hdiag, hrow⟩ :=
    exists_pencil_signed_transport e hΩ hQ hB z τ hx hξ hp hgap
  let I := ball z.1 δ
  let U := ball z.2 δ
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hb := contDiffOn_pencilChartComplement e hQ hh (fun w hw ↦ (hroot w hw).1)
    hstateSmooth (fun q hq ↦ (hstate q hq).1) r c (fun w hw ↦ (hroot w hw).2.2.1)
    (fun w hw ↦ (hroot w hw).2.2.2.2.1) (fun w hw ↦ (hroot w hw).2.2.2.2.2)
  refine ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hroot, hC,
    hstate, hstateSmooth, hk, hl, hpot, hb, hV, hzV,
    hphase, hdiff, hdiag, ?_⟩
  intro σ hσ j
  obtain ⟨ha, hdiagRow, heq, _⟩ := hrow σ hσ
  have hα : ContDiffOn ℝ ∞ (fun q ↦ pencilSignedRow e Q B h Φ C r c σ q j) V :=
    contDiffOn_pi.mp ha j
  have hleading : ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j) V :=
    hα.smul (hk.mono inter_subset_left)
  have hmap (q : TwoTimePoint (Euclidean d)) (hq : q ∈ V) :
      e.symm (q.1, q.2.2.1) ∈ Ω := by
    have hx := (hroot _ (hstate q hq.1).1).1
    rwa [(hstate q hq.1).2, (twoTimeChart_inverse_coordinates hC hq.1).2.2.2] at hx
  have hP := contDiffOn_adaptedPencilApply e hQ hB hV hmap hleading
  refine ⟨hleading, ?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    exact ContDiffOn.sum (s := Finset.univ) fun a _ ↦
      ((Matrix.entryLinearMap ℝ ℝ i a).toContinuousLinearMap.contDiff.comp_contDiffOn
        (hb.mono inter_subset_left)).mul (contDiffOn_pi.mp hP a)
  · intro w hw
    simp only [pencilLeadingColumn, hdiagRow w hw, pencilSignedDatum, Pi.smul_apply,
      smul_eq_mul, pencilChartRight, (hdiag w hw).2.1]
  · intro q hq
    have hw := (hstate q hq.1).1
    obtain ⟨_, _, hdet, hder, hm, ht⟩ := hroot _ hw
    have hnull := (minor_normalization hdet hm ht).1
    have hcompat : pencilChartLeft e Q h Φ C r c q ⬝ᵥ
        adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q = 0 := by
      have hαd := (hα.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
      have hkd := (hk.contDiffAt (C.open_target.mem_nhds hq.1)).differentiableAt (by simp)
      obtain ⟨htime, hspace⟩ := pencilChart_transport_coefficients e Q hD hh
        (fun w hw ↦ (hroot w hw).2.2.1) hC hq.1 hw (hstate q hq.1).2 hm hder
      have hscalar := congrArg (fun a : Fin n → ℝ ↦ a j) (heq q hq)
      have hderiv : fderiv ℝ (fun w ↦ pencilSignedRow e Q B h Φ C r c σ w j) q =
          (ContinuousLinearMap.proj j).comp (fderiv ℝ (pencilSignedRow e Q B h Φ C r c σ) q) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).hasFDerivAt.comp q
          ((ha.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt).fderiv
      change pencilChartLeft e Q h Φ C r c q ⬝ᵥ
        adaptedPencilApply e Q B
          (fun w ↦ pencilSignedRow e Q B h Φ C r c σ w j • pencilChartRight e Q h Φ C r c w) q = 0
      rw [adaptedPencilApply_left_smul e Q B hαd hkd _ _ htime hspace, hderiv]
      change (fderiv ℝ (pencilSignedRow e Q B h Φ C r c σ) q
        (1, (0, (-rootMomentumGradient h (twoTimeState Φ (C.symm q)), 0)))) j +
          pencilSignedRow e Q B h Φ C r c σ q j * pencilTransportPotential e Q B h Φ C r c q = 0
      rw [hscalar]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, hcompat, ?_⟩
    · simp only [pencilLeadingColumn, pencilChartRight, mulVec_smul, hnull, smul_zero]
    · exact pencilChartComplement_mulVec_of_left_eq_zero e Q h Φ C r c q hdet hm ht _ hcompat

end JanetCartan.RegularSector.Characteristic
