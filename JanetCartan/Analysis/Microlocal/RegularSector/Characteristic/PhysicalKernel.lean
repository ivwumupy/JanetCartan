module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalOperator

/-!
# The constructed physical two-term characteristic kernel

For `paper-v2.tex`, `app:ch_regular_base:eq:two-term-null-identity`, the
original regular characteristic differential selects a physical coordinate
split. The existing local root, minor, Hamilton chart and signed row producer
then constructs the same phase and both real amplitude columns. The complex
physical kernel is literally `exp(i Ψ) (W₀ + i b₋₁ P W₀)`.

`exists_physical_pencil_kernel` discharges the phase, null and correction
premises of its pointwise differential identity from that construction. The
chart precedes the source mask. This is a local construction from smooth
pencil coefficients and a regular characteristic point, not a uniform finite
sector theorem: common coefficient-family buffers, symbol budgets, fixed
masks, retarded integration and complete forward/adjoint estimates remain.
The retarded consumer must retain its upper endpoint when integrating this
identity, as required by `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d : ℕ}

/-- Complexify the two actual real-column identities and apply the existing physical wave
product rule.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrder_twoTerm_real_columns
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    {φ : Euclidean n → ℝ} {u v : Euclidean n → Fin n → ℝ} {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (ξ : Euclidean n)
    (hξ : ∀ a, partialDeriv φ x a = ξ a)
    (hnull : pencil (Q x) ξ *ᵥ u x = 0)
    (hcorr : pencil (Q x) ξ *ᵥ v x = physicalPencilApply Q B u x) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) •
        ((fun j ↦ (u y j : ℂ)) + Complex.I • (fun j ↦ (v y j : ℂ)))) x =
      Complex.exp (Complex.I * (φ x : ℂ)) •
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y ↦ Complex.I • (fun j ↦ (v y j : ℂ))) x := by
  have huc : DifferentiableAt ℝ (fun y j ↦ (u y j : ℂ)) x :=
    differentiableAt_pi.mpr fun j ↦ Complex.ofRealCLM.differentiableAt.comp x
      (differentiableAt_pi.mp hu j)
  have hvc : DifferentiableAt ℝ (fun y j ↦ (v y j : ℂ)) x :=
    differentiableAt_pi.mpr fun j ↦ Complex.ofRealCLM.differentiableAt.comp x
      (differentiableAt_pi.mp hv j)
  have hincl (w : Fin n → ℝ) :
      ((pencil (Q x) ξ).map Complex.ofReal) *ᵥ (fun j ↦ (w j : ℂ)) =
        fun j ↦ ((pencil (Q x) ξ *ᵥ w) j : ℂ) := by
    ext j
    simp [mulVec, dotProduct]
  have hn : WKB.principalSymbol (complexPencilCoefficient Q) φ x (fun j ↦ (u x j : ℂ)) = 0 := by
    rw [principalSymbol_complexPencil Q φ x ξ hξ]
    change ((pencil (Q x) ξ).map Complex.ofReal) *ᵥ (fun j ↦ (u x j : ℂ)) = 0
    rw [hincl, hnull]
    rfl
  have hc : Complex.I • WKB.principalSymbol (complexPencilCoefficient Q) φ x
      (Complex.I • (fun j ↦ (v x j : ℂ))) +
      WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (fun y j ↦ (u y j : ℂ)) x = 0 := by
    rw [map_smul, smul_smul, Complex.I_mul_I, neg_one_smul,
      principalSymbol_complexPencil Q φ x ξ hξ, firstOrderApply_complexPencil_real Q B hu]
    change -(((pencil (Q x) ξ).map Complex.ofReal) *ᵥ (fun j ↦ (v x j : ℂ))) + _ = 0
    rw [hincl, hcorr, neg_add_cancel]
  have h := WKB.firstOrder_twoTermWave_residual (complexPencilCoefficient Q)
    (complexPencilZeroth B) (lam := 1) one_ne_zero hφ huc
    (show DifferentiableAt ℝ (fun y ↦ Complex.I • (fun j ↦ (v y j : ℂ))) x from
      hvc.const_smul Complex.I) hn hc
  have he : twoTermWave 1 φ (fun y j ↦ (u y j : ℂ))
      (fun y ↦ Complex.I • (fun j ↦ (v y j : ℂ))) =
      fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) •
        ((fun j ↦ (u y j : ℂ)) + Complex.I • (fun j ↦ (v y j : ℂ))) := by
    funext y
    simp [twoTermWave, modulatedWave, waveCarrier]
  rw [he] at h
  simpa [waveCarrier] using h

/-- The literal physical column of exp(i Ψ)(W₀ + W₁), with W₁ = i b₋₁ P W₀ on the same pencil
chart.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
def pencilTwoTermKernelColumn (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (j : Fin n)
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) : Fin n → ℂ :=
  let q := physicalSlice e s η x
  Complex.exp (Complex.I * (twoTimePhase C q : ℂ)) •
    ((fun k ↦ (pencilLeadingColumn e Q B h Φ C r c σ j q k : ℂ)) +
      Complex.I • (fun k ↦ (pencilCorrectionColumn e Q B h Φ C r c σ j q k : ℂ)))

/-- Transfer the local pencil cancellation to the actual physical differential operator. Every
coordinate and complexification premise is proved in PhysicalOperator; the following existence
theorem supplies the remaining local amplitude premises.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrder_pencilTwoTermKernelColumn
    (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (j : Fin (d + 1))
    {q : TwoTimePoint (Euclidean d)}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hclock : (twoTimeState Φ (C.symm q)).1 = q.1)
    (hy : (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1)
    (hu : DifferentiableAt ℝ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) q)
    (hv : DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) q)
    (hnull : rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm q)) *ᵥ
      pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j q = 0)
    (hcorr : rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm q)) *ᵥ
      pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j q =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) q) :
    let x := (coordinateSplit i).symm (q.1, q.2.2.1)
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (pencilTwoTermKernelColumn (coordinateSplit i) Q B h Φ C r c σ j q.2.1 q.2.2.2) x =
      Complex.exp (Complex.I * (twoTimePhase C q : ℂ)) •
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y ↦ Complex.I • (fun k ↦ (pencilCorrectionColumn (coordinateSplit i)
            Q B h Φ C r c σ j (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 y) k : ℂ))) x := by
  let e := coordinateSplit i
  let x := e.symm (q.1, q.2.2.1)
  let sl := physicalSlice e q.2.1 q.2.2.2
  let u := pencilLeadingColumn e Q B h Φ C r c σ j
  let v := pencilCorrectionColumn e Q B h Φ C r c σ j
  have hsl : sl x = q := physicalSlice_at e q
  have hsd : DifferentiableAt ℝ sl x := (contDiff_physicalSlice e _ _).differentiable (by simp) x
  have hud : DifferentiableAt ℝ (u ∘ sl) x := (hsl.symm ▸ hu).comp x hsd
  have hvd : DifferentiableAt ℝ (v ∘ sl) x := (hsl.symm ▸ hv).comp x hsd
  have hpd : DifferentiableAt ℝ (twoTimePhase C ∘ sl) x :=
    (hsl.symm ▸ hphase.differentiableAt).comp x hsd
  let ξ := e.symm (h (twoTimeState Φ (C.symm q)), (twoTimeState Φ (C.symm q)).2.2)
  have hs : pencil (Q x) ξ = rootPencil e Q h (twoTimeState Φ (C.symm q)) := by
    simp only [rootPencil, hclock, hy, x, ξ]
  have hn : pencil (Q x) ξ *ᵥ (u ∘ sl) x = 0 := by
    simpa only [Function.comp_apply, hsl, hs, u, e] using hnull
  have hc : pencil (Q x) ξ *ᵥ (v ∘ sl) x = physicalPencilApply Q B (u ∘ sl) x := by
    rw [physicalPencilApply_slice i Q B hu]
    simpa only [Function.comp_apply, hsl, hs, v, u, e] using hcorr
  have hid := firstOrder_twoTerm_real_columns Q B hpd hud hvd ξ
    (partialDeriv_twoTimePhase_physicalSlice i h Φ C hphase hclock hy) hn hc
  have he : pencilTwoTermKernelColumn e Q B h Φ C r c σ j q.2.1 q.2.2.2 =
      fun y ↦ Complex.exp (Complex.I * (twoTimePhase C (sl y) : ℂ)) •
        ((fun k ↦ (u (sl y) k : ℂ)) + Complex.I • (fun k ↦ (v (sl y) k : ℂ))) := rfl
  dsimp only
  rw [he]
  simpa only [Function.comp_apply, hsl] using hid

/-- Construct a physical two-term kernel at a regular characteristic point, selecting the time
coordinate from the nonzero determinant differential. The root, minor, flow, phase, signed row
and correction come from the same local construction. The physical cancellation and diagonal
data are conclusions; no phase, transport solution or cancellation is assumed.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem exists_physical_pencil_kernel
    {Ω : Set (Euclidean (d + 1))} (hΩ : IsOpen Ω)
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    {B : Euclidean (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (x ξ : Euclidean (d + 1)) (hx : x ∈ Ω) (hξ : ξ ≠ 0)
    (hp : determinant (Q x) ξ = 0)
    (hreg : fderiv ℝ (determinant (Q x)) ξ ≠ 0) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e ξ).2))
      ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      ∃ r c : Fin (d + 1), ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
      ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      ∃ δ > (0 : ℝ),
      let I := Metric.ball z.1 δ
      let U := Metric.ball z.2 δ
      let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
      IsOpen D ∧ z ∈ D ∧ h z = (e ξ).1 ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        (rootPencil e Q h w).det = 0 ∧
        fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
        (rootPencil e Q h w).adjugate r c ≠ 0 ∧
        minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0) ∧
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
        (twoTimeState Φ (C.symm q)).1 = q.1) ∧
      IsOpen V ∧ (z.1, z) ∈ V ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ w ∈ I ×ˢ U, (w.1, w) ∈ V ∧ twoTimeState Φ (C.symm (w.1, w)) = w ∧
        twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
      ∀ σ : RootState (Euclidean d) → ℝ, ContDiffOn ℝ ∞ σ D →
        ∀ j : Fin (d + 1),
          ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j) V ∧
          ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c σ j) V ∧
          (∀ w ∈ I ×ˢ U, pencilLeadingColumn e Q B h Φ C r c σ j (w.1, w) =
            (σ w * minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c j) •
              minorRightNullvector (rootPencil e Q h w) r c) ∧
          ∀ q ∈ V,
            let y := e.symm (q.1, q.2.2.1)
            WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
              (pencilTwoTermKernelColumn e Q B h Φ C r c σ j q.2.1 q.2.2.2) y =
              Complex.exp (Complex.I * (twoTimePhase C q : ℂ)) •
                WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                  (fun w ↦ Complex.I • (fun k ↦ (pencilCorrectionColumn e Q B h Φ C r c σ j
                    (physicalSlice e q.2.1 q.2.2.2 w) k : ℂ))) y := by
  obtain ⟨i, hi⟩ := exists_coordinateSplit_transverse (fderiv ℝ (determinant (Q x)) ξ) hreg
  let e := coordinateSplit i
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e ξ).2))
  have hx' : e.symm (z.1, z.2.1) = x := e.symm_apply_apply x
  have hξ' : e.symm ((e ξ).1, z.2.2) = ξ := e.symm_apply_apply ξ
  obtain ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hroot, hC, hstate,
    _hstateSmooth, _hk, _hl, _hpot, _hb, hV, hzV, hphase, hdiff, hdiag, hleading⟩ :=
    exists_pencil_leading_amplitude e hΩ hQ hB z (e ξ).1
      (by simpa only [hx'] using hx) (by simpa only [hξ'] using hξ)
      (by simpa only [hx', hξ'] using hp)
      (by simpa only [hx', hξ'] using hi)
  refine ⟨i, D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hroot, hC,
    hstate, hV, hzV, hphase, hdiff, hdiag, ?_⟩
  intro σ hσ j
  obtain ⟨hu, hv, hdiagu, hid⟩ := hleading σ hσ j
  refine ⟨hu, hv, hdiagu, ?_⟩
  intro q hq
  have hqd := hV.mem_nhds hq
  exact firstOrder_pencilTwoTermKernelColumn i Q B h Φ C r c σ j (hdiff q hq.1)
    (hstate q hq.1).2 (twoTimeChart_inverse_coordinates hC hq.1).2.2.2
    ((hu.contDiffAt hqd).differentiableAt (by simp))
    ((hv.contDiffAt hqd).differentiableAt (by simp)) (hid q hq).1 (hid q hq).2.2

end JanetCartan.RegularSector.Characteristic
