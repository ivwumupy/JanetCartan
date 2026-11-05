module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilLeading

/-!
# Characteristic identities on a retained uniform chart

Apply the literal signed transport to an already constructed Hamilton chart.
This avoids choosing the new single-coefficient chart in the older local
existence theorem. `exists_uniform_pencilAmplitudes` supplies every input here
from its original coefficient family and retains these conclusions alongside
the quantitative bounds on the SAME matrices.

Consumer: supported conic cancellation and the upper endpoint in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
variable {n d : ℕ}

/-- The signed-row equation, null equation, correction equation and diagonal
value on the given chart follow from the actual Hamilton ODE and primitive
root/minor data. No column cancellation is assumed. Source:
`app:ch_regular_base:lem:characteristic-kernel`, transport step. -/
theorem pencilColumns_of_retained_rootFlow
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    {B : Euclidean n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hphys : ∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin n)
    (hroot : ∀ w ∈ D, (rootPencil e Q h w).det = 0)
    (hgap : ∀ w ∈ D, fderiv ℝ Matrix.det (rootPencil e Q h w)
      (rootTimeCoefficient e Q w) ≠ 0)
    (hm : ∀ w ∈ D, (rootPencil e Q h w).adjugate r c ≠ 0)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (hCf : ContDiffOn ℝ ∞ C C.source) (hCs : ContDiffOn ℝ ∞ C.symm C.target)
    (hs : ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
      (twoTimeState Φ (C.symm q)).1 = q.1)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source) (hID : I ×ˢ U ⊆ D)
    (hi : ∀ w ∈ I ×ˢ U, Φ (w, 0) = w)
    (hd : ∀ q ∈ I ×ˢ (I ×ˢ U), HasDerivAt (fun u ↦ Φ (q.2, u))
      (rootHamiltonField h (twoTimeState Φ q)) (q.1 - q.2.1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    (∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j) V ∧
      ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c σ j) V) ∧
    (∀ w ∈ I ×ˢ U, ∀ j, pencilLeadingColumn e Q B h Φ C r c σ j (w.1, w) =
      (σ w * minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c j) •
        minorRightNullvector (rootPencil e Q h w) r c) ∧
    ∀ q ∈ V, ∀ j,
      rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
        pencilLeadingColumn e Q B h Φ C r c σ j q = 0 ∧
      pencilChartLeft e Q h Φ C r c q ⬝ᵥ
        adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q = 0 ∧
      rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
        pencilCorrectionColumn e Q B h Φ C r c σ j q =
        adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q := by
  dsimp only
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hV : IsOpen V := hCs.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hU))
  have ht w hw := minorTransportCoefficient_ne_zero_of_root (hroot w hw) (hm w hw) (hgap w hw)
  have hH := contDiffOn_rootPencil e hQ hh hphys
  have hA := contDiffOn_rootTimeCoefficient e hQ hphys
  have hHe a b := (Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.comp_contDiffOn hH
  have hAe a b := (Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.comp_contDiffOn hA
  have hk := contDiffOn_minorRightNullvector r c hHe hm
  have hl := contDiffOn_minorLeftNullvector r c hHe hAe ht
  have hkc : ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) C.target :=
    hk.comp hs (fun _ hq ↦ (hstate _ hq).1)
  have hlc : ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) C.target :=
    hl.comp hs (fun _ hq ↦ (hstate _ hq).1)
  have hmap (q : TwoTimePoint (Euclidean d)) (hq : q ∈ C.target) :
      e.symm (q.1, q.2.2.1) ∈ Ω := by
    have hx := hphys _ (hstate q hq).1
    rwa [(hstate q hq).2, (twoTimeChart_inverse_coordinates hC hq).2.2.2] at hx
  have hpot := contDiffOn_pencilTransportPotential e hQ hB r c hmap hkc hlc
  have ha₀ : ContDiffOn ℝ ∞ (pencilSignedDatum e Q h r c σ) (I ×ˢ U) :=
    (hσ.contDiffOn.smul hl).mono hID
  obtain ⟨ha, heq⟩ := twoTimeRowTransport_spec hC hCf hCs hI hIc hU hbox hd ht₀ hpot ha₀
  have hb := contDiffOn_pencilChartComplement e hQ hh hphys hs
    (fun _ hq ↦ (hstate _ hq).1) r c hroot hm ht
  have hα j : ContDiffOn ℝ ∞ (fun q ↦ pencilSignedRow e Q B h Φ C r c σ q j) V :=
    contDiffOn_pi.mp ha j
  have hleading j : ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j) V :=
    (hα j).smul (hkc.mono inter_subset_left)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine ⟨hleading j, ?_⟩
    have hP := contDiffOn_adaptedPencilApply e hQ hB hV
      (fun _ hq ↦ hmap _ hq.1) (hleading j)
    apply contDiffOn_pi.mpr
    intro k
    exact ContDiffOn.sum (s := Finset.univ) fun a _ ↦
      ((Matrix.entryLinearMap ℝ ℝ k a).toContinuousLinearMap.contDiff.comp_contDiffOn
        (hb.mono inter_subset_left)).mul (contDiffOn_pi.mp hP a)
  · intro w hw j
    have hws : (w.1, w) ∈ C.source := hbox ⟨hw.1, hw⟩
    have hrow := twoTimeRowTransport_diagonal hC (pencilTransportPotential e Q B h Φ C r c)
      (pencilSignedDatum e Q h r c σ) (hi w hw) hws
    have hp : C (w.1, w) = (w.1, w) := by
      simp [hC, twoTimeProjection, twoTimeState, hi w hw]
    have hinv : C.symm (w.1, w) = (w.1, w) := by
      simpa only [hp] using C.left_inv hws
    simp only [pencilLeadingColumn, pencilSignedRow, hrow, pencilSignedDatum,
      Pi.smul_apply, smul_eq_mul, pencilChartRight, hinv, twoTimeState, sub_self, hi w hw]
  · intro q hq j
    have hw := (hstate q hq.1).1
    have hnull := (minor_normalization (hroot _ hw) (hm _ hw) (ht _ hw)).1
    have hcompat : pencilChartLeft e Q h Φ C r c q ⬝ᵥ
        adaptedPencilApply e Q B (pencilLeadingColumn e Q B h Φ C r c σ j) q = 0 := by
      have hαd := ((hα j).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
      have hkd := (hkc.contDiffAt (C.open_target.mem_nhds hq.1)).differentiableAt (by simp)
      obtain ⟨htime, hspace⟩ := pencilChart_transport_coefficients e Q hD hh hroot hC hq.1
        hw (hstate q hq.1).2 (hm _ hw) (hgap _ hw)
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
      change fderiv ℝ (pencilSignedRow e Q B h Φ C r c σ) q _ j = _ at hscalar
      rw [hscalar]
      simp only [Pi.smul_apply, smul_eq_mul, pencilSignedRow]
      ring
    refine ⟨?_, hcompat, ?_⟩
    · simp only [pencilLeadingColumn, pencilChartRight, mulVec_smul, hnull, smul_zero]
    · exact pencilChartComplement_mulVec_of_left_eq_zero e Q h Φ C r c q
        (hroot _ hw) (hm _ hw) (ht _ hw) _ hcompat

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
