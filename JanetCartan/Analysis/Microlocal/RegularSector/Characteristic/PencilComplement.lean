module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilTransport

/-!
# The constructed complement evaluated on the phase chart

For `paper-v2.tex`, `app:ch_regular_base:eq:two-term-null-identity`, the
correction uses the complement at `τ=Ψ_t=h(t,y,Ψ_y)`. We apply the existing
fixed-minor complement constructor to the same transported state as the
phase and row. Its invertibility, smoothness, oblique projection and side
constraint follow from the actual root/minor identities. Those identities
are conclusions of `exists_pencil_signed_transport`; no inverse or inverse
identity is assumed here. Off-root symbol budgets and the complete operator
residual remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

variable {n d : ℕ}

/-- The literal complement symbol evaluated at the phase covector. The
off-root parameter is zero because the phase solves the eikonal equation
(`app:ch_regular_base:eq:two-term-null-identity`). -/
def pencilChartComplement (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d)) : MetricTensor n :=
  let w := twoTimeState Φ (C.symm q)
  minorComplementInverse (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c 0

/-- Instantiate every invertibility premise of the complement on the phase
chart using the original characteristic, minor and transport denominators.
The side constraint uses `lᵀA_t`, and the projection remains oblique
(`app:ch_regular_base:eq:complement-symbol`). -/
theorem pencilChartComplement_identities
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d))
    (hroot : (rootPencil e Q h (twoTimeState Φ (C.symm q))).det = 0)
    (hm : (rootPencil e Q h (twoTimeState Φ (C.symm q))).adjugate r c ≠ 0)
    (ht : minorTransportCoefficient (rootPencil e Q h (twoTimeState Φ (C.symm q)))
      (rootTimeCoefficient e Q (twoTimeState Φ (C.symm q))) r c ≠ 0) :
    rootPencil e Q h (twoTimeState Φ (C.symm q)) * pencilChartComplement e Q h Φ C r c q =
      complementProjection (rootTimeCoefficient e Q (twoTimeState Φ (C.symm q)))
        (pencilChartRight e Q h Φ C r c q) (pencilChartLeft e Q h Φ C r c q) ∧
    (pencilChartLeft e Q h Φ C r c q ᵥ* rootTimeCoefficient e Q (twoTimeState Φ (C.symm q)))
      ᵥ* pencilChartComplement e Q h Φ C r c q = 0 := by
  obtain ⟨_, hl, hn, hker⟩ := minor_normalization hroot hm ht
  have hd := pencilCompletion_det_ne_zero hl hn hker
  exact ⟨by simpa only [pencilChartComplement, pencilChartRight, pencilChartLeft,
    minorComplementInverse, zero_smul, add_zero] using complementInverse_identity hl hn hd,
    complementInverse_constraint hl hn hd⟩

/-- The actual complement inverts a vector annihilated by the left
nullvector. Its consumer is `P W₀`, whose compatibility is proved by the
signed row construction (`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem pencilChartComplement_mulVec_of_left_eq_zero
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d))
    (hroot : (rootPencil e Q h (twoTimeState Φ (C.symm q))).det = 0)
    (hm : (rootPencil e Q h (twoTimeState Φ (C.symm q))).adjugate r c ≠ 0)
    (ht : minorTransportCoefficient (rootPencil e Q h (twoTimeState Φ (C.symm q)))
      (rootTimeCoefficient e Q (twoTimeState Φ (C.symm q))) r c ≠ 0)
    (v : Fin n → ℝ) (hv : pencilChartLeft e Q h Φ C r c q ⬝ᵥ v = 0) :
    rootPencil e Q h (twoTimeState Φ (C.symm q)) *ᵥ
      (pencilChartComplement e Q h Φ C r c q *ᵥ v) = v := by
  rw [mulVec_mulVec, (pencilChartComplement_identities e Q h Φ C r c q hroot hm ht).1]
  simp [complementProjection, sub_mulVec, vecMulVec_mulVec, hv]

/-- Smoothness of the same complement is derived from the primitive smooth
root and actual state map. The matrix inverse's determinant condition is
proved pointwise by the fixed minor, not supplied as an analytic premise
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_pencilChartComplement
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} {h : RootState (Euclidean d) → ℝ}
    (hh : ContDiffOn ℝ ∞ h D) (hmap : ∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hs : ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D)
    (r c : Fin n) (hroot : ∀ w ∈ D, (rootPencil e Q h w).det = 0)
    (hm : ∀ w ∈ D, (rootPencil e Q h w).adjugate r c ≠ 0)
    (ht : ∀ w ∈ D, minorTransportCoefficient (rootPencil e Q h w)
      (rootTimeCoefficient e Q w) r c ≠ 0) :
    ContDiffOn ℝ ∞ (pencilChartComplement e Q h Φ C r c) C.target := by
  have hH := (contDiffOn_rootPencil e hQ hh hmap).comp hs hstate
  have hA := (contDiffOn_rootTimeCoefficient e hQ hmap).comp hs hstate
  have hHe (i j : Fin n) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn hH
  have hAe (i j : Fin n) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn hA
  apply contDiffOn_minorComplementInverse r c hHe hAe contDiffOn_const
    (fun q hq ↦ hm _ (hstate q hq)) (fun q hq ↦ ht _ (hstate q hq))
  intro q hq
  obtain ⟨_, hl, hn, hker⟩ := minor_normalization
    (hroot _ (hstate q hq)) (hm _ (hstate q hq)) (ht _ (hstate q hq))
  exact pencilCompletion_det_ne_zero hl hn hker

end JanetCartan.RegularSector.Characteristic
