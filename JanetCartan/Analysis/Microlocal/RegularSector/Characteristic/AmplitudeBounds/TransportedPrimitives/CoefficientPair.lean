module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.TransportedPrimitives.StateMap

/-!
# The actual pencil pair after transported-covector substitution

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the
root pair producer and the literal state-map producer discharge both inputs
of additive composition. The reserve is four, independent of output order.
The consumers are the three rational primitive amplitudes and `lᵀPk`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

open NullTransport.AmplitudeTame

variable {n d : ℕ}

/-- Fixed-shift single-high control of the literal transported root pencil
and time coefficient. The primitive low order is three; no norm of the
substituted state or matrix pair is assumed. All four primitive norms use
their own fixed balls (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_transportedRootCoefficientPair_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (q : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (p : RootState (Euclidean d) × ℝ) {σ : ℝ} (hσ : 0 < σ)
    (z : RootState (Euclidean d)) {τ : ℝ} (hτ : 0 < τ)
    (x : Euclidean n) (R : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (himage : MapsTo (rootPhysicalPosition e) (closedBall z τ) (closedBall x R)) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (Ω : Set (Euclidean n)) (D : Set (RootState (Euclidean d)))
        (V : Set (TwoTimePoint (Euclidean d))) (W : Set (RootState (Euclidean d) × ℝ)),
        IsOpen Ω → IsOpen D → IsOpen V → IsOpen W →
        closedBall x R ⊆ Ω → closedBall z τ ⊆ D → closedBall q ρ ⊆ V → closedBall p σ ⊆ W →
        MapsTo (rootPhysicalPosition e) D Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
          (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ h D →
          ContDiffOn ℝ ∞ Φ W → ContDiffOn ℝ ∞ C.symm V →
          MapsTo (twoTimeFlowInput ∘ C.symm) V W →
          MapsTo (twoTimeFlowInput ∘ C.symm) (closedBall q ρ) (closedBall p σ) →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) V D →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) (closedBall q ρ) (closedBall z τ) →
          cNorm (closedBall x R) 3 Q ≤ M → cNorm (closedBall z τ) 3 h ≤ M →
          cNorm (closedBall p σ) 3 Φ ≤ M → cNorm (closedBall q ρ) 3 C.symm ≤ M →
          let U := fun y ↦ (rootPencil e Q h (twoTimeState Φ (C.symm y)),
            rootTimeCoefficient e Q (twoTimeState Φ (C.symm y)))
          ContDiffOn ℝ ∞ U V ∧
          ∀ m, cNorm (closedBall q ρ) m U ≤
            A m * (1 + cNorm (closedBall x R) (m + 4) Q + cNorm (closedBall z τ) (m + 4) h +
              cNorm (closedBall p σ) (m + 4) Φ + cNorm (closedBall q ρ) (m + 4) C.symm) := by
  obtain ⟨A, hA, hstate⟩ := exists_twoTimeState_inverseChart_cNorm_bounds q hρ p hσ hM
  obtain ⟨B, hB, hpair⟩ := exists_rootCoefficientPair_cNorm_bounds e z hτ x R M himage
  let Ns := A 1 * (1 + M + M)
  let Nu := B 1 * (1 + M + M)
  have hNs : 0 ≤ Ns := mul_nonneg (hA 1).le (by linarith)
  have hNu : 0 ≤ Nu := mul_nonneg (hB 1).le (by linarith)
  choose J hJ hcomp using fun m ↦ exists_cNorm_comp_le_uniform_local
    (G := MetricTensor n × MetricTensor n) q z hρ hτ m hNs hNu
  refine ⟨fun m ↦ J m * (1 + A (m + 2) + B (m + 2)),
    fun m ↦ mul_pos (hJ m) (by linarith [hA (m + 2), hB (m + 2)]), ?_⟩
  intro Ω D V W hΩ hD hV hW hKQ hKz hKq hKp hphys Q h Φ C hQ hh hΦ hC
    hflow hflowK hstateD hstateK hQM hhM hΦM hCM
  have hQ0 : cNorm (closedBall x R) 0 Q ≤ M := (cNorm_mono_order (by omega)).trans hQM
  have hh0 : cNorm (closedBall z τ) 0 h ≤ M := (cNorm_mono_order (by omega)).trans hhM
  obtain ⟨hs, hsb⟩ := hstate V W hV hW hKq hKp Φ C hΦ hC hflow hflowK
    ((cNorm_mono_order (by omega)).trans hΦM) ((cNorm_mono_order (by omega)).trans hCM)
  let s := fun y ↦ twoTimeState Φ (C.symm y)
  let u := fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w)
  have hu : ContDiffOn ℝ ∞ u D :=
    (contDiffOn_rootPencil e hQ hh hphys).prodMk (contDiffOn_rootTimeCoefficient e hQ hphys)
  have hub m := hpair Ω D hΩ hD hKQ hKz hphys Q h hQ hh hQ0 hh0 m
  have hs1 : cNorm (closedBall q ρ) 1 s ≤ Ns := (hsb 1).trans
    (mul_le_mul_of_nonneg_left (by simpa using add_le_add (add_le_add_right hΦM 1) hCM) (hA 1).le)
  have hu1 : cNorm (closedBall z τ) 1 u ≤ Nu := (hub 1).trans
    (mul_le_mul_of_nonneg_left (by linarith [
      (cNorm_mono_order (by omega : 1 ≤ 3) (f := Q) (s := closedBall x R)).trans hQM,
      (cNorm_mono_order (by omega : 1 ≤ 3) (f := h) (s := closedBall z τ)).trans hhM]) (hB 1).le)
  refine ⟨hu.comp hs hstateD, ?_⟩
  intro m
  have hb := hcomp m V D hV hD hKq hKz s u hs hu hstateK hs1 hu1
  apply hb.trans
  let H := 1 + cNorm (closedBall x R) (m + 4) Q + cNorm (closedBall z τ) (m + 4) h +
    cNorm (closedBall p σ) (m + 4) Φ + cNorm (closedBall q ρ) (m + 4) C.symm
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall x R) (m + 4) Q, cNorm_nonneg (closedBall z τ) (m + 4) h,
      cNorm_nonneg (closedBall p σ) (m + 4) Φ, cNorm_nonneg (closedBall q ρ) (m + 4) C.symm]
  have hsH : cNorm (closedBall q ρ) (m + 2) s ≤ A (m + 2) * H := by
    apply (hsb (m + 2)).trans
    apply mul_le_mul_of_nonneg_left _ (hA _).le
    dsimp [H]
    simp only [show m + 2 + 2 = m + 4 by omega]
    linarith [cNorm_nonneg (closedBall x R) (m + 4) Q, cNorm_nonneg (closedBall z τ) (m + 4) h]
  have huH : cNorm (closedBall z τ) (m + 2) u ≤ B (m + 2) * H := by
    apply (hub (m + 2)).trans
    apply mul_le_mul_of_nonneg_left _ (hB _).le
    dsimp [H]
    linarith [cNorm_mono_order (f := Q) (s := closedBall x R) (by omega : m + 2 ≤ m + 4),
      cNorm_mono_order (f := h) (s := closedBall z τ) (by omega : m + 2 ≤ m + 4),
      cNorm_nonneg (closedBall p σ) (m + 4) Φ, cNorm_nonneg (closedBall q ρ) (m + 4) C.symm]
  have hsum : 1 + cNorm (closedBall q ρ) (m + 2) s + cNorm (closedBall z τ) (m + 2) u ≤
      (1 + A (m + 2) + B (m + 2)) * H := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsum (hJ m).le).trans_eq (by dsimp [H]; ring)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
