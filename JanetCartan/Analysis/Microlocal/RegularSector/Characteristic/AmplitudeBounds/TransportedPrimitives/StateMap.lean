module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RootData

/-!
# Primitive bounds for the literal transported state

The substitution in `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`,
is exactly `Φ ((C.symm q).2, (C.symm q).1 - (C.symm q).2.1)`.
Its fixed linear inner map costs no derivatives. The checked additive
composition estimate then costs two derivatives, independently of output order.
The consumer is the transported pencil pair and hence `pencilTransportPotential`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

open NullTransport.AmplitudeTame

variable {d : ℕ}

/-- Initial state and elapsed time in the literal two-time flow
(`app:ch_regular_base:lem:characteristic-kernel`, phase substitution). -/
def twoTimeFlowInput : TwoTimePoint (Euclidean d) →L[ℝ] RootState (Euclidean d) × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ (RootState (Euclidean d))).prod
    (ContinuousLinearMap.fst ℝ ℝ (RootState (Euclidean d)) -
      (ContinuousLinearMap.fst ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.snd ℝ ℝ (RootState (Euclidean d))))

private theorem cNorm_flowInput_comp_le
    {K : Set (TwoTimePoint (Euclidean d))} (hK : IsCompact K)
    {f : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)} (m : ℕ)
    (hf : ∀ q ∈ K, ContDiffAt ℝ m f q) :
    cNorm K m (twoTimeFlowInput ∘ f) ≤ ‖twoTimeFlowInput (d := d)‖ * cNorm K m f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K j f))
  intro j hj q hq
  apply (twoTimeFlowInput.norm_iteratedFDeriv_comp_left (hf q hq)
    (by exact_mod_cast hj)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hj)
      (mem_image_of_mem _ hq)) (norm_nonneg _)

/-- The actual substituted state has a single additive high contribution
from the flow and inverse chart. All constants precede these primitives and
their open neighborhoods; both compact balls and both image conditions are
explicit. This produces the state-map input for the transported pencil bounds
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_twoTimeState_inverseChart_cNorm_bounds
    (q : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (p : RootState (Euclidean d) × ℝ) {σ : ℝ} (hσ : 0 < σ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (V : Set (TwoTimePoint (Euclidean d))) (W : Set (RootState (Euclidean d) × ℝ)),
        IsOpen V → IsOpen W → closedBall q ρ ⊆ V → closedBall p σ ⊆ W →
        ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
          ContDiffOn ℝ ∞ Φ W → ContDiffOn ℝ ∞ C.symm V →
          MapsTo (twoTimeFlowInput ∘ C.symm) V W →
          MapsTo (twoTimeFlowInput ∘ C.symm) (closedBall q ρ) (closedBall p σ) →
          cNorm (closedBall p σ) 1 Φ ≤ M → cNorm (closedBall q ρ) 1 C.symm ≤ M →
          ContDiffOn ℝ ∞ (fun y ↦ twoTimeState Φ (C.symm y)) V ∧
          ∀ m, cNorm (closedBall q ρ) m (fun y ↦ twoTimeState Φ (C.symm y)) ≤
            A m * (1 + cNorm (closedBall p σ) (m + 2) Φ +
              cNorm (closedBall q ρ) (m + 2) C.symm) := by
  let L := twoTimeFlowInput (d := d)
  choose A hA hb using fun m ↦ exists_cNorm_comp_le_uniform_local
    (G := RootState (Euclidean d)) q p hρ hσ m
      (mul_nonneg (norm_nonneg L) hM) hM
  refine ⟨fun m ↦ A m * (1 + ‖L‖), fun m ↦ mul_pos (hA m) (by positivity), ?_⟩
  intro V W hV hW hK hJ Φ C hΦ hC hmap hmapK hΦM hCM
  have hf : ContDiffOn ℝ ∞ (L ∘ C.symm) V := L.contDiff.comp_contDiffOn hC
  have hlin (m : ℕ) : cNorm (closedBall q ρ) m (L ∘ C.symm) ≤
      ‖L‖ * cNorm (closedBall q ρ) m C.symm :=
    cNorm_flowInput_comp_le (isCompact_closedBall _ _) m
      (fun y hy ↦ (hC.contDiffAt (hV.mem_nhds (hK hy))).of_le (by simp))
  refine ⟨hΦ.comp hf hmap, ?_⟩
  intro m
  have hh := hb m V W hV hW hK hJ (L ∘ C.symm) Φ hf hΦ hmapK
    ((hlin 1).trans (mul_le_mul_of_nonneg_left hCM (norm_nonneg L))) hΦM
  change cNorm (closedBall q ρ) m (fun y ↦ twoTimeState Φ (C.symm y)) ≤ _ at hh
  apply hh.trans
  have hhigh : 1 + cNorm (closedBall q ρ) (m + 2) (L ∘ C.symm) +
      cNorm (closedBall p σ) (m + 2) Φ ≤
      (1 + ‖L‖) * (1 + cNorm (closedBall p σ) (m + 2) Φ +
        cNorm (closedBall q ρ) (m + 2) C.symm) := by
    nlinarith [hlin (m + 2), norm_nonneg L, cNorm_nonneg (closedBall q ρ) (m + 2) C.symm,
      mul_nonneg (norm_nonneg L) (cNorm_nonneg (closedBall p σ) (m + 2) Φ)]
  exact (mul_le_mul_of_nonneg_left hhigh (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
