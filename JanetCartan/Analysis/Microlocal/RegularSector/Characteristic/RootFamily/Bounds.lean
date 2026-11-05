module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Field
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RootData

/-!
# Original-coefficient bounds for the constructed root branch

For `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`, compose the single smooth
coefficient branch with the original physical coefficient field and the
frequency projection. Compact-range tame composition and a fixed linear
pullback give joint `cNorm` estimates with zero derivative loss and one high
coefficient norm. No derivative of a variable root is an input.

The branch smoothness used here is produced by
`exists_buffered_coefficientRoot`. The quantitative family constructor
instantiates this helper with that very branch. The consumers are the
two-time Hamilton flow and `AmplitudeBounds.exists_rootMinorData_cNorm_bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open ActualCarriers AmplitudeBounds FullPhaseCharts.InverseEstimates
  NullTransport.AmplitudeTame

variable {n d : ℕ}

/-- Joint root estimates on a fixed state ball, in terms of the original
coefficient on the prescribed physical ball. All constants precede the
smooth coefficient field and its derivative order; the derivative reserve
is zero (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_fieldRoot_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : RootState (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R : ℝ)
    (A₀ : Fin n → MetricTensor n) (η₀ : Euclidean d) {ε : ℝ} (hε : 0 < ε)
    (H : (Fin n → MetricTensor n) × Euclidean d → ℝ)
    (hH : ∀ p ∈ closedBall (A₀, η₀) (3 * ε), ContDiffAt ℝ ∞ H p)
    (himage : MapsTo (rootPhysicalPosition e) (closedBall z ρ) (closedBall x R))
    (hfrequency : MapsTo (fun w : RootState (Euclidean d) ↦ w.2.2)
      (closedBall z ρ) (closedBall η₀ ε)) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n)), IsOpen Ω → closedBall x R ⊆ Ω →
        ∀ Q : Euclidean n → Fin n → MetricTensor n,
          ContDiffOn ℝ ∞ Q Ω → MapsTo Q (closedBall x R) (closedBall A₀ ε) →
          ∀ m, cNorm (closedBall z ρ) m (fieldRoot e Q H) ≤
            C m * (1 + cNorm (closedBall x R) m Q) := by
  let K := closedBall z ρ
  let KQ := closedBall x R
  let T := closedBall (A₀, η₀) (3 * ε)
  let η : RootState (Euclidean d) → Euclidean d := fun w ↦ w.2.2
  let L := rootPhysicalPosition e
  choose A hA hb using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn z hρ
      (isCompact_closedBall (A₀, η₀) (3 * ε)) (le_refl m)
      (fun p hp ↦ (hH p hp).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  let a := fun m ↦ linearNormCost L m
  let b := fun m ↦ cNorm K m η
  have ha (m) : 0 < a m := linearNormCost_pos L m
  have hb0 (m) : 0 ≤ b m := cNorm_nonneg _ _ _
  refine ⟨fun m ↦ A m * (1 + a m + b m),
    fun m ↦ mul_pos (hA m) (by linarith [ha m, hb0 m]), ?_⟩
  intro Ω hΩ hKQ Q hQ hQrange m
  let D := L ⁻¹' Ω
  have hD : IsOpen D := hΩ.preimage L.continuous
  have hKD : K ⊆ D := fun w hw ↦ hKQ (himage hw)
  let f := fun w ↦ (Q (L w), η w)
  have hQp : ContDiffOn ℝ ∞ (Q ∘ L) D :=
    hQ.comp L.contDiff.contDiffOn (fun _ hw ↦ hw)
  have hf : ContDiffOn ℝ ∞ f D := hQp.prodMk contDiffOn_snd.snd
  have hft : MapsTo f K T := by
    intro w hw
    dsimp only [T]
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall (by linarith) (hQrange (himage hw)),
      closedBall_subset_closedBall (by linarith) (hfrequency hw)⟩
  have hQhigh : cNorm K m (Q ∘ L) ≤ a m * cNorm KQ m Q :=
    cNorm_comp_linear_le L (isCompact_closedBall _ _) hΩ hKQ hQ himage m
  have hpair := cNorm_prodMk_le_on K (isCompact_closedBall _ _) m
    (fun w hw ↦ (hQp.contDiffAt (hD.mem_nhds (hKD hw))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp))
    (fun _ _ ↦ contDiffAt_snd.snd (n := (m : ℕ∞ω)))
  have hn : cNorm K m f ≤ a m * cNorm KQ m Q + b m := by
    change cNorm K m f ≤ cNorm K m (Q ∘ L) + b m at hpair
    linarith
  have hbound := hb m D hD hKD f hf hft
  change cNorm K m (fieldRoot e Q H) ≤ A m * (1 + cNorm K m f) at hbound
  apply hbound.trans
  have hq0 := cNorm_nonneg KQ m Q
  have hfinal : 1 + cNorm K m f ≤
      (1 + a m + b m) * (1 + cNorm KQ m Q) := by
    nlinarith [mul_nonneg (hb0 m) hq0, ha m, hb0 m]
  exact (mul_le_mul_of_nonneg_left hfinal (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.RootFamily
