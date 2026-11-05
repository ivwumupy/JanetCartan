module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilTransport
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.MinorData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Reparametrization

/-!
# Primitive bounds before the transported-covector substitution

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the
literal matrix pair at the root is bounded by one additive high contribution
from `Q` and `h`. The physical coefficient is pulled back along the fixed
adapted coordinate map. Its norm is measured on the stated physical compact
ball, and the root norm on the stated state ball.

The signed-datum estimate below consumes this primitive estimate. The later
transported nullvector estimates also consume it; their flow and inverse-chart
pullbacks remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

open ActualCarriers FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame

variable {n d : ℕ}

/-- The fixed physical projection used in the primitive norms for
`app:ch_regular_base:lem:characteristic-kernel`. -/
def rootPhysicalPosition (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)) :
    RootState (Euclidean d) →L[ℝ] Euclidean n :=
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ ℝ (Euclidean d × Euclidean d)).prod
      ((ContinuousLinearMap.fst ℝ (Euclidean d) (Euclidean d)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d))))

/-- No derivative shift or multiplied high norms are needed to form the
actual root pencil and time coefficient from `Q,h`. Fixed value bounds and
fixed compact domains determine the constants before both primitive functions
(`app:ch_regular_base:lem:characteristic-kernel`, nullvector inputs). -/
theorem exists_rootCoefficientPair_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : RootState (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M : ℝ)
    (himage : MapsTo (rootPhysicalPosition e) (closedBall z ρ) (closedBall x R)) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n)) (D : Set (RootState (Euclidean d))),
        IsOpen Ω → IsOpen D → closedBall x R ⊆ Ω → closedBall z ρ ⊆ D →
        MapsTo (rootPhysicalPosition e) D Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ h D →
          cNorm (closedBall x R) 0 Q ≤ M → cNorm (closedBall z ρ) 0 h ≤ M →
          ∀ m, cNorm (closedBall z ρ) m (fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w)) ≤
            C m * (1 + cNorm (closedBall x R) m Q + cNorm (closedBall z ρ) m h) := by
  let K := closedBall z ρ
  let KQ := closedBall x R
  let η : RootState (Euclidean d) → Euclidean d := fun w ↦ w.2.2
  let T := closedBall (0 : Fin n → MetricTensor n) M ×ˢ
    (closedBall (0 : ℝ) M ×ˢ (η '' K))
  have hT : IsCompact T := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).image
      (continuous_snd.comp continuous_snd)))
  let G : (Fin n → MetricTensor n) × (ℝ × Euclidean d) → MetricTensor n × MetricTensor n :=
    fun p ↦ (pencil p.1 (e.symm p.2), pencil p.1 (e.symm (1, 0)))
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_pencil.comp (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd))).prodMk
      (contDiff_pencil.comp (contDiff_fst.prodMk contDiff_const))
  choose A hA hb using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn z hρ hT (le_refl m)
      (fun _ _ ↦ hG.contDiffAt.of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  let L := rootPhysicalPosition e
  let a := fun m ↦ linearNormCost L m
  let b := fun m ↦ cNorm K m η
  have ha (m) : 0 < a m := linearNormCost_pos L m
  have hb0 (m) : 0 ≤ b m := cNorm_nonneg _ _ _
  refine ⟨fun m ↦ A m * (1 + a m + b m),
    fun m ↦ mul_pos (hA m) (by linarith [ha m, hb0 m]), ?_⟩
  intro Ω D hΩ hD hKQ hK hmap Q h hQ hh hQM hhM m
  let f := fun w ↦ (Q (L w), (h w, η w))
  have hQp : ContDiffOn ℝ ∞ (Q ∘ L) D := hQ.comp L.contDiff.contDiffOn hmap
  have hf : ContDiffOn ℝ ∞ f D := hQp.prodMk (hh.prodMk contDiffOn_snd.snd)
  have hQl (j : ℕ) : ∀ y ∈ KQ, ContDiffAt ℝ j Q y :=
    fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hKQ hy))).of_le (by simp)
  have hhl (j : ℕ) : ∀ w ∈ K, ContDiffAt ℝ j h w :=
    fun w hw ↦ (hh.contDiffAt (hD.mem_nhds (hK hw))).of_le (by simp)
  have hft : MapsTo f K T := by
    intro w hw
    refine ⟨?_, ?_, mem_image_of_mem η hw⟩
    · rw [mem_closedBall, dist_zero_right]
      have h0 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x R)
        (hQl 0) (himage hw) (le_refl 0)
      simpa only [norm_iteratedFDeriv_zero] using h0.trans hQM
    · rw [mem_closedBall, dist_zero_right]
      have h0 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z ρ)
        (hhl 0) hw (le_refl 0)
      simpa only [norm_iteratedFDeriv_zero] using h0.trans hhM
  have hQhigh : cNorm K m (Q ∘ L) ≤ a m * cNorm KQ m Q :=
    cNorm_comp_linear_le L (isCompact_closedBall _ _) hΩ hKQ hQ himage m
  have hinner := cNorm_prodMk_le_on K (isCompact_closedBall _ _) m (hhl m)
    (fun _ _ ↦ contDiffAt_snd.snd (n := (m : ℕ∞ω)))
  have houter := cNorm_prodMk_le_on K (isCompact_closedBall _ _) m
    (fun w hw ↦ (hQp.contDiffAt (hD.mem_nhds (hK hw))).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
    (fun w hw ↦ (hhl m w hw).prodMk contDiffAt_snd.snd)
  have hn : cNorm K m f ≤ a m * cNorm KQ m Q + cNorm K m h + b m := by
    dsimp [f, b] at *
    linarith
  have hbound := hb m D hD hK f hf hft
  change cNorm K m (fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w)) ≤
    A m * (1 + cNorm K m f) at hbound
  apply hbound.trans
  have hq0 := cNorm_nonneg KQ m Q
  have hh0 := cNorm_nonneg K m h
  have hfinal : 1 + cNorm K m f ≤
      (1 + a m + b m) * (1 + cNorm KQ m Q + cNorm K m h) := by
    nlinarith [mul_nonneg (ha m).le hh0, mul_nonneg (hb0 m) hq0,
      mul_nonneg (hb0 m) hh0, ha m, hb0 m]
  exact (mul_le_mul_of_nonneg_left hfinal (hA m).le).trans_eq (by ring)

/-- Primitive, zero-loss bounds for the actual root nullvectors, signed
datum and root complement. Every matrix value bound is derived from `Q,h`;
only the original adjugate and transport gaps are assumed. The fixed balls,
coordinate map and low budgets precede all primitive functions and masks.
The transported nullvectors consume the first two conclusions, and the row
construction consumes the literal `pencilSignedDatum` conclusion
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem exists_rootMinorData_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : RootState (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M S : ℝ) (r c : Fin n)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (himage : MapsTo (rootPhysicalPosition e) (closedBall z ρ) (closedBall x R)) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n)) (D : Set (RootState (Euclidean d))),
        IsOpen Ω → IsOpen D → closedBall x R ⊆ Ω → closedBall z ρ ⊆ D →
        MapsTo (rootPhysicalPosition e) D Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n)
          (h σ : RootState (Euclidean d) → ℝ),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ h D → ContDiffOn ℝ ∞ σ D →
          cNorm (closedBall x R) 0 Q ≤ M → cNorm (closedBall z ρ) 0 h ≤ M →
          cNorm (closedBall z ρ) 0 σ ≤ S →
          (∀ w ∈ closedBall z ρ, (rootPencil e Q h w).det = 0 ∧
            μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) →
          ∀ m,
            let H := 1 + cNorm (closedBall x R) m Q + cNorm (closedBall z ρ) m h +
              cNorm (closedBall z ρ) m σ
            cNorm (closedBall z ρ) m (fun w ↦ minorRightNullvector (rootPencil e Q h w) r c) ≤ C m * H ∧
            cNorm (closedBall z ρ) m
              (fun w ↦ minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c) ≤ C m * H ∧
            cNorm (closedBall z ρ) m (pencilSignedDatum e Q h r c σ) ≤ C m * H ∧
            cNorm (closedBall z ρ) m
              (fun w ↦ minorComplementInverse (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c 0) ≤ C m * H := by
  obtain ⟨A, hA, hpair⟩ := exists_rootCoefficientPair_cNorm_bounds e z hρ x R M himage
  let N := A 0 * (1 + M + M)
  obtain ⟨B, hB, hnull⟩ := exists_minorNullvectors_cNorm_bounds z hρ r c N hμ hν
  obtain ⟨F, hF, hdatum⟩ := exists_minorSignedDatum_cNorm_bounds z hρ r c N S hμ hν
  obtain ⟨J, hJ, hcomp⟩ := exists_minorComplement_cNorm_bounds z hρ r c N hμ hν
  let L := fun m ↦ B m + F m + J m
  have hL m : 0 < L m := add_pos (add_pos (hB m) (hF m)) (hJ m)
  refine ⟨fun m ↦ L m * (1 + A m), fun m ↦ mul_pos (hL m) (by linarith [hA m]), ?_⟩
  intro Ω D hΩ hD hKQ hK hmap Q h σ hQ hh hσ hQM hhM hσM hgaps m
  let K := closedBall z ρ
  let U := fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w)
  have hU : ContDiffOn ℝ ∞ U D :=
    (contDiffOn_rootPencil e hQ hh hmap).prodMk (contDiffOn_rootTimeCoefficient e hQ hmap)
  have hp j := hpair Ω D hΩ hD hKQ hK hmap Q h hQ hh hQM hhM j
  have hlow : cNorm K 0 U ≤ N := (hp 0).trans
    (mul_le_mul_of_nonneg_left (by linarith) (hA 0).le)
  have hclass : MapsTo U K (minorCoefficientClass r c N μ ν) := by
    intro w hw
    have hn : ‖U w‖ ≤ N := by
      have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z ρ)
        (fun y hy ↦ (hU.contDiffAt (hD.mem_nhds (hK hy))).of_le
          (show (0 : ℕ∞ω) ≤ ∞ by simp)) hw (le_refl 0)
      have hb' : ‖U w‖ ≤ cNorm K 0 U := by
        simpa only [norm_iteratedFDeriv_zero] using hb
      exact hb'.trans hlow
    exact ⟨(norm_fst_le (U w)).trans hn, (norm_snd_le (U w)).trans hn, hgaps w hw⟩
  obtain ⟨hk, hl⟩ := hnull D hD hK U hU hclass m
  have hd := hdatum D hD hK U σ hU hσ hclass hσM m
  have hj := hcomp D hD hK U hU hclass m
  have hq0 := cNorm_nonneg (closedBall x R) m Q
  have hh0 := cNorm_nonneg K m h
  have hs0 := cNorm_nonneg K m σ
  have hhigh : 1 + cNorm K m U + cNorm K m σ ≤
      (1 + A m) * (1 + cNorm (closedBall x R) m Q + cNorm K m h + cNorm K m σ) := by
    nlinarith [hp m, mul_nonneg (hA m).le hs0]
  have hmajor (a : ℝ) (ha : 0 ≤ a) (haL : a ≤ L m) :
      a * (1 + cNorm K m U + cNorm K m σ) ≤
        (L m * (1 + A m)) *
          (1 + cNorm (closedBall x R) m Q + cNorm K m h + cNorm K m σ) := by
    apply (mul_le_mul_of_nonneg_left hhigh ha).trans
    calc
      _ ≤ L m * ((1 + A m) *
          (1 + cNorm (closedBall x R) m Q + cNorm K m h + cNorm K m σ)) :=
        mul_le_mul_of_nonneg_right haL (mul_nonneg (by linarith [hA m]) (by linarith))
      _ = _ := by ring
  have hBk : B m ≤ L m := by dsimp [L]; linarith [hF m, hJ m]
  have hFk : F m ≤ L m := by dsimp [L]; linarith [hB m, hJ m]
  have hJk : J m ≤ L m := by dsimp [L]; linarith [hB m, hF m]
  refine ⟨hk.trans ((mul_le_mul_of_nonneg_left (by linarith) (hB m).le).trans
      (hmajor (B m) (hB m).le hBk)),
    hl.trans ((mul_le_mul_of_nonneg_left (by linarith) (hB m).le).trans
      (hmajor (B m) (hB m).le hBk)),
    hd.trans (hmajor (F m) (hF m).le hFk),
    hj.trans ((mul_le_mul_of_nonneg_left (by linarith) (hJ m).le).trans
      (hmajor (J m) (hJ m).le hJk))⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
