module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PrimitiveNorm
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.ComplexColumns

/-!
# Primitive bounds for the literal local characteristic amplitudes

The fixed outer physical two-time ball contains the entire potential domain;
its root-state and flow images lie in the specified compact primitive balls.
The smaller working ball has an open inverse-chart margin. The forward
characteristic ball is a product of intervals and a label ball, so every
oriented time segment, including the diagonal, remains in that ball.

The reserve is nine: four for transported primitives, one for the potential,
two for the row pullback, and two for the full physical correction residual.
All constants precede all six primitive functions. This supplies the local
`W₀,W₁,PW₁` estimates for `app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:eq:two-term-null-identity`, and
`app:ch_regular_base:eq:energy-complete-residual`. The actual uniform primitive
family and conic extension remain with the regular-sector construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

variable {n d : ℕ}

/-- Fixed-shift, single-high bounds for the existing signed datum, physical
potential, signed exponential row, leading/correction columns and full physical
correction residual. No intermediate norm or smoothness premise is assumed.
The fixed C9 primitive budgets and original adjugate/transport gaps produce
every intermediate low bound. The full zeroth-order coefficient `B` remains
inside each physical action. Consumers: `EvolutionIntegral.SymbolBudgets`
after conic extension, and the complete residual in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_pencilPrimitiveAmplitudes_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (t₀ : ℝ) (p x : Euclidean d × Euclidean d) (xQ : Euclidean n)
    {ρ ρo σ R τ S L F RQ M : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hτ : 0 < τ)
    (hρo : ρ < ρo) (hσR : σ < R) (hτS : τ < S)
    (hρoS : ρo ≤ S) (hRL : R < L) (hRF : 2 * R ≤ F)
    (hRQ : 0 < RQ) (hM : 0 ≤ M) (r c : Fin n)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hrootImage : MapsTo (rootPhysicalPosition e)
      (closedBall (t₀, p) L) (closedBall xQ RQ))
    (hphysicalImage : MapsTo (PhysicalAction.physicalPosition e)
      (closedBall (t₀, (t₀, x)) S) (closedBall xQ RQ)) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (Ω : Set (Euclidean n)) (D : Set (RootState (Euclidean d)))
        (V : Set (TwoTimePoint (Euclidean d))) (W : Set (RootState (Euclidean d) × ℝ)),
        IsOpen Ω → IsOpen D → IsOpen V → IsOpen W →
        closedBall xQ RQ ⊆ Ω → closedBall (t₀, p) L ⊆ D →
        closedBall (t₀, (t₀, x)) S ⊆ V → closedBall ((t₀, p), 0) F ⊆ W →
        MapsTo (rootPhysicalPosition e) D Ω → MapsTo (PhysicalAction.physicalPosition e) V Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
          (h mask : RootState (Euclidean d) → ℝ)
          (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiffOn ℝ ∞ h D → ContDiffOn ℝ ∞ mask D →
          ContDiffOn ℝ ∞ Φ W → ContDiffOn ℝ ∞ C.symm V →
          (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ →
          MapsTo (twoTimeFlowInput ∘ C.symm) V W →
          MapsTo (twoTimeFlowInput ∘ C.symm) (closedBall (t₀, (t₀, x)) S)
            (closedBall ((t₀, p), 0) F) →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) V D →
          MapsTo (fun y ↦ twoTimeState Φ (C.symm y)) (closedBall (t₀, (t₀, x)) S)
            (closedBall (t₀, p) L) →
          MapsTo C (closedBall (t₀, (t₀, p)) σ) (closedBall (t₀, (t₀, x)) τ) →
          MapsTo C (ball (t₀, (t₀, p)) R) (ball (t₀, (t₀, x)) S) →
          MapsTo C.symm (closedBall (t₀, (t₀, x)) ρ) (closedBall (t₀, (t₀, p)) σ) →
          MapsTo C.symm (ball (t₀, (t₀, x)) ρo) (ball (t₀, (t₀, p)) R) →
          ball (t₀, (t₀, x)) ρo ⊆ C.target →
          cNorm (closedBall xQ RQ) 9 Q ≤ M → cNorm (closedBall xQ RQ) 9 B ≤ M →
          cNorm (closedBall (t₀, p) L) 9 h ≤ M → cNorm (closedBall (t₀, p) L) 9 mask ≤ M →
          cNorm (closedBall ((t₀, p), 0) F) 9 Φ ≤ M →
          cNorm (closedBall (t₀, (t₀, x)) S) 9 C.symm ≤ M →
          (∀ w ∈ closedBall (t₀, p) L, (rootPencil e Q h w).det = 0 ∧
            μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) →
          let H := pencilPrimitiveNorm (closedBall xQ RQ) (closedBall (t₀, p) L)
            (closedBall ((t₀, p), 0) F) (closedBall (t₀, (t₀, x)) S) Q B h mask Φ C.symm
          ContDiffOn ℝ ∞ (pencilSignedDatum e Q h r c mask) (ball (t₀, p) L) ∧
          ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) (ball (t₀, (t₀, x)) S) ∧
          ContDiffOn ℝ ∞ (pencilSignedRow e Q B h Φ C r c mask) (ball (t₀, (t₀, x)) ρo) ∧
          (∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c mask j)
              (ball (t₀, (t₀, x)) ρo) ∧
            ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c mask j)
              (ball (t₀, (t₀, x)) ρo) ∧
            ContDiffOn ℝ ∞ (adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j))
              (ball (t₀, (t₀, x)) ρo)) ∧
          ∀ m,
            cNorm (closedBall (t₀, p) L) m (pencilSignedDatum e Q h r c mask) ≤ A m * H (m + 9) ∧
            cNorm (closedBall (t₀, (t₀, x)) S) m (pencilTransportPotential e Q B h Φ C r c) ≤
              A m * H (m + 9) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m (pencilSignedRow e Q B h Φ C r c mask) ≤
              A m * H (m + 9) ∧
            (∀ j, cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilLeadingColumn e Q B h Φ C r c mask j) ≤ A m * H (m + 9) ∧
              cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionColumn e Q B h Φ C r c mask j) ≤ A m * H (m + 9) ∧
              cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j)) ≤
                  A m * H (m + 9)) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilLeadingComplexMatrix e Q B h Φ C r c mask) ≤ A m * H (m + 9) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionComplexMatrix e Q B h Φ C r c mask) ≤ A m * H (m + 9) ∧
            cNorm (closedBall (t₀, (t₀, x)) ρ) m
                (pencilCorrectionResidualComplexMatrix e Q B h Φ C r c mask) ≤ A m * H (m + 9) := by
  have hS : 0 < S := hτ.trans hτS
  have hL : 0 < L := hσ.trans (hσR.trans hRL)
  have hF : 0 < F := lt_of_lt_of_le (by linarith : 0 < 2 * R) hRF
  have hρS : ρ ≤ S := hρo.le.trans hρoS
  obtain ⟨K, hK, htransport⟩ := exists_pencilChartPrimitives_cNorm_bounds e
    (t₀, (t₀, x)) hS ((t₀, p), 0) hF (t₀, p) hL xQ hRQ hM r c hμ hν hrootImage
  obtain ⟨D₀, hD₀, hdatum⟩ := exists_rootMinorData_cNorm_bounds e
    (t₀, p) hL xQ RQ M M r c hμ hν hrootImage
  let MP := M + K 1 * (1 + 4 * M)
  obtain ⟨P, hP, hpotential⟩ := PhysicalAction.exists_pencilTransportPotential_cNorm_bounds
    e (t₀, (t₀, x)) hS xQ RQ MP hphysicalImage
  let CP := fun m ↦ P m * (1 + 2 * K (m + 1))
  have hCP m : 0 < CP m := mul_pos (hP m) (by linarith [hK (m + 1)])
  let MR := (CP 3 + D₀ 3) * (1 + 6 * M) + M
  have hMR : 0 ≤ MR := by
    dsimp [MR]
    exact add_nonneg (mul_nonneg (add_nonneg (hCP 3).le (hD₀ 3).le) (by linarith)) hM
  obtain ⟨J, hJ, hrow⟩ := RowPullback.exists_twoTimeRowTransport_cNorm_bounds
    (ι := Fin n) t₀ p x hρ hσ hτ hρo hσR hτS hMR
  let CR := fun m ↦ J m * (3 + CP (m + 2) + D₀ (m + 2))
  have hCR m : 0 < CR m := mul_pos (hJ m) (by linarith [hCP (m + 2), hD₀ (m + 2)])
  let MA := M + (K 2 + CR 2) * (1 + 6 * M)
  obtain ⟨Z, hZ, hamp⟩ := PhysicalAction.exists_pencilPhysicalAmplitudes_cNorm_bounds
    e (t₀, (t₀, x)) hρ xQ RQ MA
      (fun y hy ↦ hphysicalImage (closedBall_subset_closedBall hρS hy))
  let CA := fun m ↦ Z m * (1 + 3 * K (m + 2) + CR (m + 2))
  have hCA m : 0 < CA m := mul_pos (hZ m) (by linarith [hK (m + 2), hCR (m + 2)])
  refine ⟨fun m ↦ (1 + (n : ℝ) ^ 2) * (D₀ m + CP m + CR m + CA m),
    fun m ↦ mul_pos (by positivity)
      (add_pos (add_pos (add_pos (hD₀ m) (hCP m)) (hCR m)) (hCA m)), ?_⟩
  intro Ω D V W hΩ hD hV hW hKQ hKz hKC hKΦ hrootPhys hphys
    Q B h mask Φ C hQ hB hh hmask hΦ hCi hC hflow hflowK hstate hstateK
    hforwardK hforward hinverseK hinverse htarget hQM hBM hhM hmM hΦM hCiM hgaps H
  let KQ := closedBall xQ RQ
  let Kz := closedBall (t₀, p) L
  let KΦ : Set (RootState (Euclidean d) × ℝ) := closedBall ((t₀, p), 0) F
  let KC := closedBall (t₀, (t₀, x)) S
  let KA := closedBall (t₀, (t₀, x)) ρ
  let U := ball (t₀, (t₀, x)) ρo
  let k := pencilChartRight e Q h Φ C r c
  let l := pencilChartLeft e Q h Φ C r c
  let b := pencilChartComplement e Q h Φ C r c
  let a₀ := pencilSignedDatum e Q h r c mask
  let pot := pencilTransportPotential e Q B h Φ C r c
  let a := pencilSignedRow e Q B h Φ C r c mask
  have hH (i : ℕ) : 1 ≤ H i := by
    dsimp [H, pencilPrimitiveNorm]
    linarith [cNorm_nonneg KQ i Q, cNorm_nonneg KQ i B, cNorm_nonneg Kz i h,
      cNorm_nonneg Kz i mask, cNorm_nonneg KΦ i Φ, cNorm_nonneg KC i C.symm]
  have hHmono {i j : ℕ} (hij : i ≤ j) : H i ≤ H j := by
    dsimp [H, pencilPrimitiveNorm]
    linarith [cNorm_mono_order (f := Q) (s := KQ) hij,
      cNorm_mono_order (f := B) (s := KQ) hij, cNorm_mono_order (f := h) (s := Kz) hij,
      cNorm_mono_order (f := mask) (s := Kz) hij, cNorm_mono_order (f := Φ) (s := KΦ) hij,
      cNorm_mono_order (f := C.symm) (s := KC) hij]
  have hHlow {i : ℕ} (hi : i ≤ 9) : H i ≤ 1 + 6 * M := by
    dsimp [H, pencilPrimitiveNorm]
    linarith [(cNorm_mono_order hi).trans hQM, (cNorm_mono_order hi).trans hBM,
      (cNorm_mono_order hi).trans hhM, (cNorm_mono_order hi).trans hmM,
      (cNorm_mono_order hi).trans hΦM, (cNorm_mono_order hi).trans hCiM]
  have hparts (i : ℕ) :
      1 + cNorm KQ i Q + cNorm KQ i B ≤ H i ∧
      1 + cNorm KQ i Q + cNorm Kz i h + cNorm Kz i mask ≤ H i ∧
      1 + cNorm KQ i Q + cNorm Kz i h + cNorm KΦ i Φ + cNorm KC i C.symm ≤ H i ∧
      cNorm KΦ i Φ ≤ H i ∧ cNorm KC i C.symm ≤ H i := by
    dsimp [H, pencilPrimitiveNorm]
    have hq := cNorm_nonneg KQ i Q
    have hb := cNorm_nonneg KQ i B
    have hh := cNorm_nonneg Kz i h
    have hm := cNorm_nonneg Kz i mask
    have hf := cNorm_nonneg KΦ i Φ
    have hc := cNorm_nonneg KC i C.symm
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨⟨V', hV', hKC', hV'V, hk, hl, hb⟩, hkb, hklow, _⟩ :=
    htransport Ω D V W hΩ hD hV hW hKQ hKz hKC hKΦ hrootPhys Q h Φ C hQ hh hΦ hCi
      hflow hflowK hstate hstateK
      ((cNorm_mono_order (by omega : 6 ≤ 9)).trans hQM)
      ((cNorm_mono_order (by omega : 6 ≤ 9)).trans hhM)
      ((cNorm_mono_order (by omega : 6 ≤ 9)).trans hΦM)
      ((cNorm_mono_order (by omega : 6 ≤ 9)).trans hCiM) hgaps
  have hprim (i : ℕ) : cNorm KC i k ≤ K i * H (i + 4) ∧
      cNorm KC i l ≤ K i * H (i + 4) ∧ cNorm KC i b ≤ K i * H (i + 4) := by
    have hm := mul_le_mul_of_nonneg_left (hparts (i + 4)).2.2.1 (hK i).le
    exact ⟨(hkb i).1.trans hm, (hkb i).2.1.trans hm, (hkb i).2.2.trans hm⟩
  have hdatumBound (i : ℕ) : cNorm Kz i a₀ ≤ D₀ i * H i := by
    have hd := (hdatum Ω D hΩ hD hKQ hKz hrootPhys Q h mask hQ hh hmask
      ((cNorm_mono_order (by omega : 0 ≤ 9)).trans hQM)
      ((cNorm_mono_order (by omega : 0 ≤ 9)).trans hhM)
      ((cNorm_mono_order (by omega : 0 ≤ 9)).trans hmM) hgaps i).2.2.1
    exact hd.trans (mul_le_mul_of_nonneg_left (hparts i).2.1 (hD₀ i).le)
  have hdatumSmooth : ContDiffOn ℝ ∞ a₀ (ball (t₀, p) L) :=
    contDiffOn_pencilSignedDatum_ball e hQ hh hmask hrootPhys (t₀, p) L hKz r c
      (fun w hw ↦ ⟨abs_pos.mp (hμ.trans_le (hgaps w hw).2.1),
        abs_pos.mp (hν.trans_le (hgaps w hw).2.2)⟩)
  have hMMP : M ≤ MP := by
    dsimp [MP]
    exact le_add_of_nonneg_right (mul_nonneg (hK 1).le (by linarith))
  have hkMP : cNorm KC 1 k ≤ MP := (hklow 1 (by omega)).1.trans (by dsimp [MP]; linarith)
  have hlMP : cNorm KC 1 l ≤ MP := (hklow 1 (by omega)).2.1.trans (by dsimp [MP]; linarith)
  have hpotRaw := hpotential Ω V' hΩ hV' hKQ hKC' (fun y hy ↦ hphys (hV'V hy))
    Q B h Φ C r c hQ hB hk hl
    (((cNorm_mono_order (by omega : 1 ≤ 9)).trans hQM).trans hMMP)
    (((cNorm_mono_order (by omega : 1 ≤ 9)).trans hBM).trans hMMP) hkMP hlMP
  have hpotSmooth : ContDiffOn ℝ ∞ pot V' :=
    PhysicalAction.contDiff_vectorPairing.comp_contDiffOn
      (hl.prodMk (contDiffOn_adaptedPencilApply e hQ hB hV'
        (fun y hy ↦ hphys (hV'V hy)) hk))
  have hpotBound (i : ℕ) : cNorm KC i pot ≤ CP i * H (i + 5) := by
    apply (hpotRaw i).trans
    have hq := (hparts (i + 1)).1.trans (hHmono (by omega : i + 1 ≤ i + 5))
    have hk' := (hprim (i + 1)).1
    have hl' := (hprim (i + 1)).2.1
    have hn : 1 + cNorm KQ (i + 1) Q + cNorm KQ (i + 1) B +
        cNorm KC (i + 1) k + cNorm KC (i + 1) l ≤
        (1 + 2 * K (i + 1)) * H (i + 5) := by
      simp only [Nat.add_assoc] at hk' hl'
      nlinarith only [hq, hk', hl']
    exact (mul_le_mul_of_nonneg_left hn (hP i).le).trans_eq (by dsimp [CP]; ring)
  have hsmall : KA ⊆ KC := closedBall_subset_closedBall hρS
  have hUV' : U ⊆ V' := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall hρoS)).trans hKC'
  have hUV : U ⊆ V := hUV'.trans hV'V
  have hKU : KA ⊆ U := closedBall_subset_ball hρo
  have hpotS := hpotSmooth.mono (ball_subset_closedBall.trans hKC')
  have haR := hdatumSmooth.mono (ball_subset_ball hRL.le)
  have hΦR := hΦ.mono ((ball_subset_closedBall.trans
    (closedBall_subset_closedBall hRF)).trans hKΦ)
  have hiU := hCi.mono hUV
  have hpotRestrict (i : ℕ) : cNorm (closedBall (t₀, (t₀, x)) τ) i pot ≤ cNorm KC i pot :=
    cNorm_restrict_of_smooth (closedBall_subset_closedBall hτS.le)
      (isCompact_closedBall _ _) hV' hKC' hpotSmooth i
  have haAt (i : ℕ) (w : RootState (Euclidean d)) (hw : w ∈ Kz) :
      ContDiffAt ℝ i a₀ w := by
    have hpair := ((contDiffOn_rootPencil e hQ hh hrootPhys).prodMk
      (contDiffOn_rootTimeCoefficient e hQ hrootPhys)).contDiffAt (hD.mem_nhds (hKz hw))
    have hg : (rootPencil e Q h w, rootTimeCoefficient e Q w) ∈ minorNullvectorDomain r c :=
      ⟨abs_pos.mp (hμ.trans_le (hgaps w hw).2.1), abs_pos.mp (hν.trans_le (hgaps w hw).2.2)⟩
    have hlAt := ((minorNullvectorDomain_regular r c (m := ∞)).2.2.contDiffAt
      ((minorNullvectorDomain_regular r c (m := ∞)).1.mem_nhds hg)).comp w hpair
    exact ((hmask.contDiffAt (hD.mem_nhds (hKz hw))).smul hlAt).of_le (by simp)
  have hdatumRestrict (i : ℕ) : cNorm (closedBall (t₀, p) σ) i a₀ ≤ cNorm Kz i a₀ :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall (hσR.trans hRL).le)
      (isCompact_closedBall _ _) (haAt i)
  have hΦRestrict (i : ℕ) : cNorm (closedBall ((t₀, p), 0) (2 * σ)) i Φ ≤ cNorm KΦ i Φ :=
    cNorm_restrict_of_smooth (closedBall_subset_closedBall (by linarith))
      (isCompact_closedBall _ _) hW hKΦ hΦ i
  have hiRestrict (i : ℕ) : cNorm KA i C.symm ≤ cNorm KC i C.symm :=
    cNorm_restrict_of_smooth hsmall (isCompact_closedBall _ _) hV hKC hCi i
  have hpLow : cNorm (closedBall (t₀, (t₀, x)) τ) 3 pot ≤ MR := by
    apply ((hpotRestrict 3).trans (hpotBound 3)).trans
    have hl := mul_le_mul_of_nonneg_left (hHlow (by omega : 3 + 5 ≤ 9)) (hCP 3).le
    dsimp [MR]
    nlinarith [mul_nonneg (hD₀ 3).le (by linarith : 0 ≤ 1 + 6 * M)]
  have haLow : cNorm (closedBall (t₀, p) σ) 3 a₀ ≤ MR := by
    apply ((hdatumRestrict 3).trans (hdatumBound 3)).trans
    have hl := mul_le_mul_of_nonneg_left (hHlow (by omega : 3 ≤ 9)) (hD₀ 3).le
    dsimp [MR]
    nlinarith [mul_nonneg (hCP 3).le (by linarith : 0 ≤ 1 + 6 * M)]
  have hMMR : M ≤ MR := by
    dsimp [MR]
    exact le_add_of_nonneg_left (mul_nonneg (add_nonneg (hCP 3).le (hD₀ 3).le) (by linarith))
  have hrowRaw := hrow pot a₀ Φ C hC hpotS haR hΦR hiU hforwardK hforward hinverseK
    (fun y hy ↦ htarget (hKU hy)) hpLow haLow
    (((hΦRestrict 3).trans ((cNorm_mono_order (by omega : 3 ≤ 9)).trans hΦM)).trans hMMR)
    (((hiRestrict 3).trans ((cNorm_mono_order (by omega : 3 ≤ 9)).trans hCiM)).trans hMMR)
  have hrowBound (i : ℕ) : cNorm KA i a ≤ CR i * H (i + 7) := by
    apply (hrowRaw i).2.trans
    have hp' := (hpotRestrict (i + 2)).trans (hpotBound (i + 2))
    have ha' := ((hdatumRestrict (i + 2)).trans (hdatumBound (i + 2))).trans
      (mul_le_mul_of_nonneg_left (hHmono (by omega : i + 2 ≤ i + 7)) (hD₀ (i + 2)).le)
    have hf' := (hΦRestrict (i + 2)).trans
      ((hparts (i + 2)).2.2.2.1.trans (hHmono (by omega : i + 2 ≤ i + 7)))
    have hi' := (hiRestrict (i + 2)).trans
      ((hparts (i + 2)).2.2.2.2.trans (hHmono (by omega : i + 2 ≤ i + 7)))
    have hn : 1 + cNorm (closedBall (t₀, (t₀, x)) τ) (i + 2) pot +
        cNorm (closedBall (t₀, p) σ) (i + 2) a₀ +
        cNorm (closedBall ((t₀, p), 0) (2 * σ)) (i + 2) Φ + cNorm KA (i + 2) C.symm ≤
        (3 + CP (i + 2) + D₀ (i + 2)) * H (i + 7) := by
      simp only [Nat.add_assoc] at hp'
      nlinarith only [hp', ha', hf', hi', hH (i + 7)]
    exact (mul_le_mul_of_nonneg_left hn (hJ i).le).trans_eq (by dsimp [CR]; ring)
  have hCf := RowPullback.contDiffOn_twoTimeProjection_ball t₀ p (hσ.trans hσR) hΦR
  have hchar : ContDiffOn ℝ ∞ (rowTransport (pot ∘ C) a₀) (ball (t₀, (t₀, p)) R) := by
    have hcc : ContDiffOn ℝ ∞ (pot ∘ C) (ball (t₀, (t₀, p)) R) :=
      hpotS.comp (by simpa only [hC] using hCf) hforward
    have hh := contDiffOn_rowTransport isOpen_ball (convex_ball t₀ R).ordConnected
      (isOpen_ball (x := p) (ε := R))
      (by simpa only [ball_prod_same] using hcc)
      (by simpa only [ball_prod_same] using haR) (mem_ball_self (hσ.trans hσR))
    simpa only [ball_prod_same] using hh
  have hrowSmooth : ContDiffOn ℝ ∞ a U :=
    (hchar.comp hiU hinverse).congr (fun y hy ↦
      twoTimeRowTransport_eq_pullback hC pot a₀ (htarget hy))
  have hsmallPrim (i : ℕ) : cNorm KA i k ≤ K i * H (i + 4) ∧
      cNorm KA i l ≤ K i * H (i + 4) ∧ cNorm KA i b ≤ K i * H (i + 4) :=
    ⟨(cNorm_restrict_of_smooth hsmall (isCompact_closedBall _ _) hV' hKC' hk i).trans (hprim i).1,
      (cNorm_restrict_of_smooth hsmall (isCompact_closedBall _ _) hV' hKC' hl i).trans (hprim i).2.1,
      (cNorm_restrict_of_smooth hsmall (isCompact_closedBall _ _) hV' hKC' hb i).trans (hprim i).2.2⟩
  have hMMA : M ≤ MA := by
    dsimp [MA]
    exact le_add_of_nonneg_right (mul_nonneg (add_nonneg (hK 2).le (hCR 2).le) (by linarith))
  have hkMA : K 2 * H (2 + 4) ≤ MA := by
    have hlow := mul_le_mul_of_nonneg_left (hHlow (by omega : 2 + 4 ≤ 9)) (hK 2).le
    dsimp [MA]
    nlinarith [mul_nonneg (hCR 2).le (by linarith : 0 ≤ 1 + 6 * M)]
  have haMA : cNorm KA 2 a ≤ MA := by
    apply (hrowBound 2).trans
    have hlow := mul_le_mul_of_nonneg_left (hHlow (by omega : 2 + 7 ≤ 9)) (hCR 2).le
    dsimp [MA]
    nlinarith [mul_nonneg (hK 2).le (by linarith : 0 ≤ 1 + 6 * M)]
  obtain ⟨_, hsmooth, hcolumns⟩ := hamp Ω U hΩ isOpen_ball hKQ hKU
    (fun y hy ↦ hphys (hUV hy)) Q B h Φ C r c mask hQ hB
    (hk.mono hUV') (hl.mono hUV') hrowSmooth (hb.mono hUV')
    (((cNorm_mono_order (by omega : 2 ≤ 9)).trans hQM).trans hMMA)
    (((cNorm_mono_order (by omega : 2 ≤ 9)).trans hBM).trans hMMA)
    ((hsmallPrim 2).1.trans hkMA) ((hsmallPrim 2).2.1.trans hkMA) haMA
    ((hsmallPrim 2).2.2.trans hkMA)
  have hcolumnsBound (i : ℕ) (j : Fin n) :
      cNorm KA i (pencilLeadingColumn e Q B h Φ C r c mask j) ≤ CA i * H (i + 9) ∧
      cNorm KA i (pencilCorrectionColumn e Q B h Φ C r c mask j) ≤ CA i * H (i + 9) ∧
      cNorm KA i (adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j)) ≤
        CA i * H (i + 9) := by
    have hq := (hparts (i + 2)).1.trans (hHmono (by omega : i + 2 ≤ i + 9))
    have hk' := (hsmallPrim (i + 2)).1.trans
      (mul_le_mul_of_nonneg_left (hHmono (by omega : i + 2 + 4 ≤ i + 9)) (hK (i + 2)).le)
    have hl' := (hsmallPrim (i + 2)).2.1.trans
      (mul_le_mul_of_nonneg_left (hHmono (by omega : i + 2 + 4 ≤ i + 9)) (hK (i + 2)).le)
    have hb' := (hsmallPrim (i + 2)).2.2.trans
      (mul_le_mul_of_nonneg_left (hHmono (by omega : i + 2 + 4 ≤ i + 9)) (hK (i + 2)).le)
    have ha' := hrowBound (i + 2)
    simp only [Nat.add_assoc] at ha'
    have hn : 1 + cNorm KQ (i + 2) Q + cNorm KQ (i + 2) B +
        cNorm KA (i + 2) k + cNorm KA (i + 2) l + cNorm KA (i + 2) a + cNorm KA (i + 2) b ≤
        (1 + 3 * K (i + 2) + CR (i + 2)) * H (i + 9) := by
      nlinarith only [hq, hk', hl', hb', ha']
    have hm := mul_le_mul_of_nonneg_left hn (hZ i).le
    rw [← mul_assoc] at hm
    exact ⟨((hcolumns i).2 j).1.trans hm, ((hcolumns i).2 j).2.1.trans hm,
      ((hcolumns i).2 j).2.2.trans hm⟩
  refine ⟨hdatumSmooth, hpotS, hrowSmooth, hsmooth, ?_⟩
  intro m
  let Sₘ := D₀ m + CP m + CR m + CA m
  have hSₘ : 0 ≤ Sₘ := by dsimp [Sₘ]; linarith [hD₀ m, hCP m, hCR m, hCA m]
  have hsumCost : Sₘ ≤ (1 + (n : ℝ) ^ 2) * Sₘ := by nlinarith [sq_nonneg (n : ℝ)]
  have hmajor (a : ℝ) (ha : 0 ≤ a) (haSum : a ≤ Sₘ)
      {i : ℕ} (hi : i ≤ m + 9) :
      a * H i ≤ ((1 + (n : ℝ) ^ 2) * Sₘ) * H (m + 9) :=
    (mul_le_mul_of_nonneg_left (hHmono hi) ha).trans
      (mul_le_mul_of_nonneg_right (haSum.trans hsumCost) (by linarith [hH (m + 9)]))
  have hDsum : D₀ m ≤ Sₘ := by dsimp [Sₘ]; linarith [hCP m, hCR m, hCA m]
  have hPsum : CP m ≤ Sₘ := by dsimp [Sₘ]; linarith [hD₀ m, hCR m, hCA m]
  have hRsum : CR m ≤ Sₘ := by dsimp [Sₘ]; linarith [hD₀ m, hCP m, hCA m]
  have hAsum : CA m ≤ Sₘ := by dsimp [Sₘ]; linarith [hD₀ m, hCP m, hCR m]
  refine ⟨(hdatumBound m).trans (hmajor _ (hD₀ m).le hDsum (by omega)),
    (hpotBound m).trans (hmajor _ (hCP m).le hPsum (by omega)),
    (hrowBound m).trans (hmajor _ (hCR m).le hRsum (by omega)), ?_, ?_⟩
  · intro j
    have hm := hmajor _ (hCA m).le hAsum (le_refl (m + 9))
    exact ⟨(hcolumnsBound m j).1.trans hm, (hcolumnsBound m j).2.1.trans hm,
      (hcolumnsBound m j).2.2.trans hm⟩
  · have hm : (n : ℝ) ^ 2 * (CA m * H (m + 9)) ≤
        ((1 + (n : ℝ) ^ 2) * Sₘ) * H (m + 9) := by
      have hcost : (n : ℝ) ^ 2 * CA m ≤ (1 + (n : ℝ) ^ 2) * Sₘ := by
        nlinarith [sq_nonneg (n : ℝ)]
      calc
        _ = ((n : ℝ) ^ 2 * CA m) * H (m + 9) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcost (by linarith [hH (m + 9)])
    have hlead := cNorm_complexColumnMatrix_le_uniform (isCompact_closedBall _ _) isOpen_ball hKU
      (fun j ↦ (hsmooth j).1) m (fun j ↦ (hcolumnsBound m j).1)
    have hcorr := cNorm_complexColumnMatrix_le_uniform (isCompact_closedBall _ _) isOpen_ball hKU
      (fun j ↦ (hsmooth j).2.1) m (fun j ↦ (hcolumnsBound m j).2.1)
    have hres := cNorm_complexColumnMatrix_le_uniform (isCompact_closedBall _ _) isOpen_ball hKU
      (fun j ↦ (hsmooth j).2.2) m (fun j ↦ (hcolumnsBound m j).2.2)
    refine ⟨hlead.trans hm, ?_, ?_⟩
    · change cNorm KA m (fun q ↦ Complex.I •
        complexColumnMatrix (fun j ↦ pencilCorrectionColumn e Q B h Φ C r c mask j q)) ≤ _
      rw [cNorm_I_smul_matrix isOpen_ball hKU
        (contDiffOn_complexColumnMatrix (fun j ↦ (hsmooth j).2.1))]
      exact hcorr.trans hm
    · change cNorm KA m (fun q ↦ Complex.I • complexColumnMatrix
        (fun j ↦ adaptedPencilApply e Q B (pencilCorrectionColumn e Q B h Φ C r c mask j) q)) ≤ _
      rw [cNorm_I_smul_matrix isOpen_ball hKU
        (contDiffOn_complexColumnMatrix (fun j ↦ (hsmooth j).2.2))]
      exact hres.trans hm

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
