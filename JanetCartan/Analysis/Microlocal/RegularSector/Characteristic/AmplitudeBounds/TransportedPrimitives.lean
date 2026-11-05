module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.TransportedPrimitives.CoefficientPair
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilComplement

/-!
# Primitive bounds for the literal transported nullvectors and complement

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:two-term-null-identity`, these estimates concern the
existing `pencilChartRight`, `pencilChartLeft` and `pencilChartComplement`.
The flow substitution is derived from its formula. The original root/minor/
transport gaps produce the rational smoothness neighborhood and all inverse
estimates; neither substituted-state nor amplitude bounds are assumptions.

The fixed reserve is four. Fixed primitive C6 budgets additionally give C2
amplitude bounds and a C1 bound for the differentiated right nullvector, as
needed by the parent's literal `pencilTransportPotential` and its derivatives.
The parent `jc-direct-characteristic-amplitude-budgets` supplies the uniform
primitive family and instantiates the explicit balls and image inclusions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

variable {n d : ℕ}

private theorem exists_minorData_smooth_neighborhood
    (q : TwoTimePoint (Euclidean d)) (ρ : ℝ) (r c : Fin n)
    {V : Set (TwoTimePoint (Euclidean d))} (hV : IsOpen V) (hK : closedBall q ρ ⊆ V)
    {U : TwoTimePoint (Euclidean d) → MetricTensor n × MetricTensor n}
    (hU : ContDiffOn ℝ ∞ U V)
    (hgaps : ∀ y ∈ closedBall q ρ, (U y).1.det = 0 ∧
      (U y).1.adjugate r c ≠ 0 ∧ minorTransportCoefficient (U y).1 (U y).2 r c ≠ 0) :
    ∃ V' : Set (TwoTimePoint (Euclidean d)), IsOpen V' ∧ closedBall q ρ ⊆ V' ∧ V' ⊆ V ∧
      ContDiffOn ℝ ∞ (fun y ↦ minorRightNullvector (U y).1 r c) V' ∧
      ContDiffOn ℝ ∞ (fun y ↦ minorLeftNullvector (U y).1 (U y).2 r c) V' ∧
      ContDiffOn ℝ ∞ (fun y ↦ minorComplementInverse (U y).1 (U y).2 r c 0) V' := by
  let f := fun y ↦ (U y, (0 : ℝ))
  let V' := V ∩ f ⁻¹' minorComplementDomain r c
  have hf : ContDiffOn ℝ ∞ f V := hU.prodMk contDiffOn_const
  have ho : IsOpen V' := hf.continuousOn.isOpen_inter_preimage hV
    (minorComplementDomain_regular r c (m := ∞)).1
  have hball : closedBall q ρ ⊆ V' := by
    intro y hy
    obtain ⟨hr, hm, ht⟩ := hgaps y hy
    obtain ⟨_, hl, hn, hker⟩ := minor_normalization hr hm ht
    exact ⟨hK hy, ⟨hm, ht⟩, pencilCompletion_det_ne_zero hl hn hker⟩
  have hsub : V' ⊆ V := inter_subset_left
  have hnull : MapsTo U V' (minorNullvectorDomain r c) := fun _ hy ↦ hy.2.1
  refine ⟨V', ho, hball, hsub, ?_, ?_, ?_⟩
  · exact (minorNullvectorDomain_regular r c (m := ∞)).2.1.comp (hU.mono hsub) hnull
  · exact (minorNullvectorDomain_regular r c (m := ∞)).2.2.comp (hU.mono hsub) hnull
  · have hc := (minorComplementDomain_regular r c (m := ∞)).2.comp (hf.mono hsub)
      (show MapsTo f V' (minorComplementDomain r c) from fun _ hy ↦ hy.2)
    simpa only [Function.comp_def, f] using hc

/-- Uniform primitive estimates for the actual transported nullvectors and
zero-displacement complement. The single reserve `4` is independent of `m`,
and all constants precede `Q,h,Φ,C`. The last conclusions give uniform C2
norms and a C1 derivative norm directly from fixed primitive C6 budgets.
Only the original root equation and adjugate/transport gaps are required on
the root-state ball; smoothness is proved on an open neighborhood of the
working ball. Matrix norms remain Frobenius norms.

Consumers: the literal `pencilTransportPotential`, leading/correction columns
and physical residual in `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:two-term-null-identity`. -/
theorem exists_pencilChartPrimitives_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (q : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (p : RootState (Euclidean d) × ℝ) {σ : ℝ} (hσ : 0 < σ)
    (z : RootState (Euclidean d)) {τ : ℝ} (hτ : 0 < τ)
    (x : Euclidean n) {R : ℝ} (_hR : 0 < R) {M : ℝ} (hM : 0 ≤ M)
    (r c : Fin n) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
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
          cNorm (closedBall x R) 6 Q ≤ M → cNorm (closedBall z τ) 6 h ≤ M →
          cNorm (closedBall p σ) 6 Φ ≤ M → cNorm (closedBall q ρ) 6 C.symm ≤ M →
          (∀ w ∈ closedBall z τ, (rootPencil e Q h w).det = 0 ∧
            μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) →
          (∃ V' : Set (TwoTimePoint (Euclidean d)), IsOpen V' ∧ closedBall q ρ ⊆ V' ∧ V' ⊆ V ∧
            ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) V' ∧
            ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) V' ∧
            ContDiffOn ℝ ∞ (pencilChartComplement e Q h Φ C r c) V') ∧
          (∀ m,
            let H := 1 + cNorm (closedBall x R) (m + 4) Q + cNorm (closedBall z τ) (m + 4) h +
              cNorm (closedBall p σ) (m + 4) Φ + cNorm (closedBall q ρ) (m + 4) C.symm
            cNorm (closedBall q ρ) m (pencilChartRight e Q h Φ C r c) ≤ A m * H ∧
            cNorm (closedBall q ρ) m (pencilChartLeft e Q h Φ C r c) ≤ A m * H ∧
            cNorm (closedBall q ρ) m (pencilChartComplement e Q h Φ C r c) ≤ A m * H) ∧
          (∀ j ≤ 2,
            cNorm (closedBall q ρ) j (pencilChartRight e Q h Φ C r c) ≤ A j * (1 + 4 * M) ∧
            cNorm (closedBall q ρ) j (pencilChartLeft e Q h Φ C r c) ≤ A j * (1 + 4 * M) ∧
            cNorm (closedBall q ρ) j (pencilChartComplement e Q h Φ C r c) ≤ A j * (1 + 4 * M)) ∧
          cNorm (closedBall q ρ) 1 (fderiv ℝ (pencilChartRight e Q h Φ C r c)) ≤
            A 2 * (1 + 4 * M) := by
  obtain ⟨B, hB, hrootPair⟩ := exists_rootCoefficientPair_cNorm_bounds e z hτ x R M himage
  obtain ⟨A, hA, htransport⟩ :=
    exists_transportedRootCoefficientPair_cNorm_bounds e q hρ p hσ z hτ x R hM himage
  let N := B 0 * (1 + M + M)
  obtain ⟨K, hK, hnull⟩ := exists_minorNullvectors_cNorm_bounds q hρ r c N hμ hν
  obtain ⟨J, hJ, hcomplement⟩ := exists_minorComplement_cNorm_bounds q hρ r c N hμ hν
  let F := fun m ↦ (K m + J m) * (1 + A m)
  have hF m : 0 < F m := mul_pos (add_pos (hK m) (hJ m)) (by linarith [hA m])
  refine ⟨F, hF, ?_⟩
  intro Ω D V W hΩ hD hV hW hKQ hKz hKq hKp hphys Q h Φ C hQ hh hΦ hC
    hflow hflowK hstateD hstateK hQM hhM hΦM hCM hgaps
  have hQ0 : cNorm (closedBall x R) 0 Q ≤ M := (cNorm_mono_order (by omega)).trans hQM
  have hh0 : cNorm (closedBall z τ) 0 h ≤ M := (cNorm_mono_order (by omega)).trans hhM
  obtain ⟨hU, hUb⟩ := htransport Ω D V W hΩ hD hV hW hKQ hKz hKq hKp hphys
    Q h Φ C hQ hh hΦ hC hflow hflowK hstateD hstateK
      ((cNorm_mono_order (by omega)).trans hQM) ((cNorm_mono_order (by omega)).trans hhM)
      ((cNorm_mono_order (by omega)).trans hΦM) ((cNorm_mono_order (by omega)).trans hCM)
  let s := fun y ↦ twoTimeState Φ (C.symm y)
  let u := fun w ↦ (rootPencil e Q h w, rootTimeCoefficient e Q w)
  let U := u ∘ s
  have hu : ContDiffOn ℝ ∞ u D :=
    (contDiffOn_rootPencil e hQ hh hphys).prodMk (contDiffOn_rootTimeCoefficient e hQ hphys)
  have hu0 : cNorm (closedBall z τ) 0 u ≤ N :=
    (hrootPair Ω D hΩ hD hKQ hKz hphys Q h hQ hh hQ0 hh0 0).trans
      (mul_le_mul_of_nonneg_left (by linarith) (hB 0).le)
  have hclass : MapsTo U (closedBall q ρ) (minorCoefficientClass r c N μ ν) := by
    intro y hy
    have hn : ‖U y‖ ≤ N := by
      have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z τ)
        (fun w hw ↦ (hu.contDiffAt (hD.mem_nhds (hKz hw))).of_le
          (show (0 : ℕ∞ω) ≤ ∞ by simp)) (hstateK hy) (le_refl 0)
      have hb' : ‖U y‖ ≤ cNorm (closedBall z τ) 0 u := by
        simpa only [norm_iteratedFDeriv_zero, U, s, Function.comp_def] using hb
      exact hb'.trans hu0
    exact ⟨(norm_fst_le (U y)).trans hn, (norm_snd_le (U y)).trans hn,
      hgaps (s y) (hstateK hy)⟩
  have hsmooth := exists_minorData_smooth_neighborhood q ρ r c hV hKq hU (by
    intro y hy
    have ht := hclass hy
    exact ⟨ht.2.2.1, abs_pos.mp (hμ.trans_le ht.2.2.2.1),
      abs_pos.mp (hν.trans_le ht.2.2.2.2)⟩)
  have hhigh (m : ℕ) :
      let H := 1 + cNorm (closedBall x R) (m + 4) Q + cNorm (closedBall z τ) (m + 4) h +
        cNorm (closedBall p σ) (m + 4) Φ + cNorm (closedBall q ρ) (m + 4) C.symm
      cNorm (closedBall q ρ) m (pencilChartRight e Q h Φ C r c) ≤ F m * H ∧
      cNorm (closedBall q ρ) m (pencilChartLeft e Q h Φ C r c) ≤ F m * H ∧
      cNorm (closedBall q ρ) m (pencilChartComplement e Q h Φ C r c) ≤ F m * H := by
    let H := 1 + cNorm (closedBall x R) (m + 4) Q + cNorm (closedBall z τ) (m + 4) h +
      cNorm (closedBall p σ) (m + 4) Φ + cNorm (closedBall q ρ) (m + 4) C.symm
    have hH : 1 ≤ H := by
      dsimp [H]
      linarith [cNorm_nonneg (closedBall x R) (m + 4) Q, cNorm_nonneg (closedBall z τ) (m + 4) h,
        cNorm_nonneg (closedBall p σ) (m + 4) Φ, cNorm_nonneg (closedBall q ρ) (m + 4) C.symm]
    have hsum : 1 + cNorm (closedBall q ρ) m U ≤ (1 + A m) * H := by
      have hb := hUb m
      change cNorm (closedBall q ρ) m U ≤ A m * H at hb
      nlinarith
    have hmajor (a : ℝ) (ha : 0 ≤ a) (haK : a ≤ K m + J m) :
        a * (1 + cNorm (closedBall q ρ) m U) ≤ F m * H := by
      apply (mul_le_mul_of_nonneg_left hsum ha).trans
      exact (mul_le_mul_of_nonneg_right haK
        (mul_nonneg (by linarith [hA m]) (by linarith))).trans_eq (by dsimp [F]; ring)
    obtain ⟨hk, hl⟩ := hnull V hV hKq U hU hclass m
    have hj := hcomplement V hV hKq U hU hclass m
    exact ⟨hk.trans (hmajor (K m) (hK m).le (by linarith [hJ m])),
      hl.trans (hmajor (K m) (hK m).le (by linarith [hJ m])),
      hj.trans (hmajor (J m) (hJ m).le (by linarith [hK m]))⟩
  have hlow (j : ℕ) (hj : j ≤ 2) :
      cNorm (closedBall q ρ) j (pencilChartRight e Q h Φ C r c) ≤ F j * (1 + 4 * M) ∧
      cNorm (closedBall q ρ) j (pencilChartLeft e Q h Φ C r c) ≤ F j * (1 + 4 * M) ∧
      cNorm (closedBall q ρ) j (pencilChartComplement e Q h Φ C r c) ≤ F j * (1 + 4 * M) := by
    have hb : F j * (1 + cNorm (closedBall x R) (j + 4) Q + cNorm (closedBall z τ) (j + 4) h +
        cNorm (closedBall p σ) (j + 4) Φ + cNorm (closedBall q ρ) (j + 4) C.symm) ≤
        F j * (1 + 4 * M) := by
      apply mul_le_mul_of_nonneg_left _ (hF j).le
      linarith [(cNorm_mono_order (by omega : j + 4 ≤ 6)).trans hQM,
        (cNorm_mono_order (by omega : j + 4 ≤ 6)).trans hhM,
        (cNorm_mono_order (by omega : j + 4 ≤ 6)).trans hΦM,
        (cNorm_mono_order (by omega : j + 4 ≤ 6)).trans hCM]
    exact ⟨(hhigh j).1.trans hb, (hhigh j).2.1.trans hb, (hhigh j).2.2.trans hb⟩
  exact ⟨hsmooth, hhigh, hlow,
    (GeometricProfile.cNorm_fderiv_le (closedBall q ρ) 1 _).trans (hlow 2 le_rfl).1⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
