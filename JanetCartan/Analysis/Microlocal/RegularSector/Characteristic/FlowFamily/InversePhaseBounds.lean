module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.ProjectionJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.ShearBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.InverseJetBounds

/-!
# Uniform bounds for the same inverse chart and two-time phase

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`, transfer the single-high forward
projection bounds to an actual common inverse chart and its literal phase.
The complete positive constant sequence precedes the root, flow, and chart.
The scalar-root derivative reserve is one at every order.

The flow is supplied by `FlowFamily.Flow`; the common chart construction must
supply the source, target, smooth inverse, and normalized half-gap. This module
proves the quantitative implication, not the existence of those charts. Its
consumer is the common two-time construction in `FlowFamily`, followed by
`AmplitudeBounds` and `EvolutionIntegral.SymbolBudgets`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

section Normalization

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Transfer back from the normalized target in
`exists_rootFlow_twoTime_inverse_phase_cNorm_bound`
(`app:ch_regular_base:lem:characteristic-kernel`). This is the existing local
linear jet bound summed over the orders. -/
private theorem cNorm_prelinear_le_of_bound
    (L : X →L[ℝ] X) {N : ℝ} (hN : 1 ≤ N) (hL : ‖L‖ ≤ N)
    {K J V : Set X} (hJ : IsCompact J) (hV : IsOpen V) (hJV : J ⊆ V)
    {g : X → X} (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo L K J) (n : ℕ) :
    cNorm K n (g ∘ L) ≤ ((n + 1 : ℝ) * N ^ n) * cNorm J n g := by
  have hb : ∀ j ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (g ∘ L) x‖ ≤ N ^ n * cNorm J n g := by
    intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
      L hV hg (hJV (hmap hx)) j).trans
    have hp : ‖L‖ ^ j ≤ N ^ n :=
      (pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hN hj)
    exact (mul_le_mul
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
        (fun y hy ↦ (hg.contDiffAt (hV.mem_nhds (hJV hy))).of_le (by simp))
        (hmap hx) hj) hp (by positivity) (cNorm_nonneg _ _ _)).trans_eq (mul_comm _ _)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, ← mul_assoc] using
    cNorm_le_sum_of_bounds
      (fun _ _ ↦ mul_nonneg (pow_nonneg (by linarith) _) (cNorm_nonneg J n g)) hb

variable [FiniteDimensional ℝ X]

/-- The normalization adapter used by the two-time inverse estimate. Apply
`HamiltonPhase.exists_inverse_cNorm_bound` with the identity equivalence to
`A.symm ∘ f` and `g ∘ A`. Thus the constant precedes the varying shear `A`.
The transformed compact target is allowed to vary with that shear. The consumer
is `exists_rootFlow_twoTime_inverse_phase_cNorm_bound`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
private theorem exists_inverse_cNorm_bound_of_uniform_shear
    (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 1 ≤ N) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (A : X ≃L[ℝ] X) (f g : X → X) (V K : Set X),
      ‖A.symm.toContinuousLinearMap‖ ≤ N → IsOpen V → IsCompact K → K ⊆ V →
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M → MapsTo g K (closedBall a ρ) →
      (∀ x ∈ closedBall a ρ,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ f x) -
          ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) →
      EqOn (f ∘ g) id V →
      cNorm K n g ≤ B * (1 + cNorm (closedBall a ρ) n f) := by
  have hN₀ : 0 ≤ N := le_trans zero_le_one hN
  obtain ⟨B, hB, hb⟩ := HamiltonPhase.exists_inverse_cNorm_bound a hρ hW hball
    (ContinuousLinearEquiv.refl ℝ X) (mul_nonneg hN₀ hM) n
  let Q : ℝ := (n + 1 : ℝ) * N ^ n
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q * B * (1 + N), by positivity, ?_⟩
  intro A f g V K hA hV hK hKV hf hg hlow hrange hgap heq
  let L := A.symm.toContinuousLinearMap
  let F : X → X := L ∘ f
  let G : X → X := g ∘ A
  let V' : Set X := A ⁻¹' V
  let K' : Set X := A.symm '' K
  have hV' : IsOpen V' := hV.preimage A.continuous
  have hK' : IsCompact K' := hK.image A.symm.continuous
  have hK'V' : K' ⊆ V' := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [V'] using hKV hy
  have hF : ContDiffOn ℝ ∞ F W := hf.continuousLinearMap_comp L
  have hG : ContDiffOn ℝ ∞ G V' := hg.comp A.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hFnorm (j : ℕ) : cNorm (closedBall a ρ) j F ≤
      N * cNorm (closedBall a ρ) j f := by
    exact (FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on
      (isCompact_closedBall a ρ) j L
      (fun x hx ↦ (hf.contDiffAt (hW.mem_nhds (hball hx))).of_le (by simp))).trans
      (mul_le_mul_of_nonneg_right hA (cNorm_nonneg _ _ _))
  have hi := hb F G V' K' hV' hK'V' hF hG
    ((hFnorm 1).trans (mul_le_mul_of_nonneg_left hlow hN₀)) (by
      rintro _ ⟨y, hy, rfl⟩
      simpa [G] using hrange hy) (by
      intro x hx
      have hd := (L.hasFDerivAt.comp x
        ((hf.contDiffAt (hW.mem_nhds (hball hx))).differentiableAt (by simp)).hasFDerivAt).fderiv
      change ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2
      rw [show fderiv ℝ F x = L.comp (fderiv ℝ f x) from hd]
      exact hgap x hx) (by
      intro x hx
      change A.symm (f (g (A x))) = x
      have he : f (g (A x)) = A x := heq hx
      rw [he]
      exact A.symm_apply_apply x)
  have ht : cNorm K n g ≤ Q * cNorm K' n G := by
    have he : G ∘ L = g := by funext x; simp [G, L]
    rw [← he]
    exact cNorm_prelinear_le_of_bound L hN hA hK' hV' hK'V' hG
      (fun x hx ↦ ⟨x, hx, rfl⟩) n
  calc
    _ ≤ Q * (B * (1 + cNorm (closedBall a ρ) n F)) :=
      ht.trans (mul_le_mul_of_nonneg_left hi hQ.le)
    _ ≤ Q * (B * ((1 + N) * (1 + cNorm (closedBall a ρ) n f))) := by
      apply mul_le_mul_of_nonneg_left _ hQ.le
      apply mul_le_mul_of_nonneg_left _ hB.le
      have hn := hFnorm n
      have hp := cNorm_nonneg (closedBall a ρ) n f
      nlinarith
    _ = _ := by ring

end Normalization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance twoTimeInversePhaseNormedSpace : NormedSpace ℝ E :=
  InnerProductSpace.toNormedSpace

/-- The literal phase is linear in the inverse coordinates at every norm
order: its other factor is the fixed initial-covector projection. This is
the phase transfer for `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_twoTimePhase_cNorm_bound
    {K : Set (TwoTimePoint E)} (hK : IsCompact K) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E),
      K ⊆ C.target → ContDiffOn ℝ ∞ C.symm C.target →
      cNorm K n (twoTimePhase C) ≤ B * cNorm K n C.symm := by
  let P : TwoTimePoint E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp
    ((ContinuousLinearMap.snd ℝ ℝ (E × E)).comp (ContinuousLinearMap.snd ℝ ℝ (RootState E)))
  let η : TwoTimePoint E → E := fun q ↦ q.2.2.2
  let b : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let S := ∑ j ∈ Finset.range (n + 1), ‖b‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  let B := S * ‖P‖ * cNorm K n η
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg b)
    (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hS (norm_nonneg _)) (cNorm_nonneg _ _ _)
  refine ⟨1 + B, by positivity, ?_⟩
  intro C hKC hC
  have hp := FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on hK n P
    (fun x hx ↦ (hC.contDiffAt (C.open_target.mem_nhds (hKC hx))).of_le (by simp))
  have hb := FullPhaseCharts.InverseEstimates.cNorm_bilinear_le_on b hK C.open_target hKC
    (hC.continuousLinearMap_comp P) (contDiffOn_snd.snd.snd : ContDiffOn ℝ ∞ η C.target) n
  change cNorm K n (twoTimePhase C) ≤ S * cNorm K n (P ∘ C.symm) * cNorm K n η at hb
  calc
    _ ≤ S * (‖P‖ * cNorm K n C.symm) * cNorm K n η :=
      hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hS)
        (cNorm_nonneg _ _ _))
    _ = B * cNorm K n C.symm := by dsimp [B]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

variable [FiniteDimensional ℝ E]

/-- Uniform single-high bounds for the same inverse chart and the literal
`twoTimePhase`, with scalar-root reserve one. Every constant is chosen before
the root, the actual flow, and the chart. The common chart producer retains
the geometric hypotheses; no inverse-jet bound is an input
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_rootFlow_twoTime_inverse_phase_cNorm_bound
    (z : RootState E) {R T ρ σ M : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hρ : 0 < ρ) (hσ : 0 < σ) (hM : 0 ≤ M)
    (hρR : 2 * ρ ≤ R / 4) (hρT : 2 * ρ ≤ T / 4)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ (h : RootState E → ℝ) (Φ : RootState E × ℝ → RootState E)
        (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)),
        ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
        (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ →
        C.source = ball (z.1, z) ρ → ContDiffOn ℝ ∞ C.symm C.target →
        closedBall (z.1, z) σ ⊆ C.target →
        (∀ x ∈ closedBall (z.1, z) ρ,
          ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
            (fderiv ℝ (twoTimeProjection Φ) x) -
              ContinuousLinearMap.id ℝ (TwoTimePoint E)‖ ≤ 1 / 2) →
        ∀ n, cNorm (closedBall (z.1, z) σ) n C.symm +
          cNorm (closedBall (z.1, z) σ) n (twoTimePhase C) ≤
            B n * (1 + cNorm (closedBall z R) (n + 1) h) := by
  choose A hA hforward using fun n ↦
    exists_rootFlow_twoTime_cNorm_bound z hR hT hM hρR hρT hD hRD n
  let L := A 1 * (1 + M)
  have hL : 0 ≤ L := mul_nonneg (hA 1).le (by linarith)
  have hN : 1 ≤ 1 + 2 * M := by linarith
  choose I hI hinverse using fun n ↦ exists_inverse_cNorm_bound_of_uniform_shear
    (z.1, z) hρ (isOpen_twoTimeDomain z (R / 2) T)
    (closedBall_subset_twoTimeDomain z hR hT hρR hρT) hL hN n
  choose P hP hphase using fun n ↦
    exists_twoTimePhase_cNorm_bound (isCompact_closedBall (z.1, z) σ) n
  refine ⟨fun n ↦ (1 + σ + P n) * I n * (1 + A n),
    (fun n ↦ by have := hP n; have := hI n; have := hA n; positivity), ?_⟩
  intro h Φ C hh hlow hΦ hC hsource hCsmooth htarget hgap n
  have hproj (j : ℕ) : cNorm (closedBall (z.1, z) ρ) j (twoTimeProjection Φ) ≤
      A j * (1 + cNorm (closedBall z R) (j + 1) h) := by
    have hb := hforward j h Φ hh hlow hΦ
    linarith [cNorm_nonneg (closedBall (z.1, z) ρ) j (twoTimeState Φ)]
  have hprojlow : cNorm (closedBall (z.1, z) ρ) 1 (twoTimeProjection Φ) ≤ L :=
    (hproj 1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) ((cNorm_mono_order (f := h) (s := closedBall z R)
        (show 2 ≤ 3 by omega)).trans hlow)) (hA 1).le)
  have hi := hinverse n (twoTimeProjectionEquiv (-rootMomentumGradient h z))
    (twoTimeProjection Φ) C.symm C.target (closedBall (z.1, z) σ)
    (rootProjectionShear_bounds_of_cNorm_three hD hR.le hRD hh hlow).2
    C.open_target (isCompact_closedBall _ _) htarget (rootFlow_twoTimeProjection_smooth hΦ)
    hCsmooth hprojlow (by
      intro x hx
      have hm := C.map_target (htarget hx)
      rw [hsource] at hm
      exact ball_subset_closedBall hm) hgap (by
      intro x hx
      simpa only [Function.comp_apply, id_eq, ← hC] using C.right_inv hx)
  have hp := hphase n C htarget hCsmooth
  have hfactor : 0 ≤ 1 + σ + P n := by have := hP n; positivity
  have hs : cNorm (closedBall (z.1, z) σ) n C.symm +
      cNorm (closedBall (z.1, z) σ) n (twoTimePhase C) ≤
        (1 + σ + P n) * cNorm (closedBall (z.1, z) σ) n C.symm := by
    nlinarith [cNorm_nonneg (closedBall (z.1, z) σ) n C.symm]
  calc
    _ ≤ (1 + σ + P n) * (I n * (1 + cNorm (closedBall (z.1, z) ρ) n
        (twoTimeProjection Φ))) := hs.trans (mul_le_mul_of_nonneg_left hi hfactor)
    _ ≤ (1 + σ + P n) * (I n * ((1 + A n) *
        (1 + cNorm (closedBall z R) (n + 1) h))) := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      apply mul_le_mul_of_nonneg_left _ (hI n).le
      have hb := hproj n
      have hn := cNorm_nonneg (closedBall z R) (n + 1) h
      nlinarith [hA n]
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic
