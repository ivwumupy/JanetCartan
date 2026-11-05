module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NullAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Phase

/-!
# Canonical principal-normal budgets

The literal normal in `app:ch_background:eq:bg-T` is reconstructed from the
SAME null amplitude and Hamilton gradient. The extra derivative in
`app:ch_waves:eq:joint-tame` gives a fixed immersion/initial-data reserve
fourteen. The inputs below are primitive geometry and the retained outputs
of `exists_projected_local_positive_amplitude`, with fixed buffer containments.
Consumer: `CoefficientNormCharts.Controls.normal`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude AmplitudeTame ActualCarriers.ConstructedCarrierJets
open GeometricProfile LeadingWave AmbientResponse LeadingWave.JointReconstruction ProjectedStressFrame

private theorem principalNormal_smooth {n N : ℕ}
    {F : Euclidean n → Euclidean N}
    {b ξ : Euclidean n × CarrierParameter → Euclidean n}
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F X) (hb : ContDiffOn ℝ ∞ b (X ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (X ×ˢ V))
    (hi : IsImmersionOn F X) (hrank : HasFullNormalRankOn F X) :
    ContDiffOn ℝ ∞
      (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p))
      (X ×ˢ V) := by
  have hj := contDiffOn_jointJet hX hV hF hb hξ
  intro p hp
  have hFp : ContDiffAt ℝ 2 F p.1 :=
    (hF.contDiffAt (hX.mem_nhds hp.1)).of_le (by simp)
  have hri : Set.range (secondJetNormalMap (secondJet F p.1)) =
      ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
    rw [secondJetNormalMap_eq_of_contDiffAt hFp (hi _ hp.1)]
    exact hrank _ hp.1
  have hcoef := contDiffAt_principalNormalValue
    (q := jointJet F b ξ p) (hi _ hp.1) hri
  have he := (jointJet_fields_eventuallyEq ξ hX hV hF hb hi hrank hp).1
  exact ((hcoef.comp p (hj.contDiffAt ((hX.prod hV).mem_nhds hp))).congr_of_eventuallyEq
    he.symm).contDiffWithinAt

/-- The actual normal field is smooth and has uniform low and additive
one-high bounds, with fixed loss fourteen. No normal, scalar, null-amplitude
or phase bound is assumed: the scalar estimate is invoked on the retained
producer outputs, and the sharp phase estimate is instantiated with the SAME
projected stress. Fixed primitive C15 bounds and the separate geometric gaps
fix all constants before the immersion, initial data and high norms.
Source: `app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_projected_normalField_bounds {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) {ρ R τ : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A H : ℕ → ℝ) (hA : ∀ j, 0 < A j) (hH : ∀ j, 0 < H j)
    (a : Euclidean n × CarrierParameter) {σ : ℝ} (hσ : 0 < σ)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (haX : closedBall a.1 σ ⊆ X) (haV : closedBall a.2 σ ⊆ V)
    (haK : closedBall a.1 σ ⊆ K)
    (hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (X ×ˢ V) (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius)))
    (hLW : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (closedBall a σ)
      ((coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 64))))
    (hregion : MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2))
      (X ×ˢ V) (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32)))
    {M₁₅ Mᵣ κmet κ : ℝ} (hM₁₅ : 0 ≤ M₁₅) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ M > 0, ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 15 F ≤ M₁₅ →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ (row col : Fin n) (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let p₀ := ((0 : Euclidean (n - 1)), z)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let Bρ := closedBall ((0 : Euclidean n), z) ρ
      let α := carrierScalarAmplitude T Q F row col Φ Y initial
      let b := fun w ↦ α w • carrierNullvector T Q col w
      IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) →
      (∀ j, cNorm Bρ j (carrierNullvector T Q col) +
        cNorm Bρ j (carrierConullvector T Q row) +
        cNorm Bρ j (carrierAdaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (carrierTransportDirection T Q row col) +
        cNorm Bρ j (carrierTransportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) →
      ContDiffOn ℝ ∞ initial (ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ α (C ⁻¹' D) → ContDiffOn ℝ ∞ b (C ⁻¹' D) →
      cNorm (closedBall p₀ (R / 8)) 15 initial ≤ Mᵣ →
      ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial)) (X ×ˢ V) ∧
      cNorm (closedBall a σ) 1 (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤ M ∧
      ∀ j, cNorm (closedBall a σ) j
        (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤
        B j * (1 + cNorm K (j + 14) F +
          cNorm (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (j + 14) initial) := by
  let L := closedBall a σ
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hL : IsCompact L := isCompact_closedBall ..
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hLXV : L ⊆ X ×ˢ V := by
    rw [show L = closedBall a σ from rfl, ← closedBall_prod_same a.1 a.2 σ]
    exact Set.prod_mono haX haV
  have hcL : ψ '' L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hc (hLXV hp)
  obtain ⟨E, hE, he⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL (hL.image hψ.continuous) (fun _ _ ↦ hψ.contDiffAt) (mapsTo_image _ _)
  obtain ⟨G, hG, hg⟩ := T.exists_projected_carrierGradient_sharp_bound (N := N)
    hP (hL.image hψ.continuous) hcL hK hKU hball M₁₅ hκmet hκ
  let G' := fun j ↦ E j * G j
  have hG' (j) : 0 < G' j := mul_pos (hE j) (hG j)
  obtain ⟨Mb, hMb, Bb, hBb, hnb⟩ := exists_canonical_nullAmplitude_bounds T (N := N)
    K z hρ hR hτ hτR hbuffer A H hA hH hL hLW hM₁₅ hMᵣ
  obtain ⟨J, hJ, hj⟩ := exists_cNorm_joint_reconstruction_le_of_primitive_bounds
    (N := N) a hσ (show 0 < M₁₅ + 1 by positivity) hκmet hκ
    (Mb + G' 1 * (1 + M₁₅))
  let B := fun j ↦ J j * (1 + Bb (j + 1) + G' j)
  have hB (j) : 0 < B j := by
    dsimp [B]
    have := hJ j
    have := hBb (j + 1)
    have := hG' j
    positivity
  refine ⟨B 1 * (1 + M₁₅ + Mᵣ), mul_pos (hB 1) (by positivity), B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal row col D Φ Y initial
  dsimp only
  intro hD hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hr hα hbreg hrM
  let α := carrierScalarAmplitude T Q F row col Φ Y initial
  let b := fun p : Euclidean n × CarrierParameter ↦
    α (ψ p) • carrierNullvector T Q col (ψ p)
  let ξ := fun p : Euclidean n × CarrierParameter ↦ T.carrierGradient Q p.1 (parameter p.2)
  have hmaps : MapsTo ψ (X ×ˢ V)
      ((coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D) :=
    fun p hp ↦ hsmall (hregion hp)
  have hb : ContDiffOn ℝ ∞ b (X ×ˢ V) := by
    have hh := hbreg.comp (f := ψ) (s := X ×ˢ V) hψ.contDiffOn hmaps
    exact hh
  have hξ : ContDiffOn ℝ ∞ ξ (X ×ˢ V) := by
    have hh := (T.carrierGradient_smooth hP Q).comp (f := ψ) (s := X ×ˢ V) hψ.contDiffOn hc
    exact hh
  have hFi : ContDiffOn ℝ ∞ F X := hF.mono hXU
  have hii : IsImmersionOn F X := fun x hx ↦ hi x (hXU hx)
  have hri : HasFullNormalRankOn F X := fun x hx ↦ hrank x (hXU hx)
  have hfour : cNorm K 4 F ≤ M₁₅ := (cNorm_mono_order (by omega)).trans hFM
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [← hQ]
    exact Q.2.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = Q :=
    Subtype.ext hQ.symm
  have hgF := hg F hF hi hrank hfour hmet hnormal hlow
  dsimp only at hgF
  rw [hQeq] at hgF
  have hξbound (j) : cNorm L j ξ ≤ G' j * (1 + cNorm K (j + 4) F) := by
    have hs := T.carrierGradient_smooth hP Q
    have ho : IsOpen (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius)) := isOpen_ball.prod (isOpen_parameterInterior _)
    exact (he _ (fun p hp ↦ hs.contDiffAt (ho.mem_nhds (hcL hp))) j).trans
      ((mul_le_mul_of_nonneg_left (hgF j) (hE j).le).trans_eq (by dsimp [G']; ring))
  obtain ⟨hblow, hbhigh⟩ := hnb Q F row col D Φ Y initial hD hsmall hbig hΦD hYU
    hΦ hY hreg hcoeff hflow hr hα hbreg hFM hrM
  have hb1 : cNorm L 1 b ≤ Mb := le_trans (le_add_of_nonneg_left (cNorm_nonneg ..)) hblow
  have hξ1 : cNorm L 1 ξ ≤ G' 1 * (1 + M₁₅) := (hξbound 1).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) ((cNorm_mono_order (by omega : 1 + 4 ≤ 15)).trans hFM))
      (hG' 1).le)
  have hFmono (j) : cNorm (closedBall a.1 σ) j F ≤ cNorm K j F :=
    cNorm_mono_set_of_contDiffAt haK hK
      (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hrec := hj X V hX hV haX haV F b ξ hFi hii hri hb hξ
    ((hFmono 4).trans (hfour.trans (by linarith)))
    (fun x hx ↦ hmet x (haK hx)) (fun x hx ↦ hnormal x (haK hx))
    (hb1.trans (le_add_of_nonneg_right (mul_nonneg (hG' 1).le (by positivity)))) (hξ1.trans (by linarith))
  have hhigh (j) : cNorm L j (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤
      B j * (1 + cNorm K (j + 14) F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (j + 14) initial) := by
    let W := 1 + cNorm K (j + 14) F +
      cNorm (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (j + 14) initial
    have hn : cNorm L j (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤
        J j * (1 + cNorm (closedBall a.1 σ) (j + 2) F +
          cNorm L (j + 1) b + cNorm L j ξ) := by
      apply le_trans _ (hrec j)
      exact le_trans (le_add_of_nonneg_right (cNorm_nonneg ..))
        (le_add_of_nonneg_right (cNorm_nonneg ..))
    have hf : 1 + cNorm (closedBall a.1 σ) (j + 2) F ≤ W := by
      have := (hFmono (j + 2)).trans (cNorm_mono_order (by omega : j + 2 ≤ j + 14))
      have := cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (j + 14) initial
      dsimp [W]
      linarith
    have hb' : cNorm L (j + 1) b ≤ Bb (j + 1) * W := by
      have hh := (le_add_of_nonneg_left
        (cNorm_nonneg L (j + 1) (fun p ↦ α (ψ p)))).trans (hbhigh (j + 1))
      simpa only [Nat.add_assoc, Nat.reduceAdd] using hh
    have hξ' : cNorm L j ξ ≤ G' j * W :=
      (hξbound j).trans (mul_le_mul_of_nonneg_left (by
        have := cNorm_mono_order (s := K) (f := F) (by omega : j + 4 ≤ j + 14)
        have := cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (j + 14) initial
        dsimp [W]
        linarith) (hG' j).le)
    apply hn.trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hf hb') hξ') (hJ j).le
    dsimp [B]
    convert hh using 1
    ring
  refine ⟨principalNormal_smooth hX hV hFi hb hξ hii hri, ?_, hhigh⟩
  apply (hhigh 1).trans
  apply mul_le_mul_of_nonneg_left _ (hB 1).le
  exact add_le_add (add_le_add (le_refl 1) hFM) hrM

end JanetCartan.ContinuumRow.CanonicalCarrier
