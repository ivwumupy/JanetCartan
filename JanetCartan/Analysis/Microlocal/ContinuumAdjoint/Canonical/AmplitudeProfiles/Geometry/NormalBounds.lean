module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.Smoothness

/-!
# One-high estimates for the scalar-free canonical normal

This is the principal-normal part of `app:ch_waves:eq:joint-tame`, with the
literal retained nullvector instead of the transported scalar times that
nullvector. The fixed loss is six. No scalar, flow or normal bound is an input.
Consumer: the quadratic geometric component in `Geometry.ComponentBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open LeadingWave AmbientResponse GeometricProfile LeadingWave.JointReconstruction
open ActualCarriers.ConstructedCarrierJets ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual geometric normal has additive single-high bounds with loss six.
The nullvector bounds and pointwise smoothness are projections of the retained
coefficient outputs of `exists_projected_local_positive_amplitude`; the gradient
bound is derived here for the SAME projected stress. The product chart and its
coefficient-ball containment are fixed before the immersion (`joint-tame`). -/
theorem exists_geometricNormal_bounds {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) {ρ σ : ℝ} (hσ : 0 < σ)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (hσX : closedBall (0 : Euclidean n) σ ⊆ X)
    (hσV : closedBall (chartCenter (n := n) z).2 σ ⊆ V)
    (hσK : closedBall (0 : Euclidean n) σ ⊆ K)
    (hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)))
    (hcoef : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 6 F ≤ M →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ col : Fin n,
      (∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
        ContDiffAt ℝ ∞ (carrierNullvector T Q col) w) →
      (∀ j, cNorm (closedBall ((0 : Euclidean n), z) ρ) j (carrierNullvector T Q col) ≤
        A j * (1 + cNorm K (j + 5) F)) →
      ∀ j, cNorm (closedBall (chartCenter z) σ) j
        (fun p : Euclidean n × CarrierParameter ↦ geometricNormal T Q F col (p.2, p.1)) ≤
        B j * (1 + cNorm K (j + 6) F) := by
  let L := closedBall (chartCenter (n := n) z) σ
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  have hL : IsCompact L := isCompact_closedBall ..
  have hLXV : L ⊆ X ×ˢ V := by
    rw [show L = closedBall (chartCenter z) σ from rfl,
      ← closedBall_prod_same (chartCenter (n := n) z).1 (chartCenter (n := n) z).2 σ]
    exact Set.prod_mono hσX hσV
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_fst.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  obtain ⟨E, hE, he⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL (isCompact_closedBall ((0 : Euclidean n), z) ρ)
    (fun _ _ ↦ hψ.contDiffAt) (hcoef.mono_left hLXV)
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL (hL.image hψ.continuous) (fun _ _ ↦ hψ.contDiffAt) (mapsTo_image _ _)
  have hcL : ψ '' L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hc (hLXV hp)
  obtain ⟨G, hG, hg⟩ := T.exists_projected_carrierGradient_sharp_bound (N := N)
    hP (hL.image hψ.continuous) hcL hK hKU hball M hκmet hκ
  let Ab := fun j ↦ E j * A j
  let Ag := fun j ↦ D j * G j
  have hAb j : 0 < Ab j := mul_pos (hE j) (hA j)
  have hAg j : 0 < Ag j := mul_pos (hD j) (hG j)
  obtain ⟨J, hJ, hj⟩ := exists_cNorm_joint_reconstruction_le_of_primitive_bounds
    (N := N) (chartCenter (n := n) z) hσ (show 0 < M + 1 by positivity) hκmet hκ
    ((Ab 1 + Ag 1) * (1 + M))
  let B := fun j ↦ J j * (1 + Ab (j + 1) + Ag j)
  have hB j : 0 < B j := by
    have := hJ j
    have := hAb (j + 1)
    have := hAg j
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal col hnull hnullB
  let b := fun p ↦ carrierNullvector T Q col (ψ p)
  let ξ := fun p : Euclidean n × CarrierParameter ↦
    T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2)
  have hb : ContDiffOn ℝ ∞ b (X ×ˢ V) := by
    change ContDiffOn ℝ ∞ ((carrierNullvector T Q col) ∘ ψ) (X ×ˢ V)
    intro p hp
    exact ((hnull (ψ p) (hcoef hp)).comp p (hψ.contDiffAt)).contDiffWithinAt
  have hξ : ContDiffOn ℝ ∞ ξ (X ×ˢ V) :=
    (T.carrierGradient_smooth hP Q).comp (f := ψ) (s := X ×ˢ V) hψ.contDiffOn hc
  have hbB (j) : cNorm L j b ≤ Ab j * (1 + cNorm K (j + 5) F) :=
    (he _ hnull j).trans ((mul_le_mul_of_nonneg_left (hnullB j) (hE j).le).trans_eq
      (by dsimp [Ab]; ring))
  have hfour : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [← hQ]
    exact Q.2.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = Q := Subtype.ext hQ.symm
  have hgF := hg F hF hi hrank hfour hmet hnormal hlow
  dsimp only at hgF
  rw [hQeq] at hgF
  have hξB (j) : cNorm L j ξ ≤ Ag j * (1 + cNorm K (j + 4) F) := by
    have hs := T.carrierGradient_smooth hP Q
    have ho : IsOpen (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius)) := isOpen_ball.prod (isOpen_parameterInterior _)
    exact (hd _ (fun p hp ↦ hs.contDiffAt (ho.mem_nhds (hcL hp))) j).trans
      ((mul_le_mul_of_nonneg_left (hgF j) (hD j).le).trans_eq (by dsimp [Ag]; ring))
  have hFmono (j) : cNorm (closedBall (0 : Euclidean n) σ) j F ≤ cNorm K j F :=
    cNorm_mono_set_of_contDiffAt hσK hK
      (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hb1 : cNorm L 1 b ≤ (Ab 1 + Ag 1) * (1 + M) := by
    apply (hbB 1).trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hFM) (hAb 1).le
    have hp := mul_nonneg (hAg 1).le (show 0 ≤ 1 + M by positivity)
    nlinarith
  have hξ1 : cNorm L 1 ξ ≤ (Ab 1 + Ag 1) * (1 + M) := by
    apply (hξB 1).trans
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) ((cNorm_mono_order (by omega : 1 + 4 ≤ 6)).trans hFM)) (hAg 1).le
    have hp := mul_nonneg (hAb 1).le (show 0 ≤ 1 + M by positivity)
    nlinarith
  have hrec := hj X V hX hV hσX hσV F b ξ (hF.mono hXU)
    (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx)) hb hξ
    ((hFmono 4).trans (hfour.trans (by linarith)))
    (fun x hx ↦ hmet x (hσK hx)) (fun x hx ↦ hnormal x (hσK hx)) hb1 hξ1
  intro j
  have hn : cNorm L j (fun p : Euclidean n × CarrierParameter ↦
      geometricNormal T Q F col (p.2, p.1)) ≤
      J j * (1 + cNorm (closedBall (0 : Euclidean n) σ) (j + 2) F +
        cNorm L (j + 1) b + cNorm L j ξ) := by
    apply le_trans _ (hrec j)
    exact le_trans (le_add_of_nonneg_right (cNorm_nonneg ..))
      (le_add_of_nonneg_right (cNorm_nonneg ..))
  have hf' : 1 + cNorm (closedBall (0 : Euclidean n) σ) (j + 2) F ≤
      1 + cNorm K (j + 6) F := add_le_add (le_refl 1)
    ((hFmono (j + 2)).trans (cNorm_mono_order (by omega)))
  have hb' : cNorm L (j + 1) b ≤ Ab (j + 1) * (1 + cNorm K (j + 6) F) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hbB (j + 1)
  have hξ' : cNorm L j ξ ≤ Ag j * (1 + cNorm K (j + 6) F) :=
    (hξB j).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (cNorm_mono_order (by omega))) (hAg j).le)
  apply hn.trans
  convert mul_le_mul_of_nonneg_left (add_le_add (add_le_add hf' hb') hξ') (hJ j).le using 1
  dsimp [B]
  ring

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
