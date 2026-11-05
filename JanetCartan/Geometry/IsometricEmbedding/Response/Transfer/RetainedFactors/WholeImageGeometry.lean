module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.RadialComparison
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientJets

/-!
# Whole-image inverse jets of the retained elapsed phase

Construct the actual averaged-gradient inverse on its entire image from the
original retained half-gap and finite coefficient norm. The source annulus,
inverse constants and derivative reserve precede coefficients and histories.
The single smooth representative uses these same inverse coordinates and
Jacobians by equality on the full physical box and collared cone.
Consumer: the whole-image primitive inputs in both integrated-envelope
endpoints (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison LowBounds
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The existing direct-envelope reserve already pays the fixed original
coefficient order needed for the whole-image inverse; this adds no new
Sobolev-order-dependent loss (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_wholeImage_history_reserve {Rstar rStar : ℕ}
    (hRstar : FullLowBounds.fullLowReserve (d + 1) + 2 < Rstar)
    (hreserve : Rstar + 5 ≤ rStar) :
    wholeImagePhaseReserve (d + 1) + 3 ≤ rStar := by
  rw [FullLowBounds.fullLowReserve_eq] at hRstar
  simp only [wholeImagePhaseReserve, primitiveNormalReserve]
  omega

/-- All whole-image geometric inputs for the actual smooth elapsed phase.
The only coefficient norm is the fixed order `wholeImagePhaseReserve (d+1)+1`;
the actual history producer supplies it before selecting any output order.
Every shell of the full image is retained, including its low-frequency
shoulder, with both physical positions (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_retained_representative_wholeImage_geometry
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b aperture : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε < b) (hAp : 0 ≤ aperture)
    (phaseCost : ℕ → ℝ) (hcost : ∀ j, 0 < phaseCost j) (M : ℝ) :
    ∃ gap > (0 : ℝ), ∃ a > (0 : ℝ), ∃ bfreq > a,
    ∃ Mgraph > (0 : ℝ), ∃ Ggraph > (0 : ℝ),
    ∃ cgraph : ℝ, 1 ≤ cgraph ∧ ∃ growth > (0 : ℝ),
    ∀ (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1)),
      cNorm KQ (wholeImagePhaseReserve (d + 1) + 1) Q ≤ M →
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ C.target,
        HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
        phaseCost j * (1 + cNorm KQ (j + 1) Q)) →
    ∀ (src δ : ℝ), src ≤ ε → ∀ hδ : 0 < δ, δ ≤ 1 / 2 →
    ∀ χ : TC → ℝ,
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ t ∈ Icc (0 : ℝ) (3 * src / 4),
      let X := elapsedPhysicalBox z (ε / 2)
      let D := retainedFrequencyDomain ℓ z ε aperture (1 / 2)
      let S := elapsedPhase (curriedPhase ℓ C) t
      let S' := elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t
      let η := wholeImageInverse S D
      let J := averagedJacobian S
      let W := X ×ˢ (X ×ˢ D)
      AveragedGradientChart S' X D η J gap ∧
      IsOpen (bufferedNormalDomain X D S') ∧
      ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D S') ∧
      MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S') W ∧
      ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W ∧
      (∀ q ∈ W, gap ≤ |(J q.1 q.2.1 q.2.2).det|) ∧
      (∀ q ∈ bufferedNormalDomain X D S',
        normalForwardCoordinates S' (normalInverseCoordinates η q) = q) ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ ξ ∈ D,
        ‖averagedGradient S' x y ξ‖ ≤ growth * (1 + ‖ξ‖)) ∧
      (∀ K : Set (NormalVariables (d + 1)), IsClosed K → K ⊆ W →
        IsClosed (normalForwardCoordinates S' '' K) ∧
          normalForwardCoordinates S' '' K ⊆ bufferedNormalDomain X D S') ∧
      ∀ l : ℕ,
        let V := X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^l) a bfreq)
        let U := normalDyadicShell (bufferedNormalDomain X D S') l
        IsOpen U ∧ IsOpen V ∧
        ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) U ∧
        MapsTo (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) U V ∧
        ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦
          normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) V ∧
        (∀ q ∈ V, gap ≤ |(normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2).det|) ∧
        (∀ q ∈ V, ∀ j ≤ primitiveNormalReserve (d + 1),
          ‖iteratedFDeriv ℝ j (fun q : NormalVariables (d + 1) ↦
            normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) q‖ ≤ Mgraph) ∧
        (∀ q ∈ U, ∀ j, 1 ≤ j → j ≤ primitiveNormalReserve (d + 1) →
          ‖iteratedFDeriv ℝ j
            (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η)) q‖ ≤ Ggraph) ∧
        ∀ q ∈ V, (2 : ℝ)^l ≤ cgraph * (1 + ‖(2 : ℝ)^l • q.2.2‖) := by
  obtain ⟨gap, hgap, _, _, m, hm, _, Mfreq, hMfreq, hgeometry⟩ :=
    exists_retained_elapsed_frequency_comparison (aperture := aperture) ℓ z hε hεb.le phaseCost hcost M
  have hMf : 0 < Mfreq := zero_lt_one.trans_le hMfreq
  obtain ⟨a, ha, bfreq, hab, hrange⟩ := exists_normalizedWholeImageInverse_shell_range
    (n := d + 1) (by norm_num : (0 : ℝ) < 1 / 2) hMf (inv_pos.mpr hm)
  let N := wholeImagePhaseReserve (d + 1)
  obtain ⟨A, hA, B, hB, hphaseJets⟩ := exists_normalizedShell_jet_bound ℓ hε.le hAp ha
    (b := bfreq) (isOpen_ball (x := (z.1, z))) (closedBall_subset_ball hεb) N
  let Bφ := B + A * (phaseCost N * (1 + |M|))
  obtain ⟨Mgraph, hMg, Ggraph, hGg, hjets⟩ :=
    exists_normalizedWholeImage_jet_bounds (n := d + 1) (primitiveNormalReserve (d + 1)) Bφ bfreq hgap
  refine ⟨gap, hgap, a, ha, bfreq, hab, Mgraph, hMg, Ggraph, hGg,
    max 1 a⁻¹, le_max_left _ _, Mfreq, hMf, ?_⟩
  intro KQ Q hQ h Φ C hbuffer hs hdiff hnear hphase src δ hsrc hδ hδhalf χ hχ t ht X D S S' η J W
  have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, by linarith only [ht.2, hsrc, hε]⟩
  have hQ3 : cNorm KQ 3 Q ≤ M :=
    (cNorm_mono_order (by simp only [wholeImagePhaseReserve, primitiveNormalReserve]; omega)).trans hQ
  obtain ⟨hS, _, hgeom, hcomp, _⟩ := hgeometry KQ Q hQ3 h Φ C hbuffer hs hdiff hnear hphase t htε
  have hX : IsOpen X := isOpen_elapsedPhysicalBox _ _
  have hcX : Convex ℝ X := convex_elapsedPhysicalBox _ _
  have hD : IsOpen D := isOpen_retainedFrequencyDomain _ _ _ _ _
  have hinj := fun x hx y hy ↦ (hgeom x hx y hy).1
  have hgap' := fun x hx y hy ξ hξ ↦ (hgeom x hx y hy).2 ξ hξ
  have hreverse : ∀ x ∈ X, ∀ y ∈ X, ∀ ξ ∈ D,
      ‖ξ‖ ≤ m⁻¹ * ‖averagedGradient S x y ξ‖ := by
    intro x hx y hy ξ hξ
    rw [le_inv_mul_iff₀ hm]
    exact (hcomp x hx y hy ξ hξ).1
  have hmap := hrange S X D (fun ξ hξ ↦ retainedFrequencyDomain_norm_lt ℓ hξ)
    (fun x hx y hy ξ hξ ↦ ⟨(hcomp x hx y hy ξ hξ).2, hreverse x hx y hy ξ hξ⟩)
  have hbudget : ∀ l : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^l) a bfreq,
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (Function.uncurry (normalizedPhase ((2 : ℝ)^l) S)) p‖ ≤ Bφ := by
    intro l p hp j hj
    have hsball := hs.mono (ball_subset_closedBall.trans hbuffer)
    have hh := hphaseJets (twoTimePhase C) hsball ((2 : ℝ)^l) (by positivity) t htε p
      ⟨⟨ball_subset_ball (by linarith) hp.1.1, ball_subset_ball (by linarith) hp.1.2⟩,
        retainedFrequencyDomain_subset_fullAngularCone ℓ hε hAp hp.2.1, hp.2.2⟩ j hj
    apply hh.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply le_trans (cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hεb.le)
      (isCompact_closedBall _ _) (fun p hp ↦
        (hs.contDiffAt (C.open_target.mem_nhds (hbuffer hp))).of_le (by simp)))
    exact (hphase N).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hQ.trans (le_abs_self M))) (hcost N).le)
  have hj := hjets S X D hX hD hcX hS hinj hgap' a ha hab hbudget hmap
  have he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D) :=
    capped_elapsed_representative_eqOn ℓ z hε hsrc C hδ hδhalf hχ ht
  have hdom : bufferedNormalDomain X D S' = bufferedNormalDomain X D S :=
    bufferedNormalDomain_phase_congr hX hcX he
  have hchart : AveragedGradientChart S X D η J gap :=
    averagedGradientChart hX hD hcX hS hinj hgap hgap'
  have hopen : IsOpen (bufferedNormalDomain X D S) :=
    isOpen_bufferedNormalDomain hX hD hcX hS hinj hgap hgap'
  have hforward : EqOn (normalForwardCoordinates S') (normalForwardCoordinates S) W :=
    normalForwardCoordinates_phase_congr hX hcX he
  refine ⟨hchart.congr_phase hX hcX he, hdom.symm ▸ hopen,
    hdom.symm ▸ wholeImageInverse_contDiffOn hX hD hcX hS hinj hgap hgap',
    hdom.symm ▸ mapsTo_wholeImageInverse,
    averagedJacobian_contDiffOn hX hD hcX hS,
    fun q hq ↦ hgap' _ hq.1 _ hq.2.1 _ hq.2.2, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ bufferedNormalDomain X D S := hdom ▸ hq
    rw [hforward (mapsTo_wholeImageInverse hq')]
    exact normalForward_wholeImageInverse hq'
  · intro x hx y hy ξ hξ
    rw [averagedGradient_phase_congr hX hcX he hx hy hξ]
    exact (hcomp x hx y hy ξ hξ).2.trans
      (mul_le_mul_of_nonneg_left (by linarith) hMf.le)
  · intro K hK hKW
    have him : normalForwardCoordinates S' '' K = normalForwardCoordinates S '' K :=
      Set.image_congr (fun _ hq ↦ hforward (hKW hq))
    rw [him, hdom]
    exact ⟨isClosed_normalForward_image_of_frequency_bound hX hD hcX hS hK hKW
      (inv_pos.mpr hm).le hreverse, normalForward_image_subset_bufferedNormalDomain hKW⟩
  · intro l V U
    have hU : U = normalDyadicShell (bufferedNormalDomain X D S) l := by dsimp only [U]; rw [hdom]
    refine ⟨hU.symm ▸ isOpen_normalDyadicShell hopen l,
      hX.prod (hX.prod (isOpen_normalizedSourceBand hD _ _ _)),
      hU.symm ▸ normalizedWholeImageInverse_contDiffOn_shell hX hD hcX hS hinj hgap hgap' l,
      hU.symm ▸ hmap l, normalizedAveragedJacobian_contDiffOn_band hX hD hcX hS _ a bfreq,
      fun q hq ↦ hgap' _ hq.1 _ hq.2.1 _ hq.2.2.1,
      (hj l).1, hU.symm ▸ (hj l).2, ?_⟩
    intro q hq
    have hR : 0 < (2 : ℝ)^l := by positivity
    have hlow : (2 : ℝ)^l ≤ a⁻¹ * ‖(2 : ℝ)^l • q.2.2‖ := by
      rw [le_inv_mul_iff₀ ha, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith only [hq.2.2.2.1, hR]
    exact hlow.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans (le_max_left _ _))))

end JanetCartan.ResponseTransfer.RetainedFactors
