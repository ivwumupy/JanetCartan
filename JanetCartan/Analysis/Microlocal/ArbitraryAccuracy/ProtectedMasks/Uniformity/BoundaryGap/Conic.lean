module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap.Collar

/-!
# Boundary collar on the actual normalized conic phase

Positive homogeneity identifies every radial normalization with the same
continued phase. Its full zero-time diagonal is transferred from the actual
local chart on open buffered domains. The compact radial band is used only
to bound the fixed normalization map, never to compactify a coefficient class.
Consumer: the comparable normalized carrier in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase

variable {d : ℕ}

private theorem jointPhase_diagonal_distance_le_of_germ
    (φ : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hg : Function.uncurry φ =ᶠ[𝓝 (p.1.1, p.2.1)]
      (fun q ↦ inner ℝ q.1 q.2)) :
    dist (x, p.2.2.2) (y, p.2.2.1) ≤ 3 * ‖fderiv ℝ (jointPhase backward φ x y) p‖ := by
  have ht : ContinuousAt (fun w : JointVariables (Euclidean (d + 1)) ↦ (w.1.1, w.2.1)) p :=
    by fun_prop
  have he : jointPhase backward φ x y =ᶠ[𝓝 p] jointPhase backward (inner ℝ) x y := by
    filter_upwards [ht.tendsto.eventually hg] with w hw
    cases backward <;> simp only [jointPhase, Bool.false_eq_true, ↓reduceIte,
      forwardPhase, reversePhase, Function.uncurry] at * <;> rw [hw]
  rw [he.fderiv_eq]
  apply jointPhase_diagonal_distance_le
  · exact differentiableAt_fst.inner ℝ differentiableAt_snd
  · have he : (fun v : Euclidean (d + 1) ↦ inner ℝ v p.2.1) = innerSL ℝ p.2.1 := by
      funext v
      exact real_inner_comm _ _
    rw [he]
    exact (innerSL ℝ p.2.1).fderiv
  · exact (innerSL ℝ p.1.1).fderiv

/-- The actual local diagonal continues to a full boundary germ, including
all temporal covectors. The diagonal and radius comparison are literal
outputs of `exists_uniform_fieldRoot_conicGeometry`
(`app:ch_regular:lem:finite-chain`). -/
theorem normalizedConicPhase_boundary_germ
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {β σ : ℝ} (hβσ : β ≤ σ)
    (hdiag : ∀ w ∈ ball z.1 σ ×ˢ ball z.2 σ,
      twoTimePhase C (w.1, w) = inner ℝ w.2.1 w.2.2)
    {u ξ : Euclidean (d + 1)} (hu : u ∈ elapsedPhysicalBox z β)
    (hξ : spatialPart ξ ∈ angularCone ℓ z.2.2 β) {R : ℝ} (hR : 0 < R) :
    Function.uncurry (elapsedPhase (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) 0)
      =ᶠ[𝓝 (u, ξ)] (fun q ↦ inner ℝ q.1 q.2) := by
  rw [show curriedPhase ℓ C = curriedExtend ℓ (twoTimePhase C) from rfl,
    normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) hR]
  have hU : IsOpen (elapsedPhysicalBox z β ×ˢ
      (spatialPart ⁻¹' angularCone ℓ z.2.2 β)) :=
    (isOpen_elapsedPhysicalBox z β).prod
      ((isOpen_angularCone ℓ z.2.2 β).preimage spatialPartCLM.continuous)
  filter_upwards [hU.mem_nhds (show (u, ξ) ∈ _ from ⟨hu, hξ⟩)] with q hq
  change (q.1 0 - 0) * q.2 0 + phase ℓ C
    (q.1 0, (q.1 0 - 0, (spatialPart q.1, spatialPart q.2))) = inner ℝ q.1 q.2
  rw [sub_zero, phase_diagonal_on_buffer ℓ C hβσ hdiag hq.1 hq.2]
  exact (inner_eq_time_add_spatial q.1 q.2).symm

/-- The normalized conic phase has the same coefficient-independent boundary
gap on the full closed shoulder and output complement. The boundary-germ
producer is proved above; no stationary exclusion or derivative gap is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem normalizedConicPhase_boundary_derivative_gap
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {β σ θ : ℝ} (hβσ : β ≤ σ) (hθ : 0 < θ)
    (hdiag : ∀ w ∈ ball z.1 σ ×ˢ ball z.2 σ,
      twoTimePhase C (w.1, w) = inner ℝ w.2.1 w.2.2)
    {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ a ∈ cthickening θ (tsupport mi),
      closedBall a θ ⊆ interior {q | mo q = 1})
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hu : p.1.1 ∈ elapsedPhysicalBox z β)
    (hξ : spatialPart p.2.1 ∈ angularCone ℓ z.2.2 β) {R : ℝ} (hR : 0 < R)
    (hin : (y, p.2.2.1) ∈ cthickening (θ / 2) (tsupport mi))
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    θ / 3 ≤ ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (0, w)) p‖ := by
  have hsep : θ < dist (x, p.2.2.2) (y, p.2.2.1) := by
    by_contra hn
    exact notMem_complement_tsupport_of_mem_plateau
      (hbuffer _ (cthickening_mono (by linarith : θ / 2 ≤ θ) _ hin)
        (mem_closedBall.mpr (not_lt.mp hn))) hout
  have hd := jointPhase_diagonal_distance_le_of_germ _ backward x y p
    (normalizedConicPhase_boundary_germ ℓ C hβσ hdiag hu hξ hR)
  change _ ≤ 3 * ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward
    (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (0, w)) p‖ at hd
  linarith

/-- The fixed variation constant on the constructor's buffered conic jet
set. `N` is its local phase C² budget, obtained from the original C³ input
(`app:ch_regular:eq:chain-tail`). -/
def conicElapsedVariationBound (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) (β a b N : ℝ) : ℝ :=
  (jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z β a b) 2 * N) *
    ‖elapsedJointCoordinates (d := d)‖ * ‖elapsedTangentialCoordinates (d := d)‖ +
      ‖elapsedTemporalCovector (d := d)‖

/-- Conic normalization and the actual local low jet give a uniform
elapsed variation estimate. The domain is the fixed buffered jet set;
only its time/base fiber is used in the mean-value theorem, so no convexity
of a radial annulus is required (`app:ch_regular:lem:finite-chain`). -/
theorem norm_normalizedConicPhase_tangential_variation_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {β a b N : ℝ} (hβ : 0 < β) (ha : 0 < a) (hN : 0 ≤ N)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hbuffer : closedBall (z.1, z) (2 * β) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hjet : cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (ht : p.1.1 0 ∈ closedBall z.1 β) (hy : spatialPart p.1.1 ∈ closedBall z.2.1 β)
    (hη : spatialPart p.2.1 ∈ radialSectionBand ℓ z.2.2 β a b)
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Icc 0 β) :
    ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (r, w)) p -
      fderiv ℝ (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (0, w)) p‖ ≤
      conicElapsedVariationBound ℓ z β a b N * r := by
  let J : Set (SymbolBudgets.TwoTimePoint d) :=
    (closedBall z.1 (2 * β) ×ˢ (closedBall z.1 (2 * β) ×ˢ
      closedBall z.2.1 (2 * β))) ×ˢ {spatialPart p.2.1}
  have hJ : Convex ℝ J :=
    ((convex_closedBall _ _).prod ((convex_closedBall _ _).prod
      (convex_closedBall _ _))).prod (convex_singleton _)
  have hJK : J ⊆ bufferedJetSet ℓ z β a b := by
    intro q hq
    exact ⟨hq.1, (mem_singleton_iff.mp hq.2) ▸ hη⟩
  have hcoords (s : ℝ) (hs : s ∈ Icc 0 β) : elapsedJointCoordinates (s, p) ∈ J := by
    have hsource : dist (p.1.1 0 - s) z.1 ≤ 2 * β := by
      calc
        _ ≤ dist (p.1.1 0 - s) (p.1.1 0) + dist (p.1.1 0) z.1 := dist_triangle _ _ _
        _ = s + dist (p.1.1 0) z.1 := by simp [Real.dist_eq, abs_of_nonneg hs.1]
        _ ≤ 2 * β := by linarith [mem_closedBall.mp ht, hs.2]
    exact ⟨⟨closedBall_subset_closedBall (by linarith) ht,
      mem_closedBall.mpr hsource, closedBall_subset_closedBall (by linarith) hy⟩,
      mem_singleton _⟩
  obtain ⟨hsm, hj⟩ := normalizedConicPhase_secondJet_on_fixed_carrier ℓ z β
    (isCompact_bufferedJetSet ℓ z β a b) (bufferedJetSet_normalizes ℓ hβ.le ha).1
    (bufferedJetSet_normalizes ℓ hβ.le ha).2 C hbuffer hs hjet hR
  have hnonneg : 0 ≤ jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z β a b) 2 * N :=
    mul_nonneg (jetBoundConstant_pos _ _ _).le hN
  have hv := norm_elapsed_tangential_derivative_sub_le_of_secondJet backward
    (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y hJ
    (fun q hq ↦ hsm q (hJK hq)) hnonneg (fun q hq ↦ hj q (hJK hq))
    r p (hcoords r hr) (hcoords 0 ⟨le_rfl, hβ.le⟩)
  change _ ≤ conicElapsedVariationBound ℓ z β a b N * |r| at hv
  simpa only [abs_of_nonneg hr.1] using hv

/-- A common collar for the actual normalized conic carriers, before the
chart, coefficient, masks, orientation or positive normalization radius vary.
The closed base and angular half-buffers give strict neighborhoods for the
boundary germ; the whole radial band, input shoulder and output complement
remain. Restricting this pointwise theorem to the actual closed total carrier
keeps its original elapsed interval (`app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_normalizedConic_boundary_collar
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {β σ θ a b N : ℝ} (hβ : 0 < β) (hβσ : β ≤ σ)
    (hθ : 0 < θ) (ha : 0 < a) (hN : 0 ≤ N) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      closedBall (z.1, z) (2 * β) ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N →
      (∀ w ∈ ball z.1 σ ×ˢ ball z.2 σ,
        twoTimePhase C (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (mi mo : LocalizerSymbol (d + 1)),
      (∀ q ∈ cthickening θ (tsupport mi), closedBall q θ ⊆ interior {q | mo q = 1}) →
      ∀ (backward : Bool) (x y : Euclidean (d + 1))
        (p : JointVariables (Euclidean (d + 1))) (R : ℝ), 0 < R →
      p.1.1 0 ∈ closedBall z.1 (β / 2) →
      spatialPart p.1.1 ∈ closedBall z.2.1 (β / 2) →
      spatialPart p.2.1 ∈ radialSectionBand ℓ z.2.2 (β / 2) a b →
      (y, p.2.2.1) ∈ cthickening (θ / 2) (tsupport mi) →
      (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q) →
      ∀ r : ℝ, 0 ≤ r → r ≤ ε →
      δ ≤ Localization.phaseGradientSquare e (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (r, w)) p := by
  let H := conicElapsedVariationBound ℓ z β a b N
  have hH : 0 ≤ H := by
    have hc := (jetBoundConstant_pos ℓ (budgetCoordinates '' bufferedJetSet ℓ z β a b) 2).le
    dsimp only [H, conicElapsedVariationBound]
    positivity
  let ε := min (β / 2) (θ / (6 * (1 + H)))
  have hε : 0 < ε := lt_min (half_pos hβ) (div_pos hθ (by positivity))
  have hεβ : ε ≤ β := (min_le_left _ _).trans (by linarith)
  have hεH : H * ε ≤ θ / 6 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * (1 + H))).mp (min_le_right
      (β / 2) (θ / (6 * (1 + H))))
    change ε * (6 * (1 + H)) ≤ θ at hh
    nlinarith
  have hepos := jointDirectionLoss_pos e
  refine ⟨ε, hε, (θ / 6 / jointDirectionLoss e) ^ 2, by positivity, ?_⟩
  intro C hbuffer hs hjet hdiag mi mo hmask backward x y p R hR ht hy hη hin hout r hr hrε
  have hηnorm := radialSectionBand_normalizes ha hη
  have hu : p.1.1 ∈ elapsedPhysicalBox z β :=
    ⟨(mem_closedBall.mp ht).trans_lt (half_lt_self hβ),
      (mem_closedBall.mp hy).trans_lt (half_lt_self hβ)⟩
  have hηcone : spatialPart p.2.1 ∈ angularCone ℓ z.2.2 β :=
    ⟨hηnorm.1, (mem_closedBall.mp hηnorm.2).trans_lt (half_lt_self hβ)⟩
  have hη' : spatialPart p.2.1 ∈ radialSectionBand ℓ z.2.2 β a b := by
    obtain ⟨q, ⟨hq, hqball, hqℓ⟩, he⟩ := hη
    exact ⟨q, ⟨hq, closedBall_subset_closedBall (by linarith) hqball, hqℓ⟩, he⟩
  have hgap := normalizedConicPhase_boundary_derivative_gap ℓ C hβσ hθ hdiag hmask
    backward x y p hu hηcone hR hin hout
  have hv := norm_normalizedConicPhase_tangential_variation_le ℓ z hβ ha hN C hbuffer hs hjet
    backward x y p (closedBall_subset_closedBall (by linarith) ht)
      (closedBall_subset_closedBall (by linarith) hy) hη' hR ⟨hr, hrε.trans hεβ⟩
  have hv' := hv.trans ((mul_le_mul_of_nonneg_left hrε hH).trans hεH)
  have hn := norm_sub_norm_le
    (fderiv ℝ (fun w ↦ jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (0, w)) p)
    (fderiv ℝ (fun w ↦ jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C)) x y (r, w)) p)
  rw [norm_sub_rev] at hn
  exact jointDerivative_gap_phaseGradientSquare e _ p (by positivity) (by linarith)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
