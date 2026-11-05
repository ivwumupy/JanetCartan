module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap.ConicTransfer
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension.Elapsed
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.CompactJets

/-!
# The constructed conic extension preserves both localization gaps

The extension in `exists_uniform_fieldRoot_conicGeometry` agrees with the
conic phase on the full radially invariant domain of its closed buffer.
Thus its germ at every positive frequency dilation follows from the SAME
normalized domain restriction. Both the full and tangential gradient
squares are unchanged. Consumer: the supported smooth phase used in
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase JanetCartan.Localization

variable {d : ℕ}

/-- Every point of the closed boundary half-buffers stays in the actual
extension's conic domain throughout the common collar. The whole radial band
is retained; only its normalized representative is put in the local ball.
Consumer: the supported boundary gap in `app:ch_regular:eq:chain-tail`. -/
theorem elapsedChartPoint_mem_conic_boundary_buffer
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {γ a b r : ℝ} (hγ : 0 < γ) (ha : 0 < a)
    (p : JointVariables (Euclidean (d + 1))) (hr : r ∈ Icc 0 γ)
    (ht : p.1.1 0 ∈ closedBall z.1 (γ / 2))
    (hy : spatialPart p.1.1 ∈ closedBall z.2.1 (γ / 2))
    (hη : spatialPart p.2.1 ∈ radialSectionBand ℓ z.2.2 (γ / 2) a b) :
    elapsedChartPoint r p.1.1 p.2.1 ∈ domain ℓ (closedBall (z.1, z) (2 * γ)) := by
  obtain ⟨hpos, hnorm⟩ := radialSectionBand_normalizes ha hη
  have hsource : dist (p.1.1 0 - r) z.1 ≤ 2 * γ := by
    calc
      _ ≤ dist (p.1.1 0 - r) (p.1.1 0) + dist (p.1.1 0) z.1 := dist_triangle _ _ _
      _ = r + dist (p.1.1 0) z.1 := by simp [Real.dist_eq, abs_of_nonneg hr.1]
      _ ≤ 2 * γ := by linarith [mem_closedBall.mp ht, hr.2]
  refine ⟨hpos, ?_⟩
  change (p.1.1 0, (p.1.1 0 - r,
    (spatialPart p.1.1, (ℓ (spatialPart p.2.1))⁻¹ • spatialPart p.2.1))) ∈
      closedBall (z.1, z) (2 * γ)
  have hsize : γ / 2 ≤ 2 * γ := by linarith
  simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
    And.intro (closedBall_subset_closedBall hsize ht)
      (And.intro (mem_closedBall.mpr hsource)
        (And.intro (closedBall_subset_closedBall hsize hy)
          (closedBall_subset_closedBall hsize hnorm)))

/-- Pull back the actual extension's germ through positive frequency
normalization and the full elapsed substitution. There is no local-chart
overlap assumption: the radial domain is preserved by positive scaling
(`app:ch_regular:lem:finite-chain`). -/
theorem jointElapsedPhase_normalized_extension_eventuallyEq
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (hG : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    {Rf : ℝ} (hRf : 0 < Rf) (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hp : elapsedChartPoint p.1 p.2.1.1 p.2.2.1 ∈ domain ℓ K) :
    jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase Rf (fun t s v η ↦ G (t, (s, (v, η))))) x y
        =ᶠ[𝓝 p] jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase ℓ C)) x y := by
  let q := ((elapsedJointCoordinates p).1, Rf • (elapsedJointCoordinates p).2)
  have hq : budgetCoordinates q ∈ domain ℓ K := mem_domain_smul ℓ hp hRf
  have he : SymbolBudgets.jointPhase (fun t s v η ↦ G (t, (s, (v, η)))) =ᶠ[𝓝 q]
      SymbolBudgets.jointPhase (curriedPhase ℓ C) :=
    (hG _ hq).comp_tendsto (budgetCoordinates.continuous.tendsto q)
  exact jointElapsedPhase_eventuallyEq_of_twoTimePhase backward
    (SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase ℓ C))
    (SymbolBudgets.normalizedTwoTimePhase Rf (fun t s v η ↦ G (t, (s, (v, η))))) x y p
    (normalizedTwoTimePhase_eventuallyEq_of_germ Rf (curriedPhase ℓ C)
      (fun t s v η ↦ G (t, (s, (v, η)))) (elapsedJointCoordinates p) he)

/-- The actual constructed supported extension has exactly the same full
and tangential squared gradients at every normalized supported point. Its
producer supplies `hG` on `domain ℓ (closedBall (z.1,z) (2*γ))`; the actual
factor support supplies `hp`. Both orientations and every positive frequency
scale are retained (`app:ch_regular:eq:chain-tail`). -/
theorem phaseGradientSquare_normalized_extension_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : ι → JointVariables (Euclidean (d + 1)))
    (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {G : TwoTimePoint (Euclidean d) → ℝ} {K : Set (TwoTimePoint (Euclidean d))}
    (hG : ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C)
    {Rf : ℝ} (hRf : 0 < Rf) (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hp : elapsedChartPoint p.1 p.2.1.1 p.2.2.1 ∈ domain ℓ K) :
    let Ψ := SymbolBudgets.normalizedTwoTimePhase Rf (fun t s v η ↦ G (t, (s, (v, η))))
    let Ψ₀ := SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase ℓ C)
    phaseGradientSquare eI (jointElapsedPhase backward Ψ x y) p =
      phaseGradientSquare eI (jointElapsedPhase backward Ψ₀ x y) p ∧
    phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward Ψ x y (p.1, w)) p.2 =
      phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward Ψ₀ x y (p.1, w)) p.2 := by
  have he := jointElapsedPhase_normalized_extension_eventuallyEq ℓ C hG hRf backward x y p hp
  have ht := he.comp_tendsto
    ((continuous_const.prodMk continuous_id).tendsto p.2)
  dsimp only [Function.comp_def, id_eq] at ht
  constructor
  · simp only [phaseGradientSquare, he.fderiv_eq]
  · simp only [phaseGradientSquare, ht.fderiv_eq]

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
