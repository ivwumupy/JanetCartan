module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.RootSegments
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.FieldBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations.Bounds

/-!
# Uniform graph transport from primitive root buffers

The quantitative segment estimate of `app:ch_regular:lem:finite-chain`.
The fixed section, transverse ball and root-value bounds determine a common
annulus for every intermediate root state. Together with the retained graph's
radial bounds this closes the field estimate on a fixed annulus. The literal
`IsSmoothFlowOn` supplies the original elapsed ODE, including both orientations.

The comparison bounds are produced by `InitializedProtection` on the same
charts as all its no-return conclusions. `Construction` assembles that producer
with this deduction; this leaf alone does not assert existence of those charts.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic EvolutionIntegratedLocalization
open HamiltonPhase ProtectedFlow PhaseCover ActualCarriers
open JanetCartan.FiniteChain.Graph.PhysicalShells

variable {d : ℕ}

/-- Choose the comparison transport loss before the coefficient field from
primitive root-section constants, its C³ budget, and uniform comparison jets.
The latter are the outputs of `exists_initialized_signed_no_return_with_graph_bounds`.
All root hypotheses are literal restrictions of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry` and its retained
`IsSmoothFlowOn` witness. No error smallness or persistence premise is needed
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_physicalDirectRelation_comparison_transport
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {r M c C Lx κ Δ α β : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) (_hC : 0 < C) (hLx : 0 ≤ Lx)
    (hκ : 0 < κ) (hΔ : 0 ≤ Δ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ L ≥ (1 : ℝ),
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 r) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 r →
        (∀ j v, v ∈ K j →
          v.2.2 ∈ closedBall (η₀ j) (ε j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
      ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
      ∀ (g : ComparisonGeometry (Euclidean (d + 1)))
        (chart : ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) g),
        r ≤ 2 * g.radius →
        (∀ η ∈ g.parameters, ∀ x ∈ closedBall 0 r,
          ‖fderiv ℝ (chart.gradientMap η) x‖ ≤ Lx) →
        (∀ η ∈ g.parameters, ∀ x ∈ closedBall 0 r,
          c ≤ ‖chart.gradientMap η x‖ ∧ ‖chart.gradientMap η x‖ ≤ C) →
      ∀ η ∈ g.parameters,
        (∀ x ∈ closedBall 0 r, ∀ y ∈ closedBall 0 r,
          ‖chart.gradientMap η x - chart.gradientMap η y‖ ≤ Lx * dist x y) ∧
        ∀ scale ∈ Icc α β, ∀ p q,
          physicalDirectRelation i h Φ U K W χsource χout Δ p q →
          ‖q.2 - scale • chart.gradientMap η q.1‖ ≤
            L * ‖p.2 - scale • chart.gradientMap η p.1‖ := by
  classical
  let := Fintype.ofFinite J
  let lower : Option J → ℝ := fun j ↦ j.elim 1 (fun j ↦ 1 / (2 * (‖ℓ j‖ + 1)))
  let upper : Option J → ℝ := fun j ↦ j.elim 1
    (fun j ↦ (‖ℓ j‖ * (‖η₀ j‖ + ε j)) * G j + (‖η₀ j‖ + ε j))
  let a₀ := Finset.univ.inf' Finset.univ_nonempty lower
  let b₀ := Finset.univ.sup' Finset.univ_nonempty upper
  have ha₀ : 0 < a₀ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j _
    cases j <;> dsimp [lower] <;> positivity
  let a := min a₀ (α * c)
  let b := max a (max b₀ (β * C))
  have ha : 0 < a := lt_min ha₀ (mul_pos hα hc)
  obtain ⟨V, hV, hfield⟩ :=
    exists_uniform_normalizedHomogeneousSymbol_vectorField_covector_lipschitz
      r hr M hM ha (le_max_left a (max b₀ (β * C)))
  let L := Real.exp (κ⁻¹ * ((1 + β * Lx) * V) * Δ)
  have hβ : 0 ≤ β := hα.le.trans hαβ
  refine ⟨L, Real.one_le_exp (by positivity), ?_⟩
  intro Q hQ hQM i h Φ U K D W χsource χout hD hh hroot hKD hW hsection hgap
    z Rflow rFlow T hflow htime hU g chart hgr hderiv hnorm η hη
  refine ⟨fun x hx y hy ↦ comparisonChart_gradient_dist_le_of_derivative_bound
    chart hη hgr (hderiv η hη) hx hy, ?_⟩
  intro scale hscale p q hpq
  have hs : 0 < scale := hα.trans_le hscale.1
  have hrootann (j : J) (v : RootState (Euclidean d)) (hv : v ∈ K j) :
      (physicalPencilRootState (coordinateSplit (i j)) (h j) v).2 ∈ frequencyAnnulus a b := by
    obtain ⟨hball, hsec, hval⟩ := hsection j v hv
    obtain ⟨_, hlo, hup, hval'⟩ :=
      rootBuffer_bounds_of_section_and_ball (ℓ j) (η₀ j) (hG j) hball hsec hval
    obtain ⟨hl, hu⟩ := physicalPencilRootState_covector_bounds (i j) (h j) v hlo hup hval'
    have hlow : a₀ ≤ 1 / (2 * (‖ℓ j‖ + 1)) :=
      Finset.inf'_le lower (Finset.mem_univ (some j))
    have hhigh : (‖ℓ j‖ * (‖η₀ j‖ + ε j)) * G j + (‖η₀ j‖ + ε j) ≤ b₀ :=
      Finset.le_sup' upper (Finset.mem_univ (some j))
    exact ⟨((min_le_left _ _).trans hlow).trans hl,
      (hu.trans hhigh).trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  have hgraphann (x) (hx : x ∈ closedBall (0 : Euclidean (d + 1)) r) :
      scale • chart.gradientMap η x ∈ frequencyAnnulus a b := by
    rw [frequencyAnnulus, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    obtain ⟨hl, hu⟩ := hnorm η hη x hx
    exact ⟨(min_le_right _ _).trans (mul_le_mul hscale.1 hl hc.le hs.le),
      (mul_le_mul hscale.2 hu (norm_nonneg _) hβ).trans
        ((le_max_right _ _).trans (le_max_right _ _))⟩
  have hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v :=
    fun j v hv ↦ (hflow j).initial v (hU j hv)
  have hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t := by
    intro j v hv t ht
    exact (hflow j).hasDerivAt (hU j hv)
      ⟨by linarith [ht.1, htime j], ht.2.trans_lt (htime j)⟩
  exact physicalDirectRelation_comparison_graph_error_le i hQ hκ hLx hV
    hD hh hroot hKD hW hi hode hgap hrootann chart hη hgr hs hscale.2
    (hderiv η hη) (hfield Q hQ hQM) hgraphann hpq

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
