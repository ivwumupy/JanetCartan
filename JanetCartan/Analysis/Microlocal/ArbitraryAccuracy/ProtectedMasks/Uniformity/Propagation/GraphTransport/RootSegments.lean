module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.Defect

/-!
# Comparison error along actual supported root segments

These deductions retain both orientations, the physical masks, the original
elapsed bound, and every intermediate point of `physicalDirectRelation`.
They are the quantitative segment step for `app:ch_regular:lem:finite-chain`.

`physicalDirectRelation_comparison_graph_error_le` discharges the ODE and
signed-speed obligations from the actual root relation. Its uniform field
and comparison-gradient bounds are explicit remaining producer obligations;
this module does not assert their unconditional existence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic EvolutionIntegratedLocalization
open HamiltonPhase ProtectedFlow PhaseCover ActualCarriers

variable {d : ℕ}

/-- Recover the original forward elapsed curve from either orientation of the
actual relation. The endpoint parameters lie in the SAME original interval;
the full root and physical buffers are retained. No time reparametrization
is performed (`app:ch_regular:lem:finite-chain`).
Consumer: `physicalDirectRelation_comparison_graph_error_le`. -/
theorem physicalDirectRelation_exists_elapsed_curve {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
    ∃ j, ∃ v ∈ U j, ∃ elapsed ∈ Icc 0 Δ,
      ∃ t₀ ∈ Icc 0 elapsed, ∃ t₁ ∈ Icc 0 elapsed,
        (∀ t ∈ Icc 0 elapsed, Φ j (v, t) ∈ K j ∧
          (physicalPencilRootState (coordinateSplit (i j)) (h j) (Φ j (v, t))).1 ∈ W) ∧
        p = physicalPencilRootState (coordinateSplit (i j)) (h j) (Φ j (v, t₀)) ∧
        q = physicalPencilRootState (coordinateSplit (i j)) (h j) (Φ j (v, t₁)) := by
  obtain ⟨j, backward, a, b, hab, rfl, rfl⟩ := hpq
  obtain ⟨elapsed, he, hc, _, _, hrel⟩ := hab
  have hzero : (0 : ℝ) ∈ Icc 0 elapsed := ⟨le_rfl, he.1⟩
  have hend : elapsed ∈ Icc 0 elapsed := ⟨he.1, le_rfl⟩
  cases backward
  · refine ⟨j, spacetimeRootState a, hc.1, elapsed, he, 0, hzero, elapsed, hend,
      hc.2, ?_, ?_⟩
    · rw [hi j (spacetimeRootState a) hc.1]
      exact adaptedPhysicalPhaseState_eq_root_of_zero_energy _ _ _ hrel.1
    · rw [hrel.2, adaptedPhysicalPhaseState_rootSuspensionState]
  · refine ⟨j, spacetimeRootState b, hc.1, elapsed, he, elapsed, hend, 0, hzero,
      hc.2, ?_, ?_⟩
    · rw [hrel.2, adaptedPhysicalPhaseState_rootSuspensionState]
    · rw [hi j (spacetimeRootState b) hc.1]
      exact adaptedPhysicalPhaseState_eq_root_of_zero_energy _ _ _ hrel.1

/-- The primitive transverse gap bounds the signed physical speed in the
original root time. The input is the normalized determinant gap exported by
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`
(`app:ch_regular:thm:no-return`). -/
theorem inverse_pencilRootSpeed_abs_le
    {n : ℕ} {Q : Euclidean n → Fin n → MetricTensor n}
    {e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ} {v : RootState (Euclidean d)}
    {κ : ℝ} (hκ : 0 < κ) (hgap : κ ≤ |pencilRootSpeed Q e h v|) :
    |(pencilRootSpeed Q e h v)⁻¹| ≤ κ⁻¹ := by
  rw [abs_inv]
  exact inv_anti₀ hκ hgap

/-- Quantitative graph-error transport along the ACTUAL masked relation,
with both orientations and its original elapsed interval. The analytic
inputs are the physical Hamilton-field Lipschitz bound and the derivative
bound for the SAME comparison chart. Root smoothness, the literal determinant
equation, buffers and normalized transverse gap come from
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`; the initial/ODE
fields come from its `IsSmoothFlowOn` witness. The remaining field and chart
bounds must still be instantiated before this becomes a uniform construction.
Consumer: finite-depth buffered propagation in `app:ch_regular:lem:finite-chain`. -/
theorem physicalDirectRelation_comparison_graph_error_le {J : Type*}
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q)
    {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K D : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ r κ Lx V β scale : ℝ}
    (hκ : 0 < κ) (hLx : 0 ≤ Lx) (hV : 0 ≤ V)
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
        ((coordinateSplit (i j)).symm (h j v, v.2.2))
        ((coordinateSplit (i j)).symm (1, 0)) ≠ 0)
    (hKD : ∀ j, K j ⊆ D j) (hW : W ⊆ closedBall 0 r)
    (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hgap : ∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|)
    {P : Set (Euclidean (d + 1))}
    (hP : ∀ j v, v ∈ K j →
      (physicalPencilRootState (coordinateSplit (i j)) (h j) v).2 ∈ P)
    {g : ComparisonGeometry (Euclidean (d + 1))}
    (C : ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) g)
    {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters)
    (hr : r ≤ 2 * g.radius) (hscale : 0 < scale) (hscaleβ : scale ≤ β)
    (hderiv : ∀ y ∈ closedBall (0 : Euclidean (d + 1)) r,
      ‖fderiv ℝ (C.gradientMap η) y‖ ≤ Lx)
    (hfield : ∀ y ∈ closedBall (0 : Euclidean (d + 1)) r, ∀ v ∈ P, ∀ w ∈ P,
      ‖(normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).vectorField (y, v) -
        (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).vectorField (y, w)‖ ≤
          V * ‖v - w‖)
    (hgP : ∀ y ∈ closedBall (0 : Euclidean (d + 1)) r, scale • C.gradientMap η y ∈ P)
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
    ‖q.2 - scale • C.gradientMap η q.1‖ ≤
      Real.exp (κ⁻¹ * ((1 + β * Lx) * V) * Δ) *
        ‖p.2 - scale • C.gradientMap η p.1‖ := by
  obtain ⟨j, v, hv, elapsed, he, t₀, ht₀, t₁, ht₁, hcurve, rfl, rfl⟩ :=
    physicalDirectRelation_exists_elapsed_curve hi hpq
  have hsub : Icc 0 elapsed ⊆ Icc 0 Δ := Icc_subset_Icc_right he.2
  obtain ⟨_, _, _, hphysical⟩ := physicalPencilRootCurve_scaled_ode
    (coordinateSplit (i j)) (coordinateSplit_inverse_pairing (i j)) hQ (hD j) (hh j)
    (hroot j) (fun t ht ↦ hode j v hv t (hsub ht))
    (fun t ht ↦ hKD j (hcurve t ht).1)
  have heq := comparisonChart_scaled_graph_error_le C hη hr hLx (inv_nonneg.mpr hκ.le)
    hscale hscaleβ hderiv hfield hgP ht₀ ht₁
    (fun t ht ↦ inverse_pencilRootSpeed_abs_le hκ (hgap j _ (hcurve t ht).1))
    (fun t ht ↦ (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hphysical t ht))
    (fun t ht ↦ (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hphysical t ht))
    (fun t ht ↦ hW (hcurve t ht).2) (fun t ht ↦ hP j _ (hcurve t ht).1)
  apply heq.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have htime : |t₁ - t₀| ≤ Δ := by
    rw [abs_le]
    constructor <;> linarith [ht₀.1, ht₀.2, ht₁.1, ht₁.2, he.2]
  exact mul_le_mul_of_nonneg_left htime
    (mul_nonneg (inv_nonneg.mpr hκ.le)
      (mul_nonneg (by positivity [hscale.le.trans hscaleβ]) hV))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
