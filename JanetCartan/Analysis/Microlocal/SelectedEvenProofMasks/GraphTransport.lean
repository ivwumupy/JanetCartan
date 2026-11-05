module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SymbolReflection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.RootSegments

/-!
# Actual graph transport for the reflected proof relation

Reflect the actual physical whole-segment curve using the dimension-dependent
parity of the SAME normalized pencil. The resulting signed speed has the same
absolute bound. Apply the existing comparison-chart defect estimate without
assuming that the arbitrary finite chart selection is reflection invariant.
Consumer: uniform angular protection for the even proof-mask construction in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic EvolutionIntegratedLocalization
open HamiltonPhase ProtectedFlow PhaseCover ActualCarriers

variable {d : ℕ}

/-- The original relation and its covector reflection share the SAME graph
transport constant. Reflection is applied to the actual physical root curve;
its complete elapsed interval, physical buffer, coefficient field and retained
comparison chart remain fixed. The symmetric frequency carrier is the annulus
constructed by the uniform field-bound producer. No reflected-chart witness
or graph-persistence conclusion is assumed (`app:ch_regular:lem:finite-chain`). -/
theorem reflectedProofRelation_comparison_graph_error_le {J : Type*}
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
    (hPneg : ∀ v ∈ P, -v ∈ P)
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
    (hpq : reflectedProofRelation
      (physicalDirectRelation i h Φ U K W χsource χout Δ) p q) :
    ‖q.2 - scale • C.gradientMap η q.1‖ ≤
      Real.exp (κ⁻¹ * ((1 + β * Lx) * V) * Δ) *
        ‖p.2 - scale • C.gradientMap η p.1‖ := by
  rcases hpq with hpq | hpq
  · exact physicalDirectRelation_comparison_graph_error_le i hQ hκ hLx hV hD hh hroot
      hKD hW hi hode hgap hP C hη hr hscale hscaleβ hderiv hfield hgP hpq
  obtain ⟨j, v, hv, elapsed, he, t₀, ht₀, t₁, ht₁, hcurve, hpeq, hqeq⟩ :=
    physicalDirectRelation_exists_elapsed_curve hi hpq
  have hsub : Icc 0 elapsed ⊆ Icc 0 Δ := Icc_subset_Icc_right he.2
  obtain ⟨_, _, hdom, hphysical⟩ := physicalPencilRootCurve_scaled_ode
    (coordinateSplit (i j)) (coordinateSplit_inverse_pairing (i j)) hQ (hD j) (hh j)
    (hroot j) (fun t ht ↦ hode j v hv t (hsub ht))
    (fun t ht ↦ hKD j (hcurve t ht).1)
  let Z := fun t ↦ physicalPencilRootState (coordinateSplit (i j)) (h j) (Φ j (v, t))
  let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
  let c := fun t ↦ (pencilRootSpeed Q (coordinateSplit (i j)) (h j) (Φ j (v, t)))⁻¹
  let cr := fun t ↦ c t * -((-1 : ℝ) ^ (d + 1))
  have hreflect (t : ℝ) (ht : t ∈ Icc 0 elapsed) :
      HasDerivAt (fun s ↦ (Z s).1) (cr t • H.hp ((Z t).1, -(Z t).2)) t ∧
      HasDerivAt (fun s ↦ -(Z s).2) (cr t • -H.hx ((Z t).1, -(Z t).2)) t ∧
        |cr t| = |c t| := by
    apply normalizedHamilton_reflected_curve hQ (x := fun s ↦ (Z s).1)
      (ξ := fun s ↦ (Z s).2) (c := c) (hdom t ht).2
    · exact (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hphysical t ht)
    · exact (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hphysical t ht)
  have heq := comparisonChart_scaled_graph_error_le C hη hr hLx (inv_nonneg.mpr hκ.le)
    hscale hscaleβ hderiv hfield hgP ht₀ ht₁
    (c := cr) (x := fun t ↦ (Z t).1) (p := fun t ↦ -(Z t).2)
    (fun t ht ↦ (hreflect t ht).2.2 ▸
      inverse_pencilRootSpeed_abs_le hκ (hgap j _ (hcurve t ht).1))
    (fun t ht ↦ (hreflect t ht).1) (fun t ht ↦ (hreflect t ht).2.1)
    (fun t ht ↦ hW (hcurve t ht).2) (fun t ht ↦ hPneg _ (hP j _ (hcurve t ht).1))
  have hp' : p = ((Z t₀).1, -(Z t₀).2) := by
    simpa only [physicalCovectorReflection_apply, neg_neg, Prod.mk.eta] using
      congrArg physicalCovectorReflection hpeq
  have hq' : q = ((Z t₁).1, -(Z t₁).2) := by
    simpa only [physicalCovectorReflection_apply, neg_neg, Prod.mk.eta] using
      congrArg physicalCovectorReflection hqeq
  rw [hp', hq']
  apply heq.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have htime : |t₁ - t₀| ≤ Δ := by
    rw [abs_le]
    constructor <;> linarith [ht₀.1, ht₀.2, ht₁.1, ht₁.2, he.2]
  exact mul_le_mul_of_nonneg_left htime
    (mul_nonneg (inv_nonneg.mpr hκ.le)
      (mul_nonneg (by positivity [hscale.le.trans hscaleβ]) hV))

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
