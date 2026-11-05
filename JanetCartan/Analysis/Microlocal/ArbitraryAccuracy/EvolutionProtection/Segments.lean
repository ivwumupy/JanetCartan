module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Field
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Propagation

/-!
# Entire direct root segments in the retained comparison family

Consumer: direct complete-chain propagation for `app:ch_regular:lem:finite-chain`.
The only root inputs are the open smooth root domain, literal determinant equation,
nonzero transverse covector and determinant derivative supplied by
`RegularSector.Characteristic.exists_pencilRoot_domain`, and the adapted-coordinate
pairing to be instantiated by the sector owner. The comparison charts are those
for the same `normalizedHomogeneousSymbol` retained by
`ProtectedFlow.exists_initialized_signed_no_return`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover

variable {n d : ℕ}

/-- A complete segment of the actual root ODE, lifted at zero energy, with
both endpoint times arbitrary and every intermediate point in the root and
physical domains (`app:ch_regular:thm:no-return`). -/
def CompletePencilRootSegment (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (D : Set (RootState (Euclidean d)))
    (W : Set (Euclidean n)) (z w : Euclidean n × Euclidean n) : Prop :=
  ∃ (Z : ℝ → RootState (Euclidean d)) (a b t₀ t₁ : ℝ),
    t₀ ∈ Icc a b ∧ t₁ ∈ Icc a b ∧
    (∀ t ∈ Icc a b, HasDerivAt Z (rootHamiltonField h (Z t)) t) ∧
    (∀ t ∈ Icc a b, Z t ∈ D) ∧
    (∀ t ∈ Icc a b, (physicalPencilRootState e h (Z t)).1 ∈ W) ∧
    z = physicalPencilRootState e h (Z t₀) ∧ w = physicalPencilRootState e h (Z t₁)

/-- The nonzero spatial covector retained by the root constructor implies a
nonzero full physical covector (`app:ch_regular:lem:finite-chain`). -/
theorem physicalPencilRootState_covector_ne_zero
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) {w : RootState (Euclidean d)} (hw : w.2.2 ≠ 0) :
    (physicalPencilRootState e h w).2 ≠ 0 := by
  intro he
  change e.symm (h w, w.2.2) = 0 at he
  have hz : (h w, w.2.2) = 0 := e.symm.injective (he.trans (map_zero e.symm).symm)
  exact hw (congrArg Prod.snd hz)

/-- A direct root segment lies on the characteristic set of the SAME pencil.
This excludes nontrivial elliptic branches without assuming energy conservation
or protection (`app:ch_regular:thm:no-return`). -/
theorem completePencilRootSegment_source_energy
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Q : Euclidean n → Fin n → MetricTensor n}
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hroot : ∀ v ∈ D,
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0)
    {W : Set (Euclidean n)} {z w : Euclidean n × Euclidean n}
    (hseg : CompletePencilRootSegment e h D W z w) : normalizedSymbol Q z = 0 := by
  obtain ⟨Z, a, b, t₀, t₁, ht₀, _, _, hZD, _, rfl, _⟩ := hseg
  simp [physicalPencilRootState, normalizedSymbol, hroot _ (hZD t₀ ht₀)]

/-- A whole root segment has nonzero output covector by the retained root
domain, including its endpoints (`app:ch_regular:lem:finite-chain`). -/
theorem completePencilRootSegment_target_ne_zero
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hne : ∀ v ∈ D, v.2.2 ≠ 0)
    {W : Set (Euclidean n)} {z w : Euclidean n × Euclidean n}
    (hseg : CompletePencilRootSegment e h D W z w) : w.2 ≠ 0 := by
  obtain ⟨Z, a, b, t₀, t₁, _, ht₁, _, hZD, _, _, rfl⟩ := hseg
  exact physicalPencilRootState_covector_ne_zero e h (hne _ (hZD t₁ ht₁))

/-- An entire root curve is a solution of the actual pencil field with
continuous, nonzero signed speed. The scalar relation is proved from the root
equation, and no root-flow invariance is assumed
(`app:ch_regular:thm:no-return`). -/
theorem physicalPencilRootCurve_scaled_ode
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ u v : ℝ × Euclidean d,
      ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ v ∈ D, v.2.2 ≠ 0 ∧
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1))))
        (e.symm (h v, v.2.2)) (e.symm (1, 0)) ≠ 0)
    {Z : ℝ → RootState (Euclidean d)} {a b : ℝ}
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (rootHamiltonField h (Z t)) t)
    (hZD : ∀ t ∈ Icc a b, Z t ∈ D) :
    let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
    let c := fun t ↦ (pencilRootSpeed Q e h (Z t))⁻¹
    ContinuousOn c (Icc a b) ∧
      (∀ t ∈ Icc a b, c t ≠ 0) ∧
      (∀ t ∈ Icc a b, physicalPencilRootState e h (Z t) ∈ H.domain) ∧
      (∀ t ∈ Icc a b, HasDerivAt (fun u ↦ physicalPencilRootState e h (Z u))
        (c t • H.vectorField (physicalPencilRootState e h (Z t))) t) := by
  let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
  let P := fun t ↦ physicalPencilRootState e h (Z t)
  have hhd t ht : DifferentiableAt ℝ h (Z t) :=
    (hh.contDiffAt (hD.mem_nhds (hZD t ht))).differentiableAt (by simp)
  have hn t ht : (P t).2 ≠ 0 :=
    physicalPencilRootState_covector_ne_zero e h (hroot _ (hZD t ht)).1
  have hneigh t ht : ∀ᶠ v in 𝓝 (Z t),
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0 :=
    eventually_of_mem (hD.mem_nhds (hZD t ht)) (fun v hv ↦ (hroot v hv).2.1)
  have hspeed t ht : pencilRootSpeed Q e h (Z t) ≠ 0 :=
    pencilRootSpeed_ne_zero Q e h _ (hn t ht) (hroot _ (hZD t ht)).2.2
  have hpd t ht : HasDerivAt P (physicalPencilRootVelocity e h (Z t)) t :=
    hasDerivAt_physicalPencilRootState e (hhd t ht) (hZ t ht)
  have hpc : ContinuousOn P (Icc a b) := fun t ht ↦ (hpd t ht).continuousAt.continuousWithinAt
  have hdom : MapsTo P (Icc a b) H.domain := fun t ht ↦ ⟨mem_univ _, hn t ht⟩
  have hvc : ContinuousOn (fun t ↦ H.vectorField (P t)) (Icc a b) :=
    (contDiffOn_normalizedHomogeneousSymbol_vectorField isOpen_univ Q hQ.contDiffOn).continuousOn.comp hpc hdom
  have hsc : ContinuousOn (fun t ↦ pencilRootSpeed Q e h (Z t)) (Icc a b) := by
    apply (e.continuous.comp_continuousOn hvc.fst).fst.congr
    intro t ht
    exact pencilRootSpeed_eq_time_component e hpair isOpen_univ hQ.contDiffOn
      (hhd t ht) (mem_univ _) (hn t ht) (hneigh t ht)
  refine ⟨hsc.inv₀ hspeed, fun t ht ↦ inv_ne_zero (hspeed t ht), hdom, ?_⟩
  intro t ht
  have he := normalizedPencil_field_eq_root_velocity e hpair isOpen_univ hQ.contDiffOn
    (hhd t ht) (mem_univ _) (hn t ht) (hneigh t ht)
  rw [he, smul_smul, inv_mul_cancel₀ (hspeed t ht), one_smul]
  exact hpd t ht

/-- The direct root segment preserves the SAME conic comparison family retained
by initialized protection. The proof uses the derived signed scalar speed and
ODE uniqueness on the whole segment (`app:ch_regular:thm:no-return`). -/
theorem comparisonFamily_preserves_pencilRootSegment {I : Type*}
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ u v : ℝ × Euclidean d,
      ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ v ∈ D, v.2.2 ≠ 0 ∧
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1))))
        (e.symm (h v, v.2.2)) (e.symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g i))
    {r : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    {z w : Euclidean n × Euclidean n}
    (hz : z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hseg : CompletePencilRootSegment e h D (ball 0 (2 * r)) z w) :
    w ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ := by
  obtain ⟨_, η, _, scale, hscale, hz⟩ := hz
  obtain ⟨Z, a, b, t₀, t₁, ht₀, ht₁, hZ, hZD, hZW, rfl, rfl⟩ := hseg
  obtain ⟨hc, _, hdom, hode⟩ := physicalPencilRootCurve_scaled_ode e hpair hQ hD hh hroot hZ hZD
  have he := comparisonChart_preserves_scaled_segment rfl
    (contDiffOn_normalizedSymbol isOpen_univ hQ.contDiffOn) (C η.1) η.2.2 ht₀ hscale hc
    (fun t ht ↦ (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hode t ht))
    (fun t ht ↦ (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivAt t (hode t ht))
    (fun t ht ↦ ball_subset_ball (hradius η.1).le (hZW t ht)) hdom hz t₁ ht₁
  exact ⟨hZW t₁ ht₁, η, mem_univ _, scale, hscale, he⟩

end JanetCartan.ArbitraryAccuracy
