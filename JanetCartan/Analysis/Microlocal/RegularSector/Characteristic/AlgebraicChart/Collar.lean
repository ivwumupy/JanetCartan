module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.Buffers

/-!
# A same-root spectral collar of the original frozen covector

Continuity of the retained coefficient root at its actual frozen value gives
one smaller coefficient radius and an open positively conic neighborhood.
Its normalized displacement fits any prescribed positive inverse interval.
No coefficient field, multiplier or accuracy is chosen in this construction.
Consumer: finite spectral selection and `NormalizedSpectralSupport` in
`app:ch_regular_base:eq:complement-inverse` and `complement-symbol`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicChart
open ActualCarriers RootFamily FiniteMasks.ActualFamily ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification EvolutionIntegral.SymbolBudgets AlgebraicSymbols
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

/-- The normalization used by the complement inverse is invariant under
positive dilation (`app:ch_regular_base:eq:complement-inverse`). -/
theorem normalizeCovector_pos_smul (ℓ : Euclidean d →L[ℝ] ℝ)
    (ζ : E) {t : ℝ} (ht : 0 < t) :
    normalizeCovector ℓ (t • ζ) = normalizeCovector ℓ ζ := by
  simp only [normalizeCovector, spatialPart_smul, map_smul, smul_eq_mul,
    mul_inv_rev, smul_smul]
  congr 1
  field_simp [ht.ne']

/-- A cone about the ORIGINAL physical covector with exact same-root
normalized displacement, compact normalized spatial containment and bounded
normalized full covectors. The input root data are the actual output of
`exists_localChart_with_algebraic_data`. The chosen interval is arbitrary here
so the final construction can use the interval of its retained inverse-budget
producer (`app:ch_regular_base:eq:complement-inverse`). -/
theorem exists_normalized_spectral_collar (c : LocalChart Ω x RQ A₀ ξ M)
    (hc : RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
      c.minorGap c.transportGap)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ c.coefficientRadius ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      (∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V) ∧
    ∃ Λ > (0 : ℝ), ∀ ζ ∈ V,
      let ζ' := (physicalCoordinates c.index).symm ζ
      0 < c.radialSection (spatialPart ζ') ∧
      spatialPart (normalizeCovector c.radialSection ζ') ∈
        closedBall (coordinateSplit c.index ξ).2 b ∧
      ‖normalizeCovector c.radialSection ζ'‖ ≤ Λ ∧
      ∀ A ∈ closedBall A₀ a',
        |normalizeCovector c.radialSection ζ' 0 -
          c.root (A, spatialPart (normalizeCovector c.radialSection ζ'))| ≤ ε := by
  let ξ' := (physicalCoordinates c.index).symm ξ
  have hsplit : coordinateSplit 0 ξ' = coordinateSplit c.index ξ := by
    change coordinateSplit 0 ((coordinateSplit 0).symm (coordinateSplit c.index ξ)) = _
    exact (coordinateSplit 0).apply_symm_apply _
  have htime : ξ' 0 = (coordinateSplit c.index ξ).1 := congrArg Prod.fst hsplit
  have hspace : spatialPart ξ' = (coordinateSplit c.index ξ).2 := congrArg Prod.snd hsplit
  have hsection : c.radialSection (spatialPart ξ') = 1 := hspace ▸ c.section_eq_one
  have hnormalize : normalizeCovector c.radialSection ξ' = ξ' := by
    simp only [normalizeCovector, hsection, inv_one, one_smul]
  have hH : ContDiffAt ℝ ∞ c.root (A₀, spatialPart ξ') := by
    rw [hspace]
    exact (hc.2 _ ⟨mem_closedBall_self c.coefficientRadius_pos.le,
      mem_closedBall_self (le_min c.coefficientRadius_pos.le c.rootRadius_pos.le)⟩).1
  let f : Coeff × E → ℝ := fun p ↦ p.2 0 - c.root (p.1, spatialPart p.2)
  have hparam : ContinuousAt (fun p : Coeff × E ↦ (p.1, spatialPart p.2)) (A₀, ξ') :=
    continuousAt_fst.prodMk
      ((coordinateSplit 0).continuous.snd.continuousAt.comp continuousAt_snd)
  have hf : ContinuousAt f (A₀, ξ') := by
    exact ((coordinateSplit 0).continuous.fst.continuousAt.comp continuousAt_snd).sub
      (hH.continuousAt.comp (f := fun p : Coeff × E ↦ (p.1, spatialPart p.2)) hparam)
  have hfzero : f (A₀, ξ') = 0 := by
    dsimp [f]
    rw [hspace, hc.1, htime, sub_self]
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hf ε hε
  let a' := min a (min c.coefficientRadius (δ / 2))
  have ha' : 0 < a' := lt_min ha (lt_min c.coefficientRadius_pos (half_pos hδ))
  have haδ : a' < δ := (min_le_right _ _).trans_lt
    ((min_le_right _ _).trans_lt (half_lt_self hδ))
  let P : Set E := {ζ | 0 < c.radialSection (spatialPart ζ)}
  let W : Set E := ball ξ' (δ / 2) ∩ spatialPart ⁻¹' ball (coordinateSplit c.index ξ).2 b
  let V' : Set E := P ∩ normalizeCovector c.radialSection ⁻¹' W
  let V : Set E := c.angularNeighborhood ∩ (physicalCoordinates c.index).symm ⁻¹' V'
  have hP : IsOpen P := isOpen_lt continuous_const
    (c.radialSection.continuous.comp (coordinateSplit 0).continuous.snd)
  have hW : IsOpen W := isOpen_ball.inter
    (isOpen_ball.preimage (coordinateSplit 0).continuous.snd)
  have hn : ContinuousOn (normalizeCovector c.radialSection) P := fun ζ hζ ↦
    (contDiffAt_normalizeCovector c.radialSection (ne_of_gt hζ)).continuousAt.continuousWithinAt
  have hV' : IsOpen V' := hn.isOpen_inter_preimage hP hW
  have hV : IsOpen V := c.isOpen_angularNeighborhood.inter
    (hV'.preimage (physicalCoordinates c.index).symm.continuous)
  have hξV : ξ ∈ V := by
    refine ⟨c.center_mem_angularNeighborhood, ?_⟩
    change 0 < c.radialSection (spatialPart ξ') ∧ normalizeCovector c.radialSection ξ' ∈ W
    rw [hsection, hnormalize]
    exact ⟨zero_lt_one, mem_ball_self (half_pos hδ), by
      change spatialPart ξ' ∈ ball (coordinateSplit c.index ξ).2 b
      rw [hspace]
      exact mem_ball_self hb⟩
  refine ⟨a', ha', min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    V, hV, hξV, inter_subset_left, ?_, 1 + ‖ξ'‖ + δ / 2, by positivity, ?_⟩
  · intro ζ hζ t ht
    refine ⟨?_, ?_⟩
    · change (coordinateSplit c.index (t • ζ)).2 ∈ c.spatialCone
      simpa only [map_smul, Prod.smul_snd] using c.smul_mem_spatialCone hζ.1 ht
    · change (physicalCoordinates c.index).symm (t • ζ) ∈ V'
      rw [map_smul]
      refine ⟨?_, ?_⟩
      · change 0 < c.radialSection (spatialPart (t • (physicalCoordinates c.index).symm ζ))
        simpa only [spatialPart_smul, map_smul, smul_eq_mul] using mul_pos ht hζ.2.1
      · change normalizeCovector c.radialSection (t • (physicalCoordinates c.index).symm ζ) ∈ W
        rw [normalizeCovector_pos_smul _ _ ht]
        exact hζ.2.2
  · intro ζ hζ ζ'
    have hnear : dist (normalizeCovector c.radialSection ζ') ξ' < δ / 2 := hζ.2.2.1
    refine ⟨hζ.2.1, ball_subset_closedBall hζ.2.2.2, ?_, ?_⟩
    · have hbound := norm_add_le (normalizeCovector c.radialSection ζ' - ξ') ξ'
      rw [sub_add_cancel] at hbound
      rw [dist_eq_norm] at hnear
      linarith
    · intro A hA
      have hpair : dist (A, normalizeCovector c.radialSection ζ') (A₀, ξ') < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        exact ⟨hA.trans_lt haδ, hnear.trans (half_lt_self hδ)⟩
      have h := hsmall hpair
      rw [hfzero, dist_zero_right, Real.norm_eq_abs] at h
      exact h.le

/-- The collar's pointwise coefficient displacement gives the exact consumer
predicate after pulling the ORIGINAL multiplier through `physicalCoordinates`.
It holds on any physical source carrier in the coefficient domain, without
smoothness or derivative assumptions on the field (`complement-symbol`). -/
theorem normalizedSpectralSupport_of_collar
    (c : LocalChart Ω x RQ A₀ ξ M) {a ε : ℝ} {V : Set E}
    (hband : ∀ ζ ∈ V, ∀ A ∈ closedBall A₀ a,
      |normalizeCovector c.radialSection ((physicalCoordinates c.index).symm ζ) 0 -
        c.root (A, spatialPart (normalizeCovector c.radialSection
          ((physicalCoordinates c.index).symm ζ)))| ≤ ε)
    (Q : E → Coeff) {X : Set E} (hQ : MapsTo Q X (closedBall A₀ a))
    (β : E → ℂ) (hβ : tsupport β ⊆ V) :
    NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
      (physicalCoordinates c.index ⁻¹' X) ε (β ∘ physicalCoordinates c.index) := by
  intro y hy ζ hζ
  have hζ' : physicalCoordinates c.index ζ ∈ V :=
    hβ (tsupport_comp_subset_preimage β (physicalCoordinates c.index).continuous hζ)
  have h := hband _ hζ' _ (hQ hy)
  rw [(physicalCoordinates c.index).symm_apply_apply] at h
  simpa only [fieldRoot, rootState, physicalCoordinates_apply] using h

/-- The same normalized covector also lies in the retained open root domain.
This discharges the root-state support input of
`AlgebraicSymbols.normalized_support_subset_complementDomain`
(`app:ch_regular_base:eq:complement-symbol`). -/
theorem normalized_rootState_mem_fieldDomain
    (c : LocalChart Ω x RQ A₀ ξ M) {b : ℝ} (hb : b < c.coefficientRadius)
    {y ζ : E} (hy : physicalCoordinates c.index y ∈ Ω)
    (hpos : 0 < c.radialSection (spatialPart ζ))
    (hη : spatialPart (normalizeCovector c.radialSection ζ) ∈
      closedBall (coordinateSplit c.index ξ).2 b) :
    rootState y (spatialPart (normalizeCovector c.radialSection ζ)) ∈
      fieldDomain (coordinateSplit c.index) Ω c.radialSection
        (coordinateSplit c.index ξ).2 c.coefficientRadius := by
  have hrad : c.radialSection (spatialPart (normalizeCovector c.radialSection ζ)) = 1 := by
    simp only [normalizeCovector, spatialPart_smul, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  change 0 < c.radialSection (spatialPart (normalizeCovector c.radialSection ζ)) ∧
    physicalCoordinates c.index y ∈ Ω ∧ _
  refine ⟨by rw [hrad]; exact zero_lt_one, hy, ?_⟩
  dsimp only [rootState]
  rw [hrad, inv_one, one_smul]
  exact closedBall_subset_ball hb hη

end JanetCartan.RegularSector.Characteristic.AlgebraicChart
