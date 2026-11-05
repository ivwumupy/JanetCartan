module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Local
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.LowPhase

/-!
# Normalized conic jets in the elapsed-budget coordinates

`SymbolBudgets.TwoTimePoint` is `((t,(s,y)),η)`, while the characteristic
chart uses `(t,(s,(y,η)))`. The fixed reassociation is a contraction for the
product norms. Exact homogeneity removes every positive radial scale before
any differentiation, so the local-jet estimate loses zero derivatives.
Consumers: the phase budgets of `app:ch_regular_base:lem:retarded-kernel`
and `app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open EvolutionIntegral

variable {d : ℕ}

/-- Reassociate the actual joint-budget coordinates into the characteristic
chart coordinates (`app:ch_regular_base:eq:fixed-time-representation`). -/
def budgetCoordinates : SymbolBudgets.TwoTimePoint d →L[ℝ] TwoTimePoint (Euclidean d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ (p.1.1, (p.1.2.1, (p.1.2.2, p.2)))
      map_add' := by intro p q; rfl
      map_smul' := by intro a p; rfl }

/-- The reassociation incurs no norm cost in the joint phase jets of
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_budgetCoordinates_le : ‖budgetCoordinates (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [one_mul]
  change ‖(p.1.1, (p.1.2.1, (p.1.2.2, p.2)))‖ ≤ ‖p‖
  simp only [Prod.norm_def, max_assoc, le_refl]

/-- The same conic extension in the curried convention of the retarded
kernel (`app:ch_regular_base:lem:retarded-kernel`). -/
def curriedExtend (ℓ : Euclidean d →L[ℝ] ℝ)
    (F : TwoTimePoint (Euclidean d) → ℝ) : TwoTimePhase d :=
  fun t s y η ↦ extend ℓ F (t, (s, (y, η)))

/-- The joint phase is the literal fixed coordinate pullback
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem jointPhase_curriedExtend (ℓ : Euclidean d →L[ℝ] ℝ)
    (F : TwoTimePoint (Euclidean d) → ℝ) :
    SymbolBudgets.jointPhase (curriedExtend ℓ F) = extend ℓ F ∘ budgetCoordinates := rfl

/-- Positive radial normalization fixes the actual continued phase, globally
as a function, before taking any jets (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem normalizedTwoTimePhase_curriedExtend (ℓ : Euclidean d →L[ℝ] ℝ)
    (F : TwoTimePoint (Euclidean d) → ℝ) {R : ℝ} (hR : 0 < R) :
    SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F) = curriedExtend ℓ F := by
  funext t s y η
  change R⁻¹ * extend ℓ F (t, (s, (y, R • η))) = extend ℓ F (t, (s, (y, η)))
  rw [extend_smul ℓ F (t, (s, (y, η))) hR, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- Joint smoothness of the same conic extension in the budget coordinates.
The only phase smoothness input is the original local one from
`app:ch_regular_base:lem:characteristic-kernel`. -/
theorem contDiffOn_jointPhase_curriedExtend (ℓ : Euclidean d →L[ℝ] ℝ)
    {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (curriedExtend ℓ F))
      (budgetCoordinates ⁻¹' domain ℓ U) :=
  (contDiffOn_extend ℓ hU hF).comp budgetCoordinates.contDiff.contDiffOn (fun _ hp ↦ hp)

/-- The normalized joint budget follows from the local phase jets on `J`,
uniformly over all positive radii, with zero derivative shift. The coordinate
image of `K` fixes the constant before `F` or `R` is chosen
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem cNorm_normalizedTwoTimePhase_curriedExtend_le (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (SymbolBudgets.TwoTimePoint d)} {J U : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ p ∈ K, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) K J)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {R : ℝ} (hR : 0 < R) (n : ℕ) :
    cNorm K n (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase R
      (curriedExtend ℓ F))) ≤
        jetBoundConstant ℓ (budgetCoordinates '' K) n * cNorm J n F := by
  rw [normalizedTwoTimePhase_curriedExtend ℓ F hR, jointPhase_curriedExtend]
  have himage := hK.image (budgetCoordinates (d := d)).continuous
  have himagepos : ∀ q ∈ budgetCoordinates '' K, 0 < ℓ q.2.2.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact hpos p hp
  have himagemap : MapsTo (normalize ℓ) (budgetCoordinates '' K) J := by
    rintro q ⟨p, hp, rfl⟩
    exact hmap hp
  have hsubset : budgetCoordinates '' K ⊆ domain ℓ U :=
    fun q hq ↦ ⟨himagepos q hq, hJU (himagemap hq)⟩
  have h := SymbolBudgets.cNorm_preAffine_contraction_le budgetCoordinates
    norm_budgetCoordinates_le 0 himage (isOpen_domain ℓ hU) hsubset
    (contDiffOn_extend ℓ hU hF)
    (show MapsTo (fun p ↦ budgetCoordinates p + 0) K (budgetCoordinates '' K) by
      simpa only [add_zero] using mapsTo_image (budgetCoordinates (d := d)) K) n
  simp only [add_zero] at h
  exact h.trans (cNorm_extend_le ℓ himage hJ hU hJU himagepos himagemap hF n)

/-- Choose the normalized joint constant before the local phase and radial
scale. Every derivative through order `n` is bounded by local jets of order
`n`, including all time derivatives (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_normalizedTwoTimePhase_jet_bound (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (SymbolBudgets.TwoTimePoint d)} {J U : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ p ∈ K, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) K J) (n : ℕ) :
    ∃ A > (0 : ℝ), ∀ F : TwoTimePoint (Euclidean d) → ℝ,
      ContDiffOn ℝ ∞ F U → ∀ R > (0 : ℝ),
      cNorm K n (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase R
        (curriedExtend ℓ F))) ≤ A * cNorm J n F ∧
      ∀ k ≤ n, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ k (SymbolBudgets.jointPhase
          (SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F))) p‖ ≤
            A * cNorm J n F := by
  refine ⟨jetBoundConstant ℓ (budgetCoordinates '' K) n,
    jetBoundConstant_pos _ _ _, fun F hF R hR ↦ ?_⟩
  have hb := cNorm_normalizedTwoTimePhase_curriedExtend_le ℓ hK hJ hU hJU hpos hmap hF hR n
  refine ⟨hb, fun k hk p hp ↦ ?_⟩
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK ?_ hp hk).trans hb
  intro q hq
  rw [normalizedTwoTimePhase_curriedExtend ℓ F hR]
  exact ((contDiffOn_jointPhase_curriedExtend ℓ hU hF).contDiffAt
    (((isOpen_domain ℓ hU).preimage budgetCoordinates.continuous).mem_nhds
      ⟨hpos q hq, hJU (hmap hq)⟩)).of_le (by simp)

/-- Specialization to the actual inverse-chart phase. `hC` is precisely the
local smoothness published by `exists_buffered_physical_pencil_kernel`; no
extended smoothness or normalized jet budget is assumed. Consumer: the conic
assembly of `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem cNorm_normalizedTwoTimePhase_phase_le (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {K : Set (SymbolBudgets.TwoTimePoint d)} {J : Set (TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hJC : J ⊆ C.target)
    (hpos : ∀ p ∈ K, 0 < ℓ p.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) K J)
    {R : ℝ} (hR : 0 < R) (n : ℕ) :
    cNorm K n (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase R
      (curriedExtend ℓ (twoTimePhase C)))) ≤
        jetBoundConstant ℓ (budgetCoordinates '' K) n * cNorm J n (twoTimePhase C) :=
  cNorm_normalizedTwoTimePhase_curriedExtend_le ℓ hK hJ C.open_target hJC hpos hmap hC hR n

end JanetCartan.RegularSector.Characteristic.ConicPhase
