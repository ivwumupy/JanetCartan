module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.BufferedCollar

/-!
# A common collar for the finite physical residual family

The total carrier includes both external bases, closed input shoulders and
all three covectors. Both literal orientations share positive gaps, a collar
width and derivative profiles. No fixed-time arbitrary-energy graph separation
is inferred. The consumer is the collar interface of the integrated residual
estimate in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph EvolutionIntegratedLocalization JanetCartan.Localization
attribute [local fun_prop] ContDiff.inner
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E

private theorem contDiff_jointElapsedPhase_with_bases
    (Ψ : TwoTimePhase d) (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ)) (backward : Bool) :
    ContDiff ℝ ∞ (fun t : (E × E) × V ↦ jointElapsedPhase backward Ψ t.1.1 t.1.2 t.2) := by
  let f := fun t : (E × E) × V ↦ SymbolBudgets.jointPhase Ψ (elapsedJointCoordinates t.2)
  have hf : ContDiff ℝ ∞ f := hΨ.comp
    ((elapsedJointCoordinates (d := d)).contDiff.comp contDiff_snd)
  have hz : ContDiff ℝ ∞ (fun t : (E × E) × V ↦
      jointElapsedPhase backward (fun _ _ _ _ ↦ 0) t.1.1 t.1.2 t.2) := by
    unfold jointElapsedPhase jointPhase forwardPhase reversePhase elapsedPhase
    cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> fun_prop
  have hs : ContDiff ℝ ∞ (if backward then -f else f) := by
    cases backward
    · exact hf
    · exact hf.neg
  convert hs.add hz using 1
  funext t
  cases backward <;>
    simp only [jointElapsedPhase, jointPhase, Bool.false_eq_true, ↓reduceIte,
      forwardPhase, reversePhase, elapsedPhase, Pi.neg_apply,
      f, SymbolBudgets.jointPhase, elapsedJointCoordinates,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] <;> ring

/-- Instantiate the geometric collar producer on the actual finite-family
carrier and take common constants for the forward and literal-adjoint
orientations. The supported phase germs and whole chart restrictions are
inputs from `ResidualCoordinates`; the diagonal and oriented zero-energy
plateaus are inputs from the protected masks. Joint first-derivative continuity is derived from smoothness of the same
supported phase and discreteness of the finite chart index.
All constants precede the finite index, both external bases and accuracy
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_finiteFamily_buffered_residual_collar
    {α ι κ : Type*} [Finite α] [TopologicalSpace α] [DiscreteTopology α] [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (bases : α → Set (E × E)) (carrier : α → Set V)
    (mi mo : α → LocalizerSymbol (d + 1))
    (hbases : ∀ a, IsCompact (bases a)) (hcarrier : ∀ a, IsCompact (carrier a))
    (h : α → RootState (Euclidean d) → ℝ)
    (Φ : α → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : α → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (Ψ : α → TwoTimePhase d)
    (R : α → Set (E × E)) :
    let K := elapsedFiniteFamilyCarrier bases carrier mi mo
    ∀ (_hΨ : ∀ t, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ t)))
    (_hC : ∀ t, (C t : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ t))
    (_hdiag : ∀ t, tsupport (mi t) ⊆ interior {p | mo t p = 1})
    (_hflow : ∀ backward, ∀ t ∈ K, 0 < t.2.1 → ∀ a ∈ tsupport (mi t.1.1), ∀ b ∈ R t.1.1,
      zeroEnergyFlowRelation backward (h t.1.1) (Φ t.1.1) t.2.1 a b →
        b ∈ interior {p | mo t.1.1 p = 1})
    (_hR : ∀ t ∈ K, (t.1.2.1, t.2.2.2.2.2) ∈ R t.1.1)
    (_hqB : ∀ t ∈ K, elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1.1).target)
    (_hi : ∀ t ∈ K,
      Φ t.1.1 (((C t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2, 0) =
        ((C t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2)
    (_hphaseB : ∀ t ∈ K, HasFDerivAt (twoTimePhase (C t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (C t.1.1)
        (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
    (_hqI : ∀ t ∈ K, 0 < t.2.1 →
      elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1.1).target)
    (_hclock : ∀ t ∈ K, 0 < t.2.1 →
      (twoTimeState (Φ t.1.1) ((C t.1.1).symm
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))).1 = t.2.2.1.1 0)
    (_hphaseI : ∀ t ∈ K, 0 < t.2.1 → HasFDerivAt (twoTimePhase (C t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (C t.1.1)
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
    (_hGermB : ∀ t ∈ K, SymbolBudgets.jointPhase (Ψ t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates (0, t.2.2))] SymbolBudgets.jointPhase (chartPhase (C t.1.1)))
    (_hGermI : ∀ t ∈ K, 0 < t.2.1 → SymbolBudgets.jointPhase (Ψ t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates t.2)] SymbolBudgets.jointPhase (chartPhase (C t.1.1))),
    ∃ (χ : Bool → V → ℂ) (UT UI : Bool → α × (E × E) → Set V)
      (ε δT δI G : ℝ) (H : ℕ → ℝ),
      0 < ε ∧ 0 < δT ∧ 0 < δI ∧ (∀ j, 0 ≤ H j) ∧
      ∀ backward,
      ContDiff ℝ ∞ (χ backward) ∧
      (∀ t, IsOpen (UT backward t)) ∧ (∀ t, IsOpen (UI backward t)) ∧
      (∀ p, |p.1| < ε → χ backward p = 1) ∧
      (∀ a x y, (x, y) ∈ bases a →
        elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y ∩ tsupport (χ backward) ⊆
          UT backward (a, x, y)) ∧
      (∀ a x y, (x, y) ∈ bases a →
        (elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y ∩ tsupport (1 - χ backward)) ∩
          {p | 0 < p.1} ⊆ UI backward (a, x, y)) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward t →
        δT ≤ phaseGradientSquare eT
          (fun w ↦ jointElapsedPhase backward (Ψ t.1) t.2.1 t.2.2 (r, w)) p) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward t →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t.1) t.2.1 t.2.2) (r, p)‖ ≤ G) ∧
      (∀ t p, p ∈ UI backward t ∩ {p | 0 < p.1} →
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (Ψ t.1) t.2.1 t.2.2) p) ∧
      (∀ t p, p ∈ UI backward t ∩ {p | 0 < p.1} →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t.1) t.2.1 t.2.2) p‖ ≤ G) ∧
      (∀ a x y, (x, y) ∈ bases a →
        ∀ p ∈ elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y, ∀ j,
          ‖iteratedFDeriv ℝ j (χ backward) p‖ ≤ H j) := by
  classical
  intro K hΨ hC hdiag hflow hR hqB hi hphaseB hqI hclock hphaseI
    hGermB hGermI
  have hK : IsCompact K := isCompact_elapsedFiniteFamilyCarrier bases carrier mi mo hbases hcarrier
  have hfull (a : α) (backward : Bool) := contDiff_jointElapsedPhase_with_bases (Ψ a) (hΨ a) backward
  have hcontI (backward : Bool) : ContinuousOn (fun t : (α × (E × E)) × V ↦
      fderiv ℝ (jointElapsedPhase backward (Ψ t.1.1) t.1.2.1 t.1.2.2) t.2) K := by
    have hc : Continuous (fun t : α × ((E × E) × V) ↦
        fderiv ℝ (jointElapsedPhase backward (Ψ t.1) t.2.1.1 t.2.1.2) t.2.2) := by
      apply continuous_prod_of_discrete_left.mpr
      intro a
      have hcd : ContDiff ℝ ∞ (fun t : (E × E) × V ↦
          fderiv ℝ (jointElapsedPhase backward (Ψ a) t.1.1 t.1.2) t.2) := by
        apply ContDiff.fderiv (m := ∞)
          (f := fun t : (E × E) × V ↦ jointElapsedPhase backward (Ψ a) t.1.1 t.1.2)
          (g := Prod.snd) _ contDiff_snd (by simp)
        exact (hfull a backward).comp
          (f := fun t : ((E × E) × V) × V ↦ (t.1.1, t.2))
          (contDiff_fst.fst.prodMk contDiff_snd)
      exact hcd.continuous
    exact (hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).continuousOn
  have hcontB (backward : Bool) : ∀ t ∈ K, ContinuousAt
      (fun tr : ((α × (E × E)) × V) × ℝ ↦
        fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ tr.1.1.1) tr.1.1.2.1 tr.1.1.2.2
          (tr.2, w)) tr.1.2.2) (t, 0) := by
    have hc : Continuous (fun t : α × (((E × E) × V) × ℝ) ↦
        fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ t.1) t.2.1.1.1 t.2.1.1.2
          (t.2.2, w)) t.2.1.2.2) := by
      apply continuous_prod_of_discrete_left.mpr
      intro a
      have hcd : ContDiff ℝ ∞ (fun t : ((E × E) × V) × ℝ ↦
          fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ a) t.1.1.1 t.1.1.2
            (t.2, w)) t.1.2.2) := by
        apply ContDiff.fderiv (m := ∞)
          (f := fun t : ((E × E) × V) × ℝ ↦ fun w ↦
            jointElapsedPhase backward (Ψ a) t.1.1.1 t.1.1.2 (t.2, w))
          (g := fun t ↦ t.1.2.2) _ contDiff_fst.snd.snd (by simp)
        exact (hfull a backward).comp
          (f := fun t : (((E × E) × V) × ℝ) × JointVariables E ↦ (t.1.1.1, (t.1.2, t.2)))
          (show ContDiff ℝ ∞ (fun t : (((E × E) × V) × ℝ) × JointVariables E ↦
            (t.1.1.1, (t.1.2, t.2))) from by fun_prop)
      exact hcd.continuous
    have h := hc.comp (show Continuous (fun t : ((α × (E × E)) × V) × ℝ ↦
      (t.1.1.1, ((t.1.1.2, t.1.2), t.2))) from by fun_prop)
    exact fun t _ ↦ h.continuousAt
  have hdata (backward : Bool) := exists_buffered_supportedPhase_collar_data eT eI backward
    (fun t : α × (E × E) ↦ h t.1) (fun t ↦ Φ t.1) (fun t ↦ C t.1)
    (fun t ↦ Ψ t.1) (fun t ↦ t.2.1) (fun t ↦ t.2.2)
    (fun t ↦ mi t.1) (fun t ↦ mo t.1) (fun t ↦ R t.1) hK
    (fun t ↦ hΨ t.1) (fun t ↦ hC t.1) (fun t ↦ hdiag t.1)
    (hflow backward) (fun _ ht ↦ ht.2.2.1) (fun _ ht ↦ ht.2.2.2) hR hqB hi hphaseB hqI hclock hphaseI hGermB hGermI
    (hcontB backward) (hcontI backward)
  choose χ UT UI ε δT δI G H hχ hUT hUI hε hδT hδI hχone hχT hχI
    hgapT hupperT hgapI hupperI hH hχbound using hdata
  have hmin (f : Bool → ℝ) (b : Bool) : min (f false) (f true) ≤ f b := by
    cases b
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hmax (f : Bool → ℝ) (b : Bool) : f b ≤ max (f false) (f true) := by
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨χ, UT, UI, min (ε false) (ε true), min (δT false) (δT true),
    min (δI false) (δI true), max (G false) (G true), fun j ↦ H false j + H true j,
    lt_min (hε false) (hε true), lt_min (hδT false) (hδT true),
    lt_min (hδI false) (hδI true), fun j ↦ add_nonneg (hH false j) (hH true j), ?_⟩
  intro backward
  refine ⟨hχ backward, hUT backward, hUI backward,
    fun p hp ↦ hχone backward p (hp.trans_le (hmin ε backward)), ?_, ?_,
    fun t r hr p hp ↦ (hmin δT backward).trans (hgapT backward t r hr p hp),
    fun t r hr p hp ↦ (hupperT backward t r hr p hp).trans (hmax G backward),
    fun t p hp ↦ (hmin δI backward).trans (hgapI backward t p hp),
    fun t p hp ↦ (hupperI backward t p hp).trans (hmax G backward), ?_⟩
  · intro a x y hxy p hp
    exact hχT backward (a, x, y) ⟨⟨hxy, hp.1⟩, hp.2⟩
  · intro a x y hxy p hp
    exact hχI backward (a, x, y) ⟨⟨⟨hxy, hp.1.1⟩, hp.1.2⟩, hp.2⟩
  · intro a x y hxy p hp j
    apply (hχbound backward p ⟨((a, x, y), p), ⟨hxy, hp⟩, rfl⟩ j).trans
    cases backward
    · exact le_add_of_nonneg_right (hH true j)
    · exact le_add_of_nonneg_left (hH false j)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
