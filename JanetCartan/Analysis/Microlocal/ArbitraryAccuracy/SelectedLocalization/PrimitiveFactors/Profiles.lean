module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Normalized
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# Original coefficient profiles on the retained selected witnesses

These deductions use the phase and amplitude estimates retained by
`exists_finite_direct_operator_bounds`. The original coefficient profile is
the one in `app:ch_regular:eq:initial-coefficient-profile`; the radial threshold
does not occur in its slow scale. Constants are uniform over the fixed family
and chosen before the coefficients, slow scale and source frequency.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The retained local phase estimate gives joint normalized gradient jets
with the original truncated slow-scale exponent, uniformly over the SAME
finite family. `hphase` and `hbuffer` are the exact retained chart outputs of
`exists_finite_direct_operator_bounds`; the compact normalized carrier
inclusion is geometric. Consumer: the `hprimitivePhase` input of `CompleteFactor`
after supported-germ transfer (`app:ch_regular:eq:high-phase`). -/
theorem exists_selected_normalizedPhase_jet_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (Kphase : f.centers → Set (SymbolBudgets.TwoTimePoint d))
    (hKphase : ∀ p, IsCompact (Kphase p))
    (hpos : ∀ p, ∀ w ∈ Kphase p, 0 < (f.chart p).radialSection w.2)
    (hmap : ∀ p,
      let e := coordinateSplit (f.chart p).index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      MapsTo (normalize (f.chart p).radialSection ∘ budgetCoordinates) (Kphase p)
        (closedBall (z.1, z) (f.chart p).targetRadius))
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ P : ℕ → ℝ, (∀ j, 0 ≤ P j) ∧
      ∀ (Rstar : ℕ), 3 ≤ Rstar → ∀ (L ρ : ℝ), 1 ≤ L → 0 < ρ →
      ∀ (Q : E → Fin (d+1) → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      ∀ C : f.centers → OpenPartialHomeomorph T T,
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        closedBall (z.1, z) (f.chart p).targetRadius ⊆ (C p).target) →
      (∀ p m,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        cNorm (closedBall (z.1, z) (f.chart p).targetRadius) m (twoTimePhase (C p)) ≤
          (f.chart p).phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
      ∀ p, ∀ w ∈ Kphase p, ∀ j,
        ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
          (normalizedTwoTimePhase ρ (curriedExtend (f.chart p).radialSection
            (twoTimePhase (C p)))))) w‖ ≤ P j * L ^ (j - 1) := by
  classical
  let D := fun p j ↦ jetBoundConstant (f.chart p).radialSection
    (budgetCoordinates '' Kphase p) (j+1) *
      ((f.chart p).phaseCost (j+1) * (1 + A (j+2)))
  have hD p j : 0 ≤ D p j := mul_nonneg (jetBoundConstant_pos _ _ _).le
    (mul_nonneg ((f.chart p).phaseCost_pos _).le (by linarith [hA (j+2)]))
  refine ⟨fun j ↦ ∑ p, D p j, fun j ↦ Finset.sum_nonneg (fun p _ ↦ hD p j), ?_⟩
  intro Rstar hRstar L ρ hL hρ Q hQ C hC hbuffer hphase p w hw j
  let z : Z := ((coordinateSplit (f.chart p).index x).1,
    ((coordinateSplit (f.chart p).index x).2, (coordinateSplit (f.chart p).index p.val.val).2))
  let J := closedBall (z.1, z) (f.chart p).targetRadius
  have hlocal : cNorm J (j+1) (twoTimePhase (C p)) ≤
      ((f.chart p).phaseCost (j+1) * (1 + A (j+2))) * L ^ (j-1) := by
    have hb := JointBudget.fixed_profile_transfer_bound (r := j+1) (c := 1) (ν := 2)
      hL (hA (j+2)) ((f.chart p).phaseCost_pos (j+1)).le hRstar
      (hQ (j+2)) (hphase p (j+1))
    rw [show j+1-2 = j-1 by omega] at hb
    exact hb
  have hjet : ‖iteratedFDeriv ℝ (j+1) (SymbolBudgets.jointPhase
      (normalizedTwoTimePhase ρ (curriedExtend (f.chart p).radialSection
        (twoTimePhase (C p))))) w‖ ≤
      jetBoundConstant (f.chart p).radialSection (budgetCoordinates '' Kphase p) (j+1) *
        cNorm J (j+1) (twoTimePhase (C p)) := by
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (hKphase p) ?_ hw le_rfl).trans
      (cNorm_normalizedTwoTimePhase_phase_le _ (C p) (hC p) (hKphase p)
        (isCompact_closedBall _ _) (hbuffer p) (hpos p) (hmap p) hρ (j+1))
    intro v hv
    rw [normalizedTwoTimePhase_curriedExtend _ _ hρ]
    exact ((contDiffOn_jointPhase_curriedExtend _ (C p).open_target (hC p)).contDiffAt
      (((isOpen_domain _ (C p).open_target).preimage budgetCoordinates.continuous).mem_nhds
        ⟨hpos p v hv, hbuffer p (hmap p hv)⟩)).of_le (by simp)
  rw [norm_iteratedFDeriv_fderiv]
  apply hjet.trans
  calc
    _ ≤ D p j * L ^ (j-1) :=
      (mul_le_mul_of_nonneg_left hlocal (jetBoundConstant_pos _ _ _).le).trans_eq
        (by dsimp [D]; ring)
    _ ≤ (∑ p, D p j) * L ^ (j-1) := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ ↦ hD p j) (Finset.mem_univ p))
      (pow_nonneg (zero_le_one.trans hL) _)

/-- The SAME three conic amplitudes have a common slow-scale profile while
retaining their orders zero and minus one. The reserve ten and nine is exactly
the retained estimate in `exists_finite_direct_operator_bounds`, including
the full `B` in entry two. Consumer: normalized-symbol grades in `CompleteFactor`
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_amplitude_order_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (ra rb : f.centers → ℝ) (cost : f.centers → ℕ → ℝ)
    (hcost : ∀ p m, 0 < cost p m) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j - Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤ D m * L ^ m := by
  classical
  let Dp := fun p m ↦ cost p m * (1 + A (m+10) + A (m+9))
  have hDp p m : 0 ≤ Dp p m := mul_nonneg (hcost p m).le (by linarith [hA (m+10), hA (m+9)])
  refine ⟨fun m ↦ ∑ p, Dp p m, fun m ↦ Finset.sum_nonneg (fun p _ ↦ hDp p m), ?_⟩
  intro Rstar hRstar L hL Q B hQ hB Φ C angular J W hbudget p j m
  refine ⟨(hbudget p j m).1, (hbudget p j m).2.trans ?_⟩
  have hQ' : cNorm (closedBall x RQ) (m+10) Q ≤ A (m+10) * L ^ m :=
    (hQ (m+10)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : m+10-Rstar ≤ m)) (hA _))
  have hB' : cNorm (closedBall x RQ) (m+9) B ≤ A (m+9) * L ^ m :=
    (hB (m+9)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : m+9-Rstar ≤ m)) (hA _))
  have hone : 1 ≤ L ^ m := one_le_pow₀ hL
  calc
    _ ≤ Dp p m * L ^ m := by
      apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hone hQ') hB')
        (hcost p m).le).trans_eq
      dsimp [Dp]
      ring
    _ ≤ (∑ p, Dp p m) * L ^ m := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ ↦ hDp p m) (Finset.mem_univ p))
      (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
