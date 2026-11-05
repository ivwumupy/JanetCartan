module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.Uniform.Sobolev
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.CanonicalBounds

/-!
# Actual uniform identity leakage on selected even mask pairs

The original nested family supplies the common frequency support, derivative
profile and diagonal buffer. The resulting constants work before the varying
coefficients and on both physical masks and their canonical pullbacks.
-/

@[expose] public noncomputable section
open MeasureTheory Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph FourierIntegral LowBounds Pseudodifferential
open ProtectedMasks SelectedEvenProofMasks
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
local notation "Hspace" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

/-- Instantiate the uniform identity estimate on consecutive masks of the
SAME actual even family. `none` denotes the physical masks and `some p` their
literal canonical pullbacks for chart `p`; no new masks are chosen. The common
constant precedes the coefficient field, protected phase and masks. It controls
the single identity term required by the selected finite residual sum and
`finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_even_identityLeakage_fourierSobolev_bound
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
    (hcRad : ∀ p k, 0 < cRad p k) (Urad : (p : f.centers) → Fin (n p) → Set (RootState (Euclidean d)))
    (buffer a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (hbuffer : 0 < buffer) (hH : ∀ j, 0 ≤ H j) (order : ℕ)
 :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cphase : f.centers → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
      (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
      N aPhase bPhase n cRad hcRad Urad buffer a b Rbase εcollar δT δI H Q Φ Cphase),
      let masks := hEven.choose_spec.choose
      ∀ (k : Fin N) (chart : Option f.centers),
      let mi := match chart with
        | none => masks k.castSucc
        | some p => canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.castSucc)
      let mo := match chart with
        | none => masks k.succ
        | some p => canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.succ)
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (Mi Mo : Hspace →L[ℂ] Hspace),
      (∀ u, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      ∀ accuracy (u : Hspace),
        MemVectorFourierSobolev (order : ℝ) ((1 - Mo) (Mi u)) ∧
        vectorFourierSobolevNorm (order : ℝ) ((1 - Mo) (Mi u)) ≤
          C accuracy * ρ ^ (d + 1 + order) * (L / ρ) ^ accuracy * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    ResidualLocalization.IdentityDefect.exists_identityLeakage_fourierSobolev_bound_of_uniform_profiles
      (n := d+1) (r := q) b H H hH hH hbuffer order
  refine ⟨C, hC, ?_⟩
  intro Q Φ Cphase hEven masks k chart mi mo
  obtain ⟨_, _, hbuf, _, _, _, hsupport, hjoints, hnest, hcan, hcanSupport, hcanJets, _⟩ :=
    hEven.choose_spec.choose_spec
  have hdiag : ∀ z ∈ tsupport (masks k.castSucc),
      closedBall z buffer ⊆ interior {w | masks k.succ w = 1} := by
    intro z hz
    exact hnest k z (self_subset_cthickening _ hz) z (Or.inl rfl)
  cases chart with
  | none =>
    apply hbound (masks k.castSucc) (masks k.succ)
      (hbuf k.castSucc).smooth (hbuf k.castSucc).compactSupport
      (hbuf k.succ).smooth (hbuf k.succ).range
    · rintro ξ ⟨z, hz, rfl⟩
      have h := (hsupport k.castSucc (self_subset_cthickening _ hz)).1.2.2
      simpa only [mem_closedBall, dist_zero_right] using h
    · exact hjoints k.castSucc
    · exact hjoints k.succ
    · exact hdiag
  | some p =>
    apply hbound _ _ (hcan k.castSucc p).smooth (hcan k.castSucc p).compactSupport
      (hcan k.succ p).smooth (hcan k.succ p).range
    · rintro ξ ⟨z, hz, rfl⟩
      have h := (hcanSupport k.castSucc p hz).2.2
      simpa only [mem_closedBall, dist_zero_right] using h
    · exact hcanJets k.castSucc p
    · exact hcanJets k.succ p
    · rw [tsupport_canonicalProofLocalizer]
      exact canonicalProofLocalizer_closedBall_plateau (f.chart p).index hdiag

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
