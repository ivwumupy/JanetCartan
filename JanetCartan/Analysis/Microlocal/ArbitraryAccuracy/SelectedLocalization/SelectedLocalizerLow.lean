module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.OrdinaryLocalizer
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion

/-!
# Uniform low bounds for the retained even proof masks

Apply the primitive left-localizer estimate at order zero and scale one.
The literal adjoint supplies the same bound for right quantization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential FiniteChain.Graph
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic
open SelectedEvenProofMasks RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The same joint profile bounds both literal quantizations uniformly in
frequency, coefficients, history and the selected proof mask. Consumer: the
low bounds for actual factors and inserted identities in the alternating
finite chain (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_even_localizer_low_constant
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    (a b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (depth : ℕ) (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E))
        (Γ : Set E) (output : E → ℝ) (aPhase bPhase : f.centers → ℝ)
        (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
        (hcRad : ∀ p k, 0 < cRad p k)
        (Urad : (p : f.centers) → Fin (n p) → Set (RootState (Euclidean d)))
        (buffer εcollar δT δI : ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (Cphase : f.centers → OpenPartialHomeomorph
          (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
        (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
          depth aPhase bPhase n cRad hcRad Urad buffer a b Rbase εcollar δT δI Hmask Q Φ Cphase),
      let masks := hEven.choose_spec.choose
      ∀ (k : Fin (depth+1)) (ρ : ℝ), 1 ≤ ρ →
      ∀ (R Lout : H →L[ℂ] H),
        (∀ u, R u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ (masks k) (fun z ↦ (u z).ofLp) y)) →
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (leftLocalizer ρ (masks k) (fun z ↦ (u z).ofLp) y)) →
        ‖R‖ ≤ C ∧ ‖Lout‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_leftLocalizer_primitive_sobolev_bound
    (r := d+1) (closedBall (0 : E) Rbase) (isCompact_closedBall _ _)
    Hmask hHmask 0 (le_max_left 0 b) 0
  refine ⟨C, hC, ?_⟩
  intro depth χ₂ Ksource Vsource Γ output aPhase bPhase n cRad hcRad Urad
    buffer εcollar δT δI Q Φ Cphase hEven masks k ρ hρ R Lout hR hLout
  obtain ⟨_, _, hbuffered, _, _, _, hcarrier, hjets, _⟩ :=
    hEven.choose_spec.choose_spec
  have hsupp : tsupport (masks k) ⊆
      closedBall (0 : E) Rbase ×ˢ PhysicalShells.frequencyAnnulus a b :=
    fun p hp ↦ (hcarrier k (self_subset_cthickening (tsupport (masks k)) hp)).1
  have hbase : Prod.fst '' tsupport (masks k) ⊆ closedBall (0 : E) Rbase := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hsupp hp).1
  have hann : ∀ p ∈ tsupport (masks k), ‖p.2‖ ≤ max 0 b := by
    intro p hp
    exact (hsupp hp).2.2.trans (le_max_right _ _)
  have hgrades (l : ℕ) (p : E × E) :
      ‖iteratedFDeriv ℝ l (masks k) p‖ ≤ Hmask l * (1 : ℝ) ^ (l+0) := by
    simpa only [one_pow, mul_one] using hjets k l p
  have hleft (M : H →L[ℂ] H)
      (hM : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ (masks k) (fun z ↦ (u z).ofLp) y)) : ‖M‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    have h := hbound (masks k) (hbuffered k).smooth (hbuffered k).compactSupport
      hbase hann ρ 1 hρ le_rfl hgrades M hM u
    simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, pow_zero, one_pow,
      mul_one] using h.2
  refine ⟨?_, hleft Lout hLout⟩
  have h := hleft R.adjoint
    (ResidualLocalization.IdentityDefect.leftLocalizer_adjoint_ae_of_rightLocalizer
      (ne_of_gt (zero_lt_one.trans_le hρ)) (masks k)
      (hbuffered k).smooth.continuous (hbuffered k).compactSupport R hR)
  simpa only [ContinuousLinearMap.adjoint.norm_map] using h

/-- Choose the actual left/right operators of each retained even mask,
with one uniform low constant fixed before the masks and history. The right
operator is the literal adjoint of the chosen left operator, so the chain
and terminal estimates retain one realization
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_even_bounded_localizers_with_uniform_low
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    (a b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (depth : ℕ) (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E))
        (Γ : Set E) (output : E → ℝ) (aPhase bPhase : f.centers → ℝ)
        (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
        (hcRad : ∀ p k, 0 < cRad p k)
        (Urad : (p : f.centers) → Fin (n p) → Set (RootState (Euclidean d)))
        (buffer εcollar δT δI : ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (Cphase : f.centers → OpenPartialHomeomorph
          (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
        (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
          depth aPhase bPhase n cRad hcRad Urad buffer a b Rbase εcollar δT δI Hmask Q Φ Cphase),
      let masks := hEven.choose_spec.choose
      ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ R Lout : Fin (depth+1) → H →L[ℂ] H, ∀ k,
        R k = (Lout k).adjoint ∧
        (∀ u, R k u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ (masks k) (fun z ↦ (u z).ofLp) y)) ∧
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout k u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (masks k) (fun z ↦ (u z).ofLp) y)) ∧
        ‖R k‖ ≤ C ∧ ‖Lout k‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_selected_even_localizer_low_constant
    f eT eI a b Rbase Hmask hHmask
  refine ⟨C, hC, ?_⟩
  intro depth χ₂ Ksource Vsource Γ output aPhase bPhase n cRad hcRad Urad
    buffer εcollar δT δI Q Φ Cphase hEven masks ρ hρ
  have hbuffered := hEven.choose_spec.choose_spec.2.2.1
  choose Lout hleft hright using fun k : Fin (depth+1) ↦
    EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers (q := d+1)
      (ne_of_gt (zero_lt_one.trans_le hρ)) (masks k)
      (hbuffered k).smooth.continuous (hbuffered k).compactSupport
  refine ⟨fun k ↦ (Lout k).adjoint, Lout, fun k ↦ ⟨rfl, hright k, hleft k, ?_⟩⟩
  exact hbound depth χ₂ Ksource Vsource Γ output aPhase bPhase n cRad hcRad Urad
    buffer εcollar δT δI Q Φ Cphase hEven k ρ hρ (Lout k).adjoint (Lout k)
    (hright k) (hleft k)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
