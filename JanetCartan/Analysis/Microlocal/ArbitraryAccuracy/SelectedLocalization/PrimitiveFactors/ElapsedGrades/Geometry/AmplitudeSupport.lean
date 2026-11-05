module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Domains
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Amplitudes

/-!
# Retained amplitude jets outside the buffered carrier

The joint carrier also contains points outside the transported amplitude.
At those points the actual normalized residual jet is zero. This supplies
the support alternative needed when applying the original `W₂` profiles
to the auxiliary constructed in `selected_common_smooth_direct_residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.ConicAmplitude
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification
open Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionIntegratedLocalization FiniteChain.Graph
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "V" => ℝ × JointVariables E

/-- Every nonzero joint derivative of the actual normalized auxiliary
residual lies in the retained buffered jet set, provided its section radius
lies in the retained band. Outside that set the derivative vanishes.
`hF` and `hang` are the local residual support and selected angular positivity
retained by `exists_finite_direct_operator_bounds`. Only the geometric
radial-band comparison remains explicit; no amplitude estimate is assumed.
Consumer: the `Qb` component of `CompleteFactor.hprimitiveMasks`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_normalizedResidual_jet_carrier_or_eq_zero
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (angular : Euclidean d → ℝ)
    (hang : ∀ η ∈ tsupport angular, 0 < (f.chart p).radialSection η)
    (F : T → Matrix (Fin q) (Fin q) ℂ)
    (hF :
      let c := f.chart p
      let e := coordinateSplit c.index
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
      tsupport F ⊆ closedBall (z.1, z) (c.bufferRadius / 2))
    {ρ : ℝ} (hρ : 0 < ρ) (ra rb : ℝ) (v : V)
    (hband : (f.chart p).radialSection (spatialPart v.2.2.1) ∈ Icc ra rb) (m : ℕ) :
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    let W₂ := collared c.radialSection 1 angular F
    let b := fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W₂ (t, (s, (y, η)))
    elapsedJointCoordinates v ∈ bufferedJetSet c.radialSection z (c.bufferRadius / 2) ra rb ∨
      iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ b) v = 0 := by
  intro c e z W₂ b
  by_cases hj : iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ b) v = 0
  · exact Or.inr hj
  have hv := support_iteratedFDeriv_subset m hj
  let H : V → T := fun w ↦
    (w.2.1.1 0, (w.2.1.1 0 - w.1, (spatialPart w.2.1.1, spatialPart (ρ • w.2.2.1))))
  have hH : Continuous H := by
    have ht : Continuous (fun w : V ↦ w.2.1.1 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).continuous.comp continuous_snd.fst.fst
    exact ht.prodMk ((ht.sub continuous_fst).prodMk
      ((spatialPartCLM.continuous.comp continuous_snd.fst.fst).prodMk
        (spatialPartCLM.continuous.comp (continuous_snd.snd.fst.const_smul ρ))))
  have heq : normalizedElapsedSymbol ρ b =
      fun w : V ↦ chartOutputMask f p (timeSpacePoint (w.2.1.1 0) (spatialPart w.2.1.1)) • W₂ (H w) := rfl
  rw [heq] at hv
  have hW : H v ∈ tsupport W₂ := tsupport_comp_subset_preimage W₂ hH
    (tsupport_smul_subset_right _ _ hv)
  have hd := UniformAmplitudes.tsupport_collared_subset_domain c.radialSection 1 angular hang F hF hW
  let w : T := (v.2.1.1 0, (v.2.1.1 0 - v.1, (spatialPart v.2.1.1, spatialPart v.2.2.1)))
  have hd' : w ∈ ConicPhase.domain c.radialSection (closedBall (z.1, z) (c.bufferRadius / 2)) := by
    have hh := mem_domain_smul c.radialSection hd (inv_pos.mpr hρ)
    simpa only [H, spatialPart_smul, inv_smul_smul₀ hρ.ne'] using hh
  have hp := hd'.2
  change dist (ConicPhase.normalize c.radialSection w) (z.1, z) ≤ c.bufferRadius / 2 at hp
  simp only [ConicPhase.normalize, Prod.dist_eq, max_le_iff] at hp
  refine Or.inl ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact hp.1.trans (by linarith [c.bufferRadius_pos])
  · exact hp.2.1.trans (by linarith [c.bufferRadius_pos])
  · exact hp.2.2.1.trans (by linarith [c.bufferRadius_pos])
  · refine ⟨(c.radialSection w.2.2.2, (c.radialSection w.2.2.2)⁻¹ • w.2.2.2),
      ⟨hband, hp.2.2.2, ?_⟩, ?_⟩
    · exact normalization_eq_one c.radialSection hd'.1.ne'
    · exact smul_inv_smul₀ hd'.1.ne' _

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
