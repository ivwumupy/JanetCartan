module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.Regularity

/-!
# Reserved full-source profiles of the same endpoint

The compact nonzero normalized frequency set supplies the original endpoint
jet carrier. Contracting the redundant packed variables and multiplying by
the same source frequency produce the literal order-minus-one normalization.
Both physical masks and the exchanged Hilbert adjoint are retained.
Consumer: the annular endpoint of `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open ResidualLocalization ResponseTransfer ResponseTransfer.NearCarrierAssembly
open ResponseTransfer.NearCarrierFullLow

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Vbig" => FiniteChain.Graph.JointVariables E
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The actual retained endpoint certificate gives global smoothness and
reserved normalized jets on every fixed compact nonzero frequency carrier.
The bound is global in both physical positions; their original masks supply
zero jets outside their supports. The exchanged literal adjoint has the same
constant and reserve (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_endpoint_reserved_full_source_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (Jfreq : Set E) (hJfreq : IsCompact Jfreq) (hzero : (0 : E) ∉ Jfreq)
    (AQ AB : ℕ → ℝ) (cost : f.centers → ℕ → ℝ)
    (hAQ : ∀ m, 0 ≤ AQ m) (hAB : ∀ m, 0 ≤ AB m)
    (hcost : ∀ p m, 0 ≤ cost p m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (Rreserve Rcoeff : ℕ), Rreserve+10 ≤ Rcoeff →
      ∀ (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ Q : E → Fin (d+1) → MetricTensor (d+1), ContDiffOn ℝ ∞ Q Ω →
      ∀ B : E → MetricTensor (d+1),
      (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rcoeff)) →
      (∀ m, cNorm (closedBall x RQ) m B ≤ AB m * L ^ (m-Rcoeff)) →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ cost p m *
          (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p,
      let A := ρ • orientedMaskedPDOAmplitude false
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q (W p))
      ContDiff ℝ ∞ (normalizedFullAmplitude A ρ) ∧
      (∀ k v, v.2.2 ∈ Jfreq →
        ‖iteratedFDeriv ℝ k (normalizedFullAmplitude A ρ) v‖ ≤
          D k * L ^ (k-Rreserve)) ∧
      ContDiff ℝ ∞ (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) ∧
      (∀ k v, v.2.2 ∈ Jfreq →
        ‖iteratedFDeriv ℝ k (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) v‖ ≤
          D k * L ^ (k-Rreserve)) := by
  classical
  obtain ⟨a, ha, haball⟩ := Metric.isOpen_iff.mp hJfreq.isClosed.isOpen_compl 0 hzero
  have hafreq {ξ : E} (hξ : ξ ∈ Jfreq) : a ≤ ‖ξ‖ := by
    by_contra hh
    exact haball (mem_ball_zero_iff.mpr (lt_of_not_ge hh)) hξ
  let Jpdo := fun p ↦
    (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)) ×ˢ
      (Jfreq ×ˢ (({0} : Set E) ×ˢ ({0} : Set E)))
  have hJpdo p : IsCompact (Jpdo p) :=
    ((endpointOutputMask_properties f p ho hoc hout).2.1.prod
      (chartPhysicalMasks_properties f p).2.2.2.1).prod
      (hJfreq.prod (isCompact_singleton.prod isCompact_singleton))
  obtain ⟨D, hD, hraw⟩ := exists_selected_endpoint_symbol_reserved_grades
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
    Jpdo hJpdo (fun _ _ hv ↦ hv.1.1) ha (fun _ _ hv ↦ hafreq hv.2.1)
    AQ AB cost hAQ hAB hcost
  let P : V →L[ℝ] Vbig :=
    ((ContinuousLinearMap.fst ℝ E (E × E)).prod
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))).prod
        (((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).prod
          ((0 : V →L[ℝ] E).prod (0 : V →L[ℝ] E)))
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro v
    change max (max ‖v.1‖ ‖v.2.1‖) (max ‖v.2.2‖ (max ‖(0 : E)‖ ‖(0 : E)‖)) ≤ 1*‖v‖
    simp [Prod.norm_def, max_assoc]
  refine ⟨D, hD, ?_⟩
  intro Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W J hW hbudget p A
  let o := endpointOutputMask f p output
  let i := chartInputMask f p
  let raw := orientedMaskedPDOAmplitude false o i (selectedEndpointSymbol f p threshold Q (W p))
  let g := normalizedFullAmplitude raw ρ
  have hg : ContDiff ℝ ∞ g := contDiff_normalized_selected_endpoint_amplitude
    f p hΩ hball threshold ρ output ho hoc hout Q hQ (W p) (hW p)
  have hgs : tsupport g ⊆ {v : V | v.1 ∈ tsupport o ∧ v.2.1 ∈ tsupport i} := by
    apply closure_minimal
      (t := {v : V | v.1 ∈ tsupport o ∧ v.2.1 ∈ tsupport i})
    · intro v hv
      constructor
      · by_contra hh
        exact hv (by simp [g, raw, normalizedFullAmplitude, orientedMaskedPDOAmplitude,
          image_eq_zero_of_notMem_tsupport hh])
      · by_contra hh
        exact hv (by simp [g, raw, normalizedFullAmplitude, orientedMaskedPDOAmplitude,
          image_eq_zero_of_notMem_tsupport hh])
    · exact ((isClosed_tsupport o).preimage continuous_fst).inter
        ((isClosed_tsupport i).preimage continuous_snd.fst)
  have hgj k (v : V) (hv : v.2.2 ∈ Jfreq) :
      ‖iteratedFDeriv ℝ k g v‖ ≤ ρ⁻¹ * D k * L ^ (k-Rreserve) := by
    by_cases hs : v.1 ∈ tsupport o ∧ v.2.1 ∈ tsupport i
    · let G : Vbig → Mat := fun w ↦ g (w.1.1,w.1.2,w.2.1)
      have hG : ContDiff ℝ ∞ G := hg.comp
        (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd.fst))
      change ‖iteratedFDeriv ℝ k (G ∘ P) v‖ ≤ _
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P isOpen_univ
        hG.contDiffOn (mem_univ _) k).trans
      apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hP)).trans
      exact (hraw Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W hW hbudget p false).1
        (P v) ⟨hs,hv,rfl,rfl⟩ k
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh ↦ hs (hgs ((tsupport_iteratedFDeriv_subset k) hh))), norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (hD k)) (by positivity)
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hA : ContDiff ℝ ∞ (normalizedFullAmplitude A ρ) := hg.const_smul ρ
  have hAj k (v : V) (hv : v.2.2 ∈ Jfreq) :
      ‖iteratedFDeriv ℝ k (normalizedFullAmplitude A ρ) v‖ ≤ D k * L ^ (k-Rreserve) := by
    change ‖iteratedFDeriv ℝ k (ρ • g) v‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
    apply (mul_le_mul_of_nonneg_left (hgj k v hv) hρpos.le).trans_eq
    field_simp [hρpos.ne']
  refine ⟨hA, hAj, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun v : V ↦
      ((normalizedFullAmplitude A ρ) (fullAmplitudePositionSwap v)).conjTranspose)
    exact (Matrix.conjTransposeLinearEquiv (Fin (d+1)) (Fin (d+1)) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp
      (hA.comp fullAmplitudePositionSwap.contDiff)
  · intro k v hv
    rw [norm_jet_normalizedFullAmplitude_exchangedAdjoint]
    exact hAj k (v.2.1,v.1,v.2.2) hv

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
