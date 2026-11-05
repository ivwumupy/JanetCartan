module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support.Inputs

/-!
# Closed image of the original high-frequency support

The retained transverse comparison gives output frequency at least `1/2`.
The punctured buffer therefore puts every image limit in the outer inverse
chart. Continuity of that SAME inverse and closedness of the original input
support recover an original supported preimage, including its phase buffer.

The geometric hypotheses below are outputs of
`CanonicalConic.exists_actual_refined_supported_geometry`; smoothness and the
punctured buffer use its retained outer chart, never a whole-domain shell bound.
Consumer: `exists_scalarTransportCarrierAdjoint_periodic_raw_bound` (`hclosed`,
`himage`) and `PrimitiveJetGeometry.high_frequency`.
Source: `app:ch_background:prop:bg-adjoint`, `bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a aPhase rMask aMask : ℝ}

/-- The inverse frequency in the adjoint coordinates is exactly the retained
canonical inverse frequency (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_inverse_carrier_frequency_eq {aOuter : ℝ} (p : JointVariables n) :
    ((normalChart T Q z₀ ηb r aOuter aPhase).carrier
      ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2 =
      (symbolInverse T Q z₀ ηb r aOuter p).2 := by
  rw [normalChart_carrier_eq, normalChart_pull_eq]
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

variable (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r)
    (hrr : rMask ≤ r) (haa : aMask ≤ a) (hphase : aMask < aPhase)

local notation "g" => normalChart T Q z₀ ηb r (6 * a) aPhase
local notation "J" => normalSupport T z₀ ηb rMask aMask

include hηb hr ha har hrr haa hphase

/-- The transported original support is contained in the ACTUAL restricted
output domain, by its supported preimages (`bg-full-complex-amplitude`). -/
theorem normalSupport_image_subset_outputDomain : (g).push '' J ⊆ (g).outputDomain := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p.1.2.2, normalSupport_subset_inputDomain T Q hηb hr ha har hrr haa hphase hp, rfl⟩

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hInv htrans

/-- The original supported input is recovered without changing the forward
map or inverse (`app:ch_background:eq:bg-Psi`). -/
theorem normalSupport_pull_push {p : JointVariables n} (hp : p ∈ J) :
    (g).pull ((g).push p) = p := by
  have hpD := normalSupport_subset_inputDomain T Q hηb hr ha har hrr haa hphase hp
  change ((p.1.1, p.1.2.1,
    (g).inverse p.1.1 p.1.2.1 p.2 ((g).forward p.1.1 p.1.2.1 p.2 p.1.2.2)), p.2) = p
  rw [normalChart_inverse_forward T Q hηb hr hInv htrans _ _ _ hpD]

/-- The unchanged inverse returns every supported output to the ORIGINAL
support, including the high-frequency cutoff (`bg-full-complex-amplitude`). -/
theorem normalSupport_pull_image : MapsTo (g).pull ((g).push '' J) J := by
  rintro _ ⟨p, hp, rfl⟩
  rwa [normalSupport_pull_push T Q hηb hr ha har hrr haa hphase hInv htrans hp]

/-- The exact high-frequency lower bound for `PrimitiveJetGeometry` follows
from the original support and inverse identity (`bg-full-complex-amplitude`). -/
theorem normalSupport_inverse_high_frequency {p : JointVariables n}
    (hp : p ∈ (g).push '' J) : 1 ≤ ‖((g).carrier ((g).pull p)).2‖ :=
  (normalSupport_pull_image T Q hηb hr ha har hrr haa hphase hInv htrans hp).2

/-- Original frequency at least one and the retained inverse comparison give
an output gap of one half. No output support bound is assumed (`bg-Psi`). -/
theorem normalSupport_image_frequency_lower {p : JointVariables n}
    (hp : p ∈ (g).push '' J) : 1 / 2 ≤ ‖p.1.2.2‖ := by
  have hlow := normalSupport_inverse_high_frequency T Q hηb hr ha har hrr haa hphase hInv htrans hp
  rw [normalChart_inverse_carrier_frequency_eq] at hlow
  have houter := normalChart_outputDomain_subset T Q hηb hr hInv htrans
    (normalSupport_image_subset_outputDomain T Q hηb hr ha har hrr haa hphase hp)
  have hupper := symbolInverse_norm_le_two T Q hηb hr hInv htrans houter
  linarith

variable (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
    (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))

include hf

/-- The closure of the unbounded high-frequency image stays inside the outer
inverse chart. The producer is `conicMaskImage_punctured_buffer`, applied to
the retained outer masks, plus the PROVED output gap (`bg-full-complex-amplitude`). -/
theorem normalSupport_closure_image_subset_symbolDomain :
    closure ((g).push '' J) ⊆ symbolDomain T Q z₀ ηb r (6 * a) := by
  have hsub : (g).push '' J ⊆
      augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
        conicMaskSupport z₀ ηb r a := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨jointInputCoordinates T p, conicMaskSupport_mono z₀ ηb hrr haa hp.1, rfl⟩
  have hgap : closure ((g).push '' J) ⊆ {p : JointVariables n | 1 / 2 ≤ ‖p.1.2.2‖} :=
    closure_minimal (fun _ hp ↦ normalSupport_image_frequency_lower
      T Q hηb hr ha har hrr haa hphase hInv htrans hp)
        (isClosed_le continuous_const continuous_fst.snd.snd.norm)
  intro p hp
  exact conicMaskImage_punctured_buffer T Q hηb hr ha har htrans hf
    ⟨closure_mono hsub hp,
      norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hgap hp))⟩

/-- The high-frequency image is closed even though its radial variable is
unbounded. The continuous retained outer inverse takes every limit back to
the closed ORIGINAL input support (`bg-full-complex-amplitude`). -/
theorem normalSupport_image_isClosed (hV : IsOpen V) (hLV : L ⊆ V) :
    IsClosed ((g).push '' J) := by
  apply isClosed_of_closure_subset
  intro p hp
  have houter := normalSupport_closure_image_subset_symbolDomain
    T Q hηb hr ha har hrr haa hphase hInv htrans hf hp
  have hi : ContinuousAt (g).pull p := by
    rw [normalChart_pull_eq]
    exact (jointInputCoordinates T).symm.continuous.continuousAt.comp
      ((inverseCoordinates_contDiffOn
        (symbolInverse_smooth T Q hηb hr hInv htrans hLV)).continuousOn.continuousAt
          ((symbolDomain_open T Q hηb hr hInv htrans hV hLV).mem_nhds houter))
  have hpre : (g).pull p ∈ J := (normalSupport_isClosed T).closure_eq ▸
    hi.continuousWithinAt.mem_closure hp
      (normalSupport_pull_image T Q hηb hr ha har hrr haa hphase hInv htrans)
  refine ⟨(g).pull p, hpre, ?_⟩
  rw [normalChart_push_eq, normalChart_pull_eq]
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact augmentedTransportGradient_symbolInverse T Q hηb hr hInv htrans houter

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
