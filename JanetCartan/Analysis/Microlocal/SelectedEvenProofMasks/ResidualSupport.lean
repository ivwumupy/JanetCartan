module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.ResidualCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets

/-!
# Closed support of the differentiated direct residual

Use the bounded dilation or zero-jet alternative for the actual common-mask
`PW₁`. Projecting a compact set of dilations gives a single compact support
before the frequency, coefficient, shell, orientation or output order varies.
The dilated covector is only a witness: the integral and both proof masks
are evaluated at their original arguments.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral EvolutionIntegratedLocalization
open FiniteChain.Graph

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E

/-- The supported part of the selected comparable carrier. Its bounded
dilation preserves both times and the physical chart position; the section
radius after dilation is exactly the lower retained radius of the actual
`PW₁` jet producer (`app:ch_regular:eq:chain-tail`). -/
def retainedResidualJetCarrier (K : Set V) (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) (ε ra rb tlo thi : ℝ) : Set V :=
  {v | v ∈ K ∧ ∃ t ∈ Icc tlo thi,
    ℓ (t • spatialPart v.2.2.1) = ra ∧
      ((elapsedJointCoordinates v).1, t • spatialPart v.2.2.1) ∈ bufferedJetSet ℓ z ε ra rb}

/-- Closedness on the original compact joint carrier includes all limiting
amplitude and frequency shoulders (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_retainedResidualJetCarrier {K : Set V} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d)) (ε ra rb tlo thi : ℝ) :
    IsCompact (retainedResidualJetCarrier K ℓ z ε ra rb tlo thi) := by
  let η : V × ℝ → Euclidean d := fun w ↦ w.2 • spatialPart w.1.2.2.1
  have hη : Continuous η :=
    continuous_snd.smul (spatialPartCLM.continuous.comp continuous_fst.snd.snd.fst)
  let B : Set (V × ℝ) := {w | ℓ (η w) = ra ∧
    ((elapsedJointCoordinates w.1).1, η w) ∈ bufferedJetSet ℓ z ε ra rb}
  have hB : IsClosed B := (isClosed_eq (ℓ.continuous.comp hη) continuous_const).inter
    ((isCompact_bufferedJetSet ℓ z ε ra rb).isClosed.preimage
      (((elapsedJointCoordinates.continuous.comp continuous_fst).fst).prodMk hη))
  convert ((hK.prod (isCompact_Icc (a := tlo) (b := thi))).inter_right hB).image
    continuous_fst using 1
  ext v
  constructor
  · rintro ⟨hv, t, ht, he, hb⟩
    exact ⟨(v, t), ⟨⟨hv, ht⟩, he, hb⟩, rfl⟩
  · rintro ⟨⟨v, t⟩, ⟨⟨hv, ht⟩, he, hb⟩, rfl⟩
    exact ⟨hv, t, ht, he, hb⟩

/-- Recover the *undilated* section radius from the retained bounded
dilation. These are the radii needed for a gap at the original graph
covector; no radial action on the input or output mask is used
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem section_mem_Icc_of_retainedResidualJetCarrier
    {K : Set V} {ℓ : Euclidean d →L[ℝ] ℝ} {z : RootState (Euclidean d)}
    {ε ra rb tlo thi : ℝ} (hlo : 0 < tlo) (ha : 0 < ra)
    {v : V} (hv : v ∈ retainedResidualJetCarrier K ℓ z ε ra rb tlo thi) :
    ℓ (spatialPart v.2.2.1) ∈ Icc (ra / thi) (ra / tlo) := by
  obtain ⟨_, t, ht, he, _⟩ := hv
  rw [map_smul, smul_eq_mul] at he
  have ht' := hlo.trans_le ht.1
  have hr : 0 < ℓ (spatialPart v.2.2.1) := pos_of_mul_pos_right (he ▸ ha) ht'.le
  constructor
  · apply (div_le_iff₀ (ht'.trans_le ht.2)).mpr
    rw [← he, mul_comm t]
    exact mul_le_mul_of_nonneg_left ht.2 hr.le
  · apply (le_div_iff₀ hlo).mpr
    rw [← he, mul_comm t]
    exact mul_le_mul_of_nonneg_left ht.1 hr.le

/-- Restrict the literal output-independent amplitude in `PrimitiveIntegrated.hs`
to the compact radial-witness carrier. The last two inputs are respectively
the support and jet alternative of `exists_selected_direct_residual_carriers`.
The order-zero case is sufficient *before* taking closed support, so flat
points of the residual are not discarded. Both literal orientations and
every multiplier factor remain (`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_cut_jointElapsedAmplitude_subset_retainedResidualJetCarrier
    {K : Set V} (hK : IsCompact K) (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) (ε ra rb tlo thi : ℝ)
    (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d+1))
    (χA χo : E → ℝ) (θ : ℝ → ℂ) (x y : E)
    (hs : tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
      χout χsource β mi mo χA χo x y v) ⊆ K)
    (hdilate : ∀ v ∈ K,
      let t := ra / ℓ (spatialPart v.2.2.1)
      t ∈ Icc tlo thi ∧ ℓ (t • spatialPart v.2.2.1) = ra ∧
        (((elapsedJointCoordinates v).1, t • spatialPart v.2.2.1) ∈ bufferedJetSet ℓ z ε ra rb ∨
          iteratedFDeriv ℝ 0 (normalizedElapsedSymbol ρ b) v = 0)) :
    tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
      χout χsource β mi mo χA χo x y v) ⊆ retainedResidualJetCarrier K ℓ z ε ra rb tlo thi := by
  apply closure_minimal _ (isCompact_retainedResidualJetCarrier hK ℓ z ε ra rb tlo thi).isClosed
  intro v hv
  have hK' := hs (subset_tsupport _ hv)
  obtain ⟨ht, he, hband | hz⟩ := hdilate v hK'
  · exact ⟨hK', _, ht, he, hband⟩
  · have hb : normalizedElapsedSymbol ρ b v = 0 := norm_eq_zero.mp
      (by simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm hz)
    change b _ _ _ _ = 0 at hb
    rw [SymbolBudgets.spatialPart_smul] at hb
    exfalso
    apply hv
    cases backward <;> simp [jointElapsedAmplitude, jointAmplitude, orientedElapsedAmplitude,
      elapsedAmplitude, hb]

/-- Equality of the *masked* elapsed amplitudes before taking adjoints gives
equality of the entire demodulated output jets. The phases may be the two
supported representatives: their output oscillations cancel in the exact jet
formula. This identifies the auxiliary `PW₁` jets with the literal original
ones without differentiating a pointwise equality on a nonopen carrier
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem cutElapsedOutputJetAmplitude_eq_of_elapsedAmplitude_eq
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ Ψ' : TwoTimePhase d)
    (b b' : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (heq : ∀ r, elapsedAmplitude b χout χsource β r = elapsedAmplitude b' χout χsource β r)
    (mi mo : LocalizerSymbol (d+1)) (χA χo : E → ℝ) (θ : ℝ → ℂ) (x y : E)
    (ho : ContDiff ℝ ∞ mo) (m : ℕ) (v : Fin m → E) :
    cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v =
      cutElapsedOutputJetAmplitude backward ρ Ψ' b' χout χsource β mi mo χA χo θ x y m v := by
  funext w
  rw [cutElapsedOutputJetAmplitude_eq_scaled_symbolJet backward hρ Ψ b _ _ _ mi mo _ _ θ x y ho,
    cutElapsedOutputJetAmplitude_eq_scaled_symbolJet backward hρ Ψ' b' _ _ _ mi mo _ _ θ x y ho]
  simp only [jointElapsedAmplitude, orientedElapsedAmplitude, heq]

/-- Every joint derivative of every literal output jet stays in the same
retained carrier and the original closed input and output-complement supports.
This includes the identity part of `1-mo` and conjugate transpose in the
reverse integral (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem tsupport_iteratedFDeriv_cutElapsedOutputJetAmplitude_subset_retained
    {K : Set V} (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d+1))
    (χA χo : E → ℝ) (θ : ℝ → ℂ) (x y : E) (ho : ContDiff ℝ ∞ mo)
    (hs : tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
      χout χsource β mi (fun _ ↦ 0) χA χo 0 y v) ⊆ K)
    (m : ℕ) (v : Fin m → E) (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β
      mi mo χA χo θ x y m v)) ⊆
      elapsedOutputJetCarrier K mi mo x y :=
  (tsupport_iteratedFDeriv_subset j).trans
    (tsupport_cutElapsedOutputJetAmplitude_subset_bufferedCarrier backward hρ Ψ b χout χsource β
      mi mo χA χo θ x y ho hs m v)

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
