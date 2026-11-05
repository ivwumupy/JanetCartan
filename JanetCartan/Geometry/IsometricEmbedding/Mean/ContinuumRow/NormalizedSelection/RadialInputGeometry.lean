module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SliceJacobian
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.ConicExtension
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Scaling

/-!
# Full conic input geometry from the selected local buffer

Extend the original input buffer only in frequency. The exact transport
homogeneity gives full-cone regularity and the literal Jacobian scaling,
and the existing radial inverse retains its range in this same domain.
These deductions supply the global input domain of the normalized normal
limit; actual local chart and finite mask selection remain its producers.
-/

open Set Metric Filter
open scoped ContDiff Topology
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormalReduction.TransportSymbol
open ContinuumNormal.CarrierVariation.FamilyInputs
open FullPhaseCharts.ActualComparison CanonicalConic

variable {n : ℕ}

/-- The positive radial extension of the selected open input buffer, retaining
both positions and all carrier labels (`app:ch_background:eq:bg-Psi`). This
is the input domain for `NormalizedNormalLimit`'s full conic inverse range. -/
def radialInputDomain (W : Set (InputVariables n)) : Set (InputVariables n) :=
  {p | ∃ t : ℝ, 0 < t ∧ scaleInput t p ∈ W}

/-- The original selected input buffer lies in its radial extension
(`app:ch_background:eq:bg-Psi`). -/
theorem subset_radialInputDomain (W : Set (InputVariables n)) :
    W ⊆ radialInputDomain W := by
  intro p hp
  exact ⟨1, zero_lt_one, by simpa only [scaleInput, one_smul] using hp⟩

/-- Positive frequency scaling preserves the extended input domain without
changing either physical position or any scalar label (`bg-Psi`). -/
theorem scaleInput_mem_radialInputDomain_iff {W : Set (InputVariables n)}
    {t : ℝ} (ht : 0 < t) (p : InputVariables n) :
    scaleInput t p ∈ radialInputDomain W ↔ p ∈ radialInputDomain W := by
  constructor
  · rintro ⟨s, hs, hp⟩
    exact ⟨s * t, mul_pos hs ht, by simpa only [scaleInput, smul_smul] using hp⟩
  · rintro ⟨s, hs, hp⟩
    refine ⟨s / t, div_pos hs ht, ?_⟩
    simpa only [scaleInput, smul_smul, div_mul_cancel₀ _ ht.ne'] using hp

/-- Radial extension preserves openness of the original input buffer
(`app:ch_background:eq:bg-Psi`). -/
theorem isOpen_radialInputDomain {W : Set (InputVariables n)} (hW : IsOpen W) :
    IsOpen (radialInputDomain W) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨t, ht, hp⟩
  have hc : Continuous (scaleInput (n := n) t) :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_snd.snd.const_smul t))
  exact mem_of_superset ((hW.preimage hc).mem_nhds hp) (fun _ hq ↦ ⟨t, ht, hq⟩)

/-- The whole radial input domain avoids zero frequency whenever the original
selected buffer does; this is `hfreqW` of the source normal limit (`bg-Psi`). -/
theorem frequency_ne_zero_on_radialInputDomain {W : Set (InputVariables n)}
    (hfreq : ∀ p ∈ W, p.2.2 ≠ 0) :
    ∀ p ∈ radialInputDomain W, p.2.2 ≠ 0 := by
  rintro p ⟨t, _, hp⟩ hz
  exact hfreq _ hp (by simp only [scaleInput, hz, smul_zero])

/-- Joint smoothness of the actual augmented transport extends to the whole
radial input domain by its literal homogeneity. No regularity of an arbitrary
extension is used. Consumer: `NormalizedNormalLimit`'s `hjoint` (`bg-Psi`). -/
theorem contDiffOn_augmentedTransport_radialInputDomain
    {Y : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {I : Set ℝ} {W : Set (InputVariables n)} (hI : IsOpen I) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ radialInputDomain W) := by
  rintro ⟨σ, p⟩ ⟨hσ, t, ht, hp⟩
  have hscale : ContDiff ℝ ∞ (fun q : ℝ × InputVariables n ↦ (q.1, scaleInput t q.2)) :=
    contDiff_fst.prodMk (contDiff_snd.fst.prodMk
      (contDiff_snd.snd.fst.prodMk (contDiff_snd.snd.snd.const_smul t)))
  have hlocal : ContDiffAt ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (σ, scaleInput t p) :=
    hf.contDiffAt ((hI.prod hW).mem_nhds ⟨hσ, hp⟩)
  have hh := hlocal.comp (σ, p) hscale.contDiffAt
  have hout : ContDiff ℝ ∞ (fun q : Variables n × Euclidean 2 ↦
      (scaleFrequency t⁻¹ q.1, q.2)) :=
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.const_smul t⁻¹))).prodMk contDiff_snd
  have hresult := hout.contDiffAt.comp (σ, p) hh
  have heq : (fun q : ℝ × InputVariables n ↦
      (scaleFrequency t⁻¹ (augmentedTransportGradient (Y q.1) (scaleInput t q.2)).1,
        (augmentedTransportGradient (Y q.1) (scaleInput t q.2)).2)) =
      (fun q : ℝ × InputVariables n ↦ augmentedTransportGradient (Y q.1) q.2) := by
    funext q
    rw [augmentedTransportGradient_scaleInput]
    simp only [scaleFrequency, inv_smul_smul₀ ht.ne']
  dsimp only [Function.comp_def] at hresult
  rw [heq] at hresult
  exact hresult.contDiffWithinAt

/-- A local positive literal Jacobian remains positive on every radial input,
and is smooth there. These are the full-cone `hglobal` Jacobian conclusions
required by the normalized source comparison (`bg-jacobian`). -/
theorem transportJacobian_radialInputDomain
    (slice : TransportSliceCoordinates n) (hn : 0 < n)
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {W : Set (InputVariables n)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (augmentedTransportGradient Y) W)
    (hJ : ∀ p ∈ W, 0 < transportAbsoluteJacobian slice Y p) :
    (∀ p ∈ radialInputDomain W, 0 < transportAbsoluteJacobian slice Y p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice Y) (radialInputDomain W) ∧
      ∀ p ∈ radialInputDomain W, ∀ t : ℝ, 0 < t →
        transportAbsoluteJacobian slice Y (scaleInput t p) =
          t * transportAbsoluteJacobian slice Y p := by
  have hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient Y q.2) (univ ×ˢ W) :=
    hf.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  have hfull := contDiffOn_augmentedTransport_radialInputDomain
    (Y := fun _ ↦ Y) isOpen_univ hW hjoint
  have hgrad : ContDiffOn ℝ ∞ (transportAveragedGradient Y) (radialInputDomain W) :=
    (hfull.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hp ↦ ⟨mem_univ (0 : ℝ), hp⟩)).fst.snd.snd
  have hscale (p : InputVariables n) (hp : p ∈ radialInputDomain W) (t : ℝ) (ht : 0 < t) :=
    suppliedTransportJacobian_pos_smul slice hn Y (J := transportAbsoluteJacobian slice Y)
      (isOpen_radialInputDomain hW)
      hgrad (fun _ _ ↦ rfl) hp ht ((scaleInput_mem_radialInputDomain_iff ht p).mpr hp)
  have hpos : ∀ p ∈ radialInputDomain W, 0 < transportAbsoluteJacobian slice Y p := by
    intro p hp
    obtain ⟨t, ht, htp⟩ := hp
    have hpositive := hJ _ htp
    rw [hscale p ⟨t, ht, htp⟩ t ht] at hpositive
    exact (mul_pos_iff_of_pos_left ht).mp hpositive
  exact ⟨hpos, (suppliedTransportJacobian_contDiffOn slice Y (J := transportAbsoluteJacobian slice Y)
    (isOpen_radialInputDomain hW) hgrad (fun _ _ ↦ rfl)
    (fun p hp ↦ (hpos p hp).ne')).1, hscale⟩

/-- The explicit radial inverse maps the entire fixed output cone into the
radial extension of its original local input domain. This discharges the
full-cone range without asserting that the uncut frequencies are compact
(`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`). -/
theorem radialExtensionInverse_mapsTo_radialInputDomain
    {b : ℝ} (hb : 0 < b)
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)} {W : Set (InputVariables n)}
    (hrange : MapsTo (inverseCoordinates u) Ω W) :
    MapsTo (inverseCoordinates (radialExtensionInverse b u))
      (normalizedConicTarget b Ω) (radialInputDomain W) := by
  intro q hq
  change scaleInput (‖q.1.2.2‖ / b) (inverseCoordinates u (normalizeOutputRadius b q)) ∈ _
  exact (scaleInput_mem_radialInputDomain_iff
    (div_pos (norm_pos_iff.mpr hq.1) hb) _).mpr
      (subset_radialInputDomain W (hrange hq.2))

end JanetCartan.ContinuumRow.NormalizedSelection
