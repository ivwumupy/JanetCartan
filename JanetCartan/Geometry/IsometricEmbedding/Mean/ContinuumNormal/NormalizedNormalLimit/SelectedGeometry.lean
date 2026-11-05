module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RadialMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.SeedConicGeometry

/-!
# Global comparison geometry from the retained normalized section

The finite incidence producer retains the normalized inverse range and the
normalized image of the entire mask. These imply the full radial inverse
range, punctured closure containment and supported-shell containment on the
same domains. The literal Jacobian extends by transport homogeneity.
-/

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumRow CanonicalConic NormalizedSelection
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase FrozenModel

/-- The normalized image of the WHOLE supplied mask controls its punctured
closure and supported shell on the original common cone. The compact target
and radial target law are retained by finite incidence selection. This proves
the two support obligations in `exists_source_family_controlled_half_gap`
without reducing any detector support
(`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`). -/
theorem transport_mask_closure_geometry_of_normalized_image
    {n : ℕ} {b : ℝ} (hb : 0 < b)
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {Zmask : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hmask : ∀ p ∈ Zmask, normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q) :
    (closure (augmentedTransportGradient Y '' Zmask) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
      ∀ q ∈ closure (augmentedTransportGradient Y '' Zmask), ‖q.1.2.2‖ = b → q ∈ Q := by
  have hnorm (q : Variables n × Euclidean 2)
      (hq : q ∈ closure (augmentedTransportGradient Y '' Zmask)) (hne : q.1.2.2 ≠ 0) :
      normalizeOutputRadius b q ∈ Q := by
    have hm : MapsTo (normalizeOutputRadius b) (augmentedTransportGradient Y '' Zmask) Q := by
      rintro _ ⟨p, hp, rfl⟩
      exact hmask p hp
    have hh := (normalizeOutputRadius_continuousAt b hne).continuousWithinAt.mem_closure hq hm
    exact hQ.isClosed.closure_eq ▸ hh
  constructor
  · intro q hq
    have hh := hQΩ (hnorm q hq.1 hq.2)
    exact (hcone (b / ‖q.1.2.2‖) (div_pos hb (norm_pos_iff.mpr hq.2)) q).mp hh
  · intro q hq hfreq
    have hh := hnorm q hq (norm_pos_iff.mp (hfreq ▸ hb))
    simpa only [normalizeOutputRadius_eq_self hb hfreq] using hh

/-- Discharge the global geometry of the normalized source comparison from
the SAME retained local input buffer and normalized mask images. In
particular, positivity and smoothness of the actual Jacobian are proved on
the entire radial input domain, and both the current and zero-source closed
mask shells lie in the unchanged compact target. The selector supplies the
displayed local range, half-gap/Jacobian and normalized-mask facts; none is a
normal-operator estimate. Consumer: `hglobal` in
`exists_source_family_controlled_half_gap`
(`app:ch_background:prop:bg-normalized`, `bg-Psi`, `bg-jacobian`). -/
theorem source_global_geometry_of_retained_input_buffer
    {n : ℕ} (hn : 0 < n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hW : IsOpen W) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    {sourceCap gap b Cupper : ℝ} (hsourceCap : 0 ≤ sourceCap)
    (hgap : 0 < gap) (hb : 0 < b)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    (Zmask : Set (InputVariables n))
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hlocal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      ContDiffOn ℝ ∞ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) W ∧
      (∀ p ∈ W, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p) ∧
      MapsTo (fun q ↦ inverseCoordinates (u σ) (normalizeOutputRadius b q)) Ω W ∧
      (∀ q ∈ Ω, ‖(u σ q).2‖ ≤ Cupper * ‖q.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
        u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
      (∀ p ∈ Zmask, normalizeOutputRadius b
        (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ) p) ∈ Q)) :
    ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) (radialInputDomain W) ∧
      (∀ p ∈ radialInputDomain W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω (radialInputDomain W) ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ q ∈ Ω, ‖(u σ q).2‖ ≤ Cupper * ‖q.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
        u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) q)) =
          t * J σ (inverseCoordinates (u σ) q)) ∧
      ∀ q : Variables n × Euclidean 2, ‖q.1.2.2‖ = b →
        q ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → q ∈ Q := by
  have hzero := hlocal 0 ⟨le_rfl, hsourceCap⟩
  have hshellZero := (transport_mask_closure_geometry_of_normalized_image
    hb hQ hQΩ hcone hzero.2.2.2.2.2).2
  intro σ hσ Z J
  obtain ⟨hf, hJ, hrange, hupper, hscale, hmask⟩ := hlocal σ hσ
  have hrangeFull := inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range
    hb hne hrange hscale
  obtain ⟨hpos, hJsmooth, hJscale⟩ := transportJacobian_radialInputDomain
    (adaptedSliceCoordinates T) hn hW hf (fun p hp ↦ hgap.trans_le (hJ p hp))
  obtain ⟨hpunctured, hshell⟩ :=
    transport_mask_closure_geometry_of_normalized_image hb hQ hQΩ hcone hmask
  refine ⟨hJsmooth, fun p hp ↦ (hpos p hp).ne', hrangeFull, hpunctured,
    hupper, hscale, fun t ht q hq ↦ hJscale _ (hrangeFull hq) t ht, ?_⟩
  intro q hfreq hq
  exact hq.elim (fun hq ↦ hshell q hq hfreq) (fun hq ↦ hshellZero q hq hfreq)

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
