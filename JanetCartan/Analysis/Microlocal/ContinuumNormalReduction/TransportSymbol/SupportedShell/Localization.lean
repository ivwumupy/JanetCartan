module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.RelativeShell

/-!
# Density jets on the transported original mask support

For `app:ch_background:eq:bg-full-complex-amplitude` and `bg-frame`, Step 1,
primitive mask support gives vanishing of every density jet outside the closed
transported support. The spectator estimate therefore requires quantitative
shell containment only on that support. Its consumer is
`exists_transportAmplitude_supported_shell_bound`; the original spectator
measure and global amplitude are retained.
-/

@[expose] public noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Every jet of the literal extended density is supported in the closure of
the transported primitive masks. This supplies the off-support case of
`exists_amplitude_shell_bound_of_supported_buffer`, without derivative-support
assumptions. Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem tsupport_iteratedFDeriv_extendedDensity_subset_closure_image
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j (extendedDensity a J u Ω)) ⊆ closure (F '' Z) :=
  (tsupport_iteratedFDeriv_subset j).trans
    (closure_mono (support_extendedDensity_subset a J u F hmap hright hs))

/-- All extended-density jets vanish off the closed transported original
support, including at points inside the inverse chart. The conclusion uses
only the primitive masks and the inverse identity, and applies to homogeneous,
high-cutoff and regularized densities alike. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem iteratedFDeriv_extendedDensity_eq_zero_off_closure_image
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    {p : Variables n × Euclidean 2} (hp : p ∉ closure (F '' Z)) (j : ℕ) :
    iteratedFDeriv ℝ j (extendedDensity a J u Ω) p = 0 := by
  have he := notMem_tsupport_iff_eventuallyEq.mp
    (fun h ↦ hp (closure_mono (support_extendedDensity_subset a J u F hmap hright hs) h))
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- The literal shell estimate with containment only on the closed transported
original support and a relative chart buffer. The working set
`X` lies in an open region `R`, which can be the punctured frequency space.
All inverse/Jacobian profiles are still explicit at this intermediate stage;
`exists_transportAmplitude_supported_shell_bound` discharges them from primitive `Y`
bounds. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_amplitude_shell_bound_of_supported_buffer
    (s : ℕ) (hs : 2 ≤ s) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    {P : Set (InputVariables n)} {Q : Set (Variables n × Euclidean 2)}
    (hP : IsCompact P) (hQ : IsCompact Q) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hη : ∀ p ∈ P, ε ≤ ‖p.2.2‖)
    {K : Set (Euclidean 2)} (hK : IsCompact K) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (F : InputVariables n → Variables n × Euclidean 2)
      (Ω : Set (Variables n × Euclidean 2)) (W Z : Set (InputVariables n))
      (X R : Set (Variables n)) (H : ℝ),
      1 ≤ H → IsOpen Ω → PrimitiveRegularity a J W → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Ω W →
      (∀ p ∈ Ω, F (inverseCoordinates u p) = p) →
      (∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
        a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R → closure (F '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ K, (x, v) ∈ closure (F '' Z) → (x, v) ∈ Q ∧ inverseCoordinates u (x, v) ∈ P) →
      (∀ p ∈ P, δ ≤ |J p|) →
      (∀ p ∈ P, PrimitiveShellProfiles s H M a J p) →
      (∀ p ∈ Q, ShellJetProfile s H L u p) →
      ∀ x ∈ X, ∀ k ≤ s,
        ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) x‖ ≤ C * H := by
  obtain ⟨C, hC, hb⟩ := exists_substitutedDensity_bound_of_primitives
    (N := N) s hs hM hL hP hQ hδ hε hη
  refine ⟨C * (1 + volume.real K), mul_pos hC (by positivity), ?_⟩
  intro a J u F Ω W Z X R H hH hΩ hreg hu hmap hright hsupp hR hXR hbuffer
    hshell hgap hpr hinv x hx k hk
  have hf := extendedDensity_contDiffOn_of_relative_buffer a J u F hΩ hreg hu hmap hright hsupp hbuffer
  have hj (v) (hv : v ∈ K) :
      ‖iteratedFDeriv ℝ k (extendedDensity a J u Ω) (x, v)‖ ≤ C * H := by
    by_cases hp : (x, v) ∈ closure (F '' Z)
    · obtain ⟨hq, hpu⟩ := hshell x hx v hv hp
      have hpΩ : (x, v) ∈ Ω := hbuffer ⟨hp, hXR hx, mem_univ v⟩
      rw [iteratedFDeriv_extendedDensity_eq a J u hΩ hpΩ k]
      exact hb a J u H hH _ hq hpu (hgap _ hpu) (hpr _ hpu) (hinv _ hq) k hk
    · rw [iteratedFDeriv_extendedDensity_eq_zero_off_closure_image a J u F
        hmap hright hsupp hp k, norm_zero]
      exact mul_nonneg hC.le (zero_le_one.trans hH)
  apply (norm_iteratedFDeriv_spectatorIntegral_on_le hR hf hK k (hXR hx) hj).trans
  have hCH : 0 ≤ C * H := mul_nonneg hC.le (zero_le_one.trans hH)
  nlinarith [measureReal_nonneg (μ := volume) (s := K)]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
