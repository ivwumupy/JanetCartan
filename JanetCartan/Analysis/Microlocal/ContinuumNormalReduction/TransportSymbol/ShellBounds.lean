module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Coefficient
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Integration
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Primitives
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.InitialMultiplier

/-!
# One-high normalized-shell transport density bounds

The consumer is `jc-continuum-transport-symbol`. These implications do not
construct the inverse: `jc-continuum-transport-inverse-jets` supplies its jets
and the Jacobian jets. All constants precede the varying fields. H is a single
common primitive high norm at order s plus one fixed producer shift; none of
the operations here increase that shift.

Sources: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-mixed-input`, and
`app:ch_regular_base:eq:joint-primitive-product`.
-/

@[expose] public noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
open FourierIntegral.NormalOneHigh
variable {n N : ℕ}

/-- One-high joint jets of the literal density after the genuine inverse
substitution. Only primitive evaluation-array jets and inverse jets are inputs;
there is no density-jet hypothesis. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_substitutedDensity_oneHigh_bound (s : ℕ) (hs : 2 ≤ s)
    (M : ℝ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C > 0, ∀ (c : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (Ω : Set (Variables n × Euclidean 2)) (W : Set (InputVariables n)) (H : ℝ),
      1 ≤ H → IsOpen Ω → IsOpen W →
      ContDiffOn ℝ ∞ (inverseCoordinates u) Ω →
      MapsTo (inverseCoordinates u) Ω W →
      ContDiffOn ℝ ∞ (shellPrimitiveValues c J) W →
      (∀ p ∈ W, δ ≤ |J p|) → (∀ p ∈ W, ε ≤ ‖p.2.2‖) →
      (∀ p ∈ W, ‖shellPrimitiveValues c J p‖ ≤ M) →
      (∀ p ∈ W, ∀ i, 1 ≤ i → i ≤ s →
        ‖iteratedFDeriv ℝ i (shellPrimitiveValues c J) p‖ ≤
          a i * H ^ (((i : ℝ) - 1) / (s - 1))) →
      (∀ p ∈ Ω, ∀ i, 1 ≤ i → i ≤ s →
        ‖iteratedFDeriv ℝ i (inverseCoordinates u) p‖ ≤
          b i * H ^ (((i : ℝ) - 1) / (s - 1))) →
      ∀ p ∈ Ω, ∀ k ≤ s,
        ‖iteratedFDeriv ℝ k (inputDensity c J ∘ inverseCoordinates u) p‖ ≤ C * H := by
  obtain ⟨R, hR, hbound⟩ := exists_shellDensityCoefficient_jet_bound
    (n := n) (N := N) s M hδ hε
  let c := compositionBudget (fun _ ↦ R) a
  let d := compositionBudget c b
  have hc : ∀ i, 0 ≤ c i := compositionBudget_nonneg (fun _ ↦ hR.le) ha
  have hd : ∀ i, 0 ≤ d i := compositionBudget_nonneg hc hb
  let C := R + ∑ i ∈ Finset.range (s + 1), d i
  have hRC : R ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hd i))
  refine ⟨C, hR.trans_le hRC, ?_⟩
  intro A J u Ω W H hH hΩ hW hu hmap hinput hgap hη hzero hjet hinv p hp k hk
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hspos : (0 : ℝ) < s - 1 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hcoeff (z) (hz : z ∈ W) :
      ContDiffAt ℝ ∞ (@shellDensityCoefficient n N) (shellPrimitiveValues A J z) :=
    shellDensityCoefficient_contDiffAt (abs_pos.mp (hδ.trans_le (hgap z hz)))
      (norm_pos_iff.mp (hε.trans_le (hη z hz)))
  have hfirst (z) (hz : z ∈ W) (i : ℕ) (hi : 1 ≤ i) (his : i ≤ s) :
      ‖iteratedFDeriv ℝ i (inputDensity A J) z‖ ≤
        c i * H ^ (((i : ℝ) - 1) / (s - 1)) := by
    rw [inputDensity_eq_shellDensityCoefficient]
    apply norm_iteratedFDeriv_comp_le_profile
      (hinput.contDiffAt (hW.mem_nhds hz)) (hcoeff z hz) hi his hHpos
      (fun _ ↦ R) a (fun _ ↦ hR.le)
    · intro j hj hjs
      apply (hbound _ (hzero z hz) (hgap z hz) (hη z hz) j hjs).trans
      apply le_mul_of_one_le_right hR.le
      apply Real.one_le_rpow hH
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hj)) hspos.le
    · exact hjet z hz
  by_cases hk0 : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero, Function.comp_apply,
      inputDensity_eq_shellDensityCoefficient]
    exact (show ‖shellDensityCoefficient (shellPrimitiveValues A J
      (inverseCoordinates u p))‖ ≤ R by
        simpa using hbound _ (hzero _ (hmap hp)) (hgap _ (hmap hp))
          (hη _ (hmap hp)) 0 (Nat.zero_le s)).trans
      (hRC.trans (le_mul_of_one_le_right (hR.le.trans hRC) hH))
  · have hcomp := norm_iteratedFDeriv_comp_le_profile
      (hu.contDiffAt (hΩ.mem_nhds hp))
      (show ContDiffAt ℝ ∞ (inputDensity A J) (inverseCoordinates u p) from
        (hcoeff _ (hmap hp)).comp _ (hinput.contDiffAt (hW.mem_nhds (hmap hp))))
      (show 1 ≤ k by omega) hk hHpos c b hc
      (hfirst _ (hmap hp)) (hinv p hp)
    apply hcomp.trans
    have hdC : d k ≤ C := by
      have := Finset.single_le_sum (fun i _ ↦ hd i)
        (Finset.mem_range.mpr (by omega : k < s + 1))
      dsimp [C]
      linarith
    have hp : H ^ (((k : ℝ) - 1) / (s - 1)) ≤ H := by
      calc
        _ ≤ H ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH
          ((div_le_one hspos).mpr (sub_le_sub_right (by exact_mod_cast hk) 1))
        _ = H := Real.rpow_one H
    exact mul_le_mul hdC hp (Real.rpow_nonneg hHpos.le _) (hR.le.trans hRC)

/-- Inside the chart, zero extension preserves every jet of the actual
substituted density. Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem iteratedFDeriv_extendedDensity_eq (a : Coefficients n N)
    (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    {Ω : Set (Variables n × Euclidean 2)} (hΩ : IsOpen Ω)
    {p : Variables n × Euclidean 2} (hp : p ∈ Ω) (k : ℕ) :
    iteratedFDeriv ℝ k (extendedDensity a J u Ω) p =
      iteratedFDeriv ℝ k (inputDensity a J ∘ inverseCoordinates u) p := by
  have he : extendedDensity a J u Ω =ᶠ[𝓝 p] inputDensity a J ∘ inverseCoordinates u := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact indicator_of_mem hq _
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

/-- Buffered primitive evaluation-array norms give one-high bounds for the
literal zero extension and compact spectator amplitude. The same s is used for
both primitive inputs and the genuine inverse coordinates; thus the producer's
fixed derivative shift is preserved. Source:
`app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_regular_base:eq:joint-primitive-product`.

The normalized-shell application restricts W and Ω to the indicated fixed
working balls. No bound on inputDensity, extendedDensity, or amplitude is an
input to this theorem. The parent must supply the primitive array bounds. -/
theorem exists_amplitude_oneHigh_bound_of_primitiveArray_cNorm
    (s : ℕ) (hs : 2 ≤ s) (x : InputVariables n) (y : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {U : Set (InputVariables n)} {V : Set (Variables n × Euclidean 2)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hx : Metric.closedBall x ρ ⊆ U) (hy : Metric.closedBall y τ ⊆ V)
    {M L T δ ε : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hT : 1 ≤ T)
    (hδ : 0 < δ) (hε : 0 < ε)
    {K : Set (Euclidean 2)} (hK : IsCompact K) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (F : InputVariables n → Variables n × Euclidean 2)
      (Ω : Set (Variables n × Euclidean 2)) (W P : Set (InputVariables n)) (H : ℝ),
      1 ≤ H → IsOpen Ω → IsOpen W →
      W ⊆ Metric.closedBall x ρ → Ω ⊆ Metric.closedBall y τ →
      PrimitiveRegularity a J W → ContDiffOn ℝ ∞ u Ω →
      ContDiffOn ℝ ∞ (shellPrimitiveValues a J) U →
      ContDiffOn ℝ ∞ (inverseCoordinates u) V →
      MapsTo (inverseCoordinates u) Ω W →
      (∀ p ∈ W, δ ≤ |J p|) → (∀ p ∈ W, ε ≤ ‖p.2.2‖) →
      cNorm (Metric.closedBall x ρ) 1 (shellPrimitiveValues a J) ≤ M →
      cNorm (Metric.closedBall y τ) 1 (inverseCoordinates u) ≤ L →
      1 + cNorm (Metric.closedBall x ρ) s (shellPrimitiveValues a J) ≤ T * H →
      1 + cNorm (Metric.closedBall y τ) s (inverseCoordinates u) ≤ T * H →
      (∀ p ∈ Ω, F (inverseCoordinates u p) = p) →
      (∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
        a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ P) →
      IsClosed (F '' P) → F '' P ⊆ Ω →
      (∀ p, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (extendedDensity a J u Ω) p‖ ≤ C * H) ∧
      (∀ p, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p‖ ≤ C * H) := by
  obtain ⟨a, ha, hpa⟩ := exists_primitiveJet_profile_closedBall
    (F := ShellPrimitiveValues n N) x hρ hU hx hs hM hT
  obtain ⟨b, hb, hpb⟩ := exists_primitiveJet_profile_closedBall
    (F := InputVariables n) y hτ hV hy hs hL hT
  obtain ⟨C, hC, hbound⟩ := exists_substitutedDensity_oneHigh_bound
    (n := n) (N := N) s hs M (fun _ ↦ a) (fun _ ↦ b)
    (fun _ ↦ zero_le_one.trans ha) (fun _ ↦ zero_le_one.trans hb) hδ hε
  refine ⟨C * (1 + volume.real K), mul_pos hC (by positivity), ?_⟩
  intro A J u F Ω W P H hH hΩ hW hWx hΩy hreg hu hinput hinv hmap
    hgap hη hlow hlowu hhigh hhighu hright hsupp hclosed hbuffer
  obtain ⟨hzero, hjet⟩ := hpa _ H hinput hH hlow hhigh
  obtain ⟨_, hju⟩ := hpb _ H hinv hH hlowu hhighu
  have hchart := hbound A J u Ω W H hH hΩ hW
    (hinv.mono (hΩy.trans hy)) hmap (hinput.mono (hWx.trans hx)) hgap hη
    (fun p hp ↦ hzero p (hWx hp))
    (fun p hp ↦ hjet p (hWx hp)) (fun p hp ↦ hju p (hΩy hp))
  have hext (p) (k : ℕ) (hk : k ≤ s) :
      ‖iteratedFDeriv ℝ k (extendedDensity A J u Ω) p‖ ≤ C * H := by
    by_cases hp : p ∈ Ω
    · rw [iteratedFDeriv_extendedDensity_eq A J u hΩ hp k]
      exact hchart p hp k hk
    · rw [iteratedFDeriv_extendedDensity_eq_zero A J u F
        hmap hright hsupp hclosed hbuffer hp k, norm_zero]
      exact mul_nonneg hC.le (zero_le_one.trans hH)
  have hCH : 0 ≤ C * H := mul_nonneg hC.le (zero_le_one.trans hH)
  constructor
  · intro p k hk
    apply (hext p k hk).trans
    nlinarith [measureReal_nonneg (μ := volume) (s := K)]
  · intro p k hk
    have hf := extendedDensity_contDiff A J u F hΩ hreg hu hmap hright hsupp hclosed hbuffer
    have hh := norm_iteratedFDeriv_spectatorIntegral_le hf hK k p
      (fun v _ ↦ hext (p, v) k hk)
    apply hh.trans
    nlinarith [measureReal_nonneg (μ := volume) (s := K)]

/-- Pointwise shell estimate from individual primitive profiles and genuine u
jets. Both shells and constants are fixed before the fields vary. The profiles
are supplied by `exists_shellJetProfile_of_cNorm`; J and u are supplied by
`jc-continuum-transport-inverse-jets`. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_substitutedDensity_bound_of_primitives
    (s : ℕ) (hs : 2 ≤ s) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    {P : Set (InputVariables n)} {Q : Set (Variables n × Euclidean 2)}
    (hP : IsCompact P) (hQ : IsCompact Q) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hη : ∀ p ∈ P, ε ≤ ‖p.2.2‖) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (H : ℝ),
      1 ≤ H → ∀ p ∈ Q, inverseCoordinates u p ∈ P →
      δ ≤ |J (inverseCoordinates u p)| →
      PrimitiveShellProfiles s H M a J (inverseCoordinates u p) →
      ShellJetProfile s H L u p → ∀ k ≤ s,
      ‖iteratedFDeriv ℝ k (inputDensity a J ∘ inverseCoordinates u) p‖ ≤ C * H := by
  obtain ⟨A, hA, hprim⟩ := exists_shellPrimitiveValues_profile (N := N) s hs hM hP
    (fun p hp ↦ norm_pos_iff.mp (hε.trans_le (hη p hp)))
  obtain ⟨B, hB, hinv⟩ := exists_inverseCoordinates_profile s hs hL hQ
  obtain ⟨R, hR, hcoeff⟩ := exists_shellDensityCoefficient_jet_bound
    (n := n) (N := N) s A hδ hε
  let D := R + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ R) (fun _ ↦ A) i
  have hD : 0 < D := hR.trans_le (le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i _ ↦ compositionBudget_nonneg (fun _ ↦ hR.le) (fun _ ↦ hA.le) i)))
  let C := D + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ D) (fun _ ↦ B) i
  have hC : 0 < C := hD.trans_le (le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i _ ↦ compositionBudget_nonneg (fun _ ↦ hD.le) (fun _ ↦ hB.le) i)))
  refine ⟨C, hC, ?_⟩
  intro a J u H hH p hp hpu hgap hpr hu k hk
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have harray := hprim a J H hH _ hpu hpr
  have hcoord := hinv u H hH p hp hu
  have hop : ShellJetProfile s H R (@shellDensityCoefficient n N)
      (shellPrimitiveValues a J (inverseCoordinates u p)) := by
    refine ⟨shellDensityCoefficient_contDiffAt (abs_pos.mp (hδ.trans_le hgap))
      (norm_pos_iff.mp (hε.trans_le (hη _ hpu))), ?_, ?_⟩
    · simpa using hcoeff _ harray.value hgap (hη _ hpu) 0 (Nat.zero_le s)
    · intro i hi his
      apply (hcoeff _ harray.value hgap (hη _ hpu) i his).trans
      apply le_mul_of_one_le_right hR.le (Real.one_le_rpow hH ?_)
      apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast hi))
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
  have hfirst := hop.comp (f := shellPrimitiveValues a J)
    (x := inverseCoordinates u p) harray hR.le hA.le hHpos
  have hsecond := hfirst.comp (f := inverseCoordinates u) (x := p)
    hcoord hD.le hB.le hHpos
  exact hsecond.bound hC.le hH hs k hk

/-- Finite mixed shell jets of the actual compact spectator amplitude, from
individual primitive profiles. Quantitative assumptions are needed only where
(X × K) meets the inverse chart; the chart may itself be unbounded. Primitive
regularity and support buffers supply all extension and integration facts.
Source: `app:ch_background:eq:bg-full-complex-amplitude`.

This is conditional on actual J/u profiles and identities. The parent task
must instantiate those inputs and insert its common norm H at one fixed shift.
It is not an unconditional construction of the transport symbol. -/
theorem exists_amplitude_shell_bound_of_primitives
    (s : ℕ) (hs : 2 ≤ s) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    {P : Set (InputVariables n)} {Q : Set (Variables n × Euclidean 2)}
    (hP : IsCompact P) (hQ : IsCompact Q) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hη : ∀ p ∈ P, ε ≤ ‖p.2.2‖)
    {K : Set (Euclidean 2)} (hK : IsCompact K) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (F : InputVariables n → Variables n × Euclidean 2)
      (Ω : Set (Variables n × Euclidean 2)) (W Z : Set (InputVariables n))
      (X : Set (Variables n)) (H : ℝ),
      1 ≤ H → IsOpen Ω → PrimitiveRegularity a J W → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Ω W →
      (∀ p ∈ Ω, F (inverseCoordinates u p) = p) →
      (∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
        a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z) →
      IsClosed (F '' Z) → F '' Z ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ K, (x, v) ∈ Ω → (x, v) ∈ Q ∧ inverseCoordinates u (x, v) ∈ P) →
      (∀ p ∈ P, δ ≤ |J p|) →
      (∀ p ∈ P, PrimitiveShellProfiles s H M a J p) →
      (∀ p ∈ Q, ShellJetProfile s H L u p) →
      ∀ x ∈ X, ∀ k ≤ s,
        ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) x‖ ≤ C * H := by
  obtain ⟨C, hC, hb⟩ := exists_substitutedDensity_bound_of_primitives
    (N := N) s hs hM hL hP hQ hδ hε hη
  refine ⟨C * (1 + volume.real K), mul_pos hC (by positivity), ?_⟩
  intro a J u F Ω W Z X H hH hΩ hreg hu hmap hright hsupp hclosed hbuffer
    hshell hgap hpr hinv x hx k hk
  have hf := extendedDensity_contDiff a J u F hΩ hreg hu hmap hright hsupp hclosed hbuffer
  have hj (v) (hv : v ∈ K) :
      ‖iteratedFDeriv ℝ k (extendedDensity a J u Ω) (x, v)‖ ≤ C * H := by
    by_cases hp : (x, v) ∈ Ω
    · obtain ⟨hq, hpu⟩ := hshell x hx v hv hp
      rw [iteratedFDeriv_extendedDensity_eq a J u hΩ hp k]
      exact hb a J u H hH _ hq hpu (hgap _ hpu) (hpr _ hpu) (hinv _ hq) k hk
    · rw [iteratedFDeriv_extendedDensity_eq_zero a J u F hmap hright hsupp
        hclosed hbuffer hp k, norm_zero]
      exact mul_nonneg hC.le (zero_le_one.trans hH)
  apply (norm_iteratedFDeriv_spectatorIntegral_le hf hK k x hj).trans
  have hCH : 0 ≤ C * H := mul_nonneg hC.le (zero_le_one.trans hH)
  nlinarith [measureReal_nonneg (μ := volume) (s := K)]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
