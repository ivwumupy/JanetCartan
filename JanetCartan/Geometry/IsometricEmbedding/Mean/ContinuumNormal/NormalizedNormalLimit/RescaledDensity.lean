module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.WeightedPrimitive
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.RescaledCutoffs

/-!
# Frequency-uniform comparison with the original density domain

The supported-shell transfer in `CarrierVariation.AmplitudeDifference` needs
the substituted matrix-density difference for every frequency dilation. The
original wider-density comparison supplies the finite calculus before that
dilation. Here the fixed high mask supplies uniform radial norms, so that the
same comparison constant works at every dilation and for every permitted
density on the supplied domain. Neither physical nor density domains change.

This is a deduction from primitive coefficient, conic-inverse, Jacobian and
ODE-footpoint bounds. The normalized-family producers must instantiate those
bounds on the supplied row, including its full detector support. Sources:
`app:ch_background:prop:bg-normalized` and
`app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs.WideDensity

variable {n N : ℕ}

/-- Enlarge only the numerical primitive budget for the frequency-uniform
comparison in `app:ch_background:eq:bg-full-complex-amplitude`. -/
private theorem enlarge_controls
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : PrimitiveNormChart E} {s : ℕ} {M B : ℝ} {f : E → F}
    (hf : D.Controls s M (M + 1) 1 f) (hMB : M ≤ B) :
    D.Controls s B (B + 1) 1 f :=
  ⟨hf.smooth, hf.low.trans hMB, hf.high.trans (by simpa using hMB)⟩

/-- A positive radial norm chart contains every input magnitude in the
supplied compact shell. The fixed mask controls all its dilations there;
the conic domain, masks and scalar domain are unchanged. Consumer: the
weighted shell comparison (`app:ch_background:eq:bg-full-complex-amplitude`). -/
private theorem exists_fixed_high_radial_controls
    {K : Set (InputVariables n)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    (s : ℕ) :
    ∃ E : PrimitiveNormChart ℝ, (∀ p ∈ K, ‖p.2.2‖ ∈ E.carrier) ∧
      ∃ B > 0, ∀ t : ℝ, 1 ≤ t →
        E.Controls (s + 1) B (B + 1) 1 (fun r ↦ h (t * r)) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let radius := 1 + |R| + ε
  let E : PrimitiveNormChart ℝ :=
    ⟨ε / 2 + radius, radius, by dsimp [radius]; positivity,
      univ, isOpen_univ, subset_univ _⟩
  have hradial (r : ℝ) (hr : r ∈ E.carrier) : ε / 2 ≤ r := by
    have := (abs_le.mp (show |r - (ε / 2 + radius)| ≤ radius by
      simpa only [PrimitiveNormChart.carrier, Metric.mem_closedBall, Real.dist_eq] using hr)).1
    linarith
  obtain ⟨A, hA, hjet⟩ := exists_scalarMask_dilation_jet_bound hh htail (half_pos hε) (s + 1)
  let B := ((s + 2 : ℕ) : ℝ) * A
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨E, ?_, B, hB, ?_⟩
  · intro p hp
    have hnorm : ‖p.2.2‖ ≤ R :=
      (norm_snd_le p.2).trans ((norm_snd_le p).trans (hR p hp))
    change ‖p.2.2‖ ∈ Metric.closedBall (ε / 2 + radius) radius
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have := hη p hp
    dsimp [radius]
    constructor <;> linarith [le_abs_self R, abs_nonneg R]
  · intro t ht
    have hb : cNorm E.carrier (s + 1) (fun r ↦ h (t * r)) ≤ B := by
      have hb := cNorm_le_sum_of_bounds (s := E.carrier) (r := s + 1)
        (C := fun _ ↦ A) (fun _ _ ↦ hA.le)
        (fun j hj r hr ↦ hjet t (zero_le_one.trans ht) r (hradial r hr) j hj)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, B] using hb
    exact ⟨(hh.comp (contDiff_const.mul contDiff_id)).contDiffOn,
      (cNorm_mono_order (by omega : 1 ≤ s + 1)).trans hb, by linarith⟩

/-- Uniform frequency-dilated shell comparison for BOTH original density
factors. The scalar domain `L` is supplied unchanged, and the constant precedes
the density, dilation, current coefficients and primitive error. The fixed
high mask has no dilation-dependent finite-norm premise. The only density
reserve is `s + 1 ≤ d₀`, and no smallness of the density is required.

Consumer: the normalized current/frozen full-amplitude comparison through
`s = 2 * (n + 1)`, using
`CarrierVariation.AmplitudeDifference.exists_fullAmplitude_sub_bounds_of_supported_shell`.
Sources: `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`, and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_rescaled_weighted_inputDensity_sub_le
    (D : CoefficientNormCharts n)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (htail : ∀ r, 2 ≤ r → h r = 1)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ContDiffOn ℝ ∞ J₀ W)
    (hgap₀ : ∀ p ∈ K, δ ≤ |J₀ p|)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (hJ₀M : cNorm K s J₀ ≤ M) :
    ∃ C > 0, ∀ (a a₀ : Coefficients n N) (J : InputVariables n → ℝ)
      (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (g g₀ : Bool → Variables n × Euclidean 2 → Euclidean (n - 1) × Euclidean 3)
      (d : ℝ), 0 ≤ d → a.high = h → a₀.high = h →
      D.Controls s M (M + 1) 1 a → D.Controls (s + 1) M (M + 1) 1 a₀ →
      ContDiffOn ℝ ∞ J W → (∀ p ∈ K, δ ≤ |J p|) → cNorm K s J ≤ M →
      ContDiffOn ℝ ∞ u Ω → ContDiffOn ℝ ∞ u₀ Ω →
      MapsTo (inverseCoordinates u) Q K → MapsTo (inverseCoordinates u₀) Q K →
      cNorm Q s (inverseCoordinates u) ≤ M → cNorm Q s (inverseCoordinates u₀) ≤ M →
      (∀ b p, p ∈ Q → ContDiffAt ℝ ∞ (g b) p) →
      (∀ b p, p ∈ Q → ContDiffAt ℝ ∞ (g₀ b) p) →
      (∀ b, MapsTo (g b) Q L) → (∀ b, MapsTo (g₀ b) Q L) →
      (∀ b, cNorm Q s (g b) ≤ M) → (∀ b, cNorm Q s (g₀ b) ≤ M) →
      cNorm D.measurement.carrier s (a.measurement - a₀.measurement) ≤ d →
      cNorm D.angular.carrier s (a.angular - a₀.angular) ≤ d →
      cNorm D.field.carrier s (a.normal - a₀.normal) ≤ d →
      cNorm D.field.carrier s (a.reduced - a₀.reduced) ≤ d →
      cNorm K s (J - J₀) ≤ d →
      cNorm Q s (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      (∀ b, cNorm Q s (g b - g₀ b) ≤ d) →
      ∀ (d₀ : ℕ), s + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      ∀ t : ℝ, 1 ≤ t →
      let b := fun p ↦ densityPair v g p •
        inputDensity (rescaledCoefficients a t) J (inverseCoordinates u p)
      let b₀ := fun p ↦ densityPair v g₀ p •
        inputDensity (rescaledCoefficients a₀ t) J₀ (inverseCoordinates u₀ p)
      cNorm Q s b ≤ C ∧ cNorm Q s b₀ ≤ C ∧ cNorm Q s (b - b₀) ≤ C * d := by
  obtain ⟨E, hE, B, hB, hhigh⟩ := exists_fixed_high_radial_controls hK hε hη hh htail s
  let D' : CoefficientNormCharts n := {D with high := E}
  have hrange' : ∀ p ∈ K, D'.Contains p := by
    intro p hp
    obtain ⟨hm, hm', ha, _, hn, hn'⟩ := hrange p hp
    exact ⟨hm, hm', ha, hE p hp, hn, hn'⟩
  have hMM : M ≤ M + B := le_add_of_nonneg_right hB.le
  obtain ⟨C, hC, hcompare⟩ := exists_weighted_inputDensity_inverse_sub_le_of_primitive_norms
    (N := N) D' hK hW hKW hQ hΩ hQΩ hL hconv hε hδ hη hrange'
      hJ₀ hgap₀ s (add_nonneg hM hB.le) (hJ₀M.trans hMM)
  refine ⟨C, hC, ?_⟩
  intro a a₀ J u u₀ g g₀ d hd hah ha₀h ha ha₀ hJ hgap hJM hu hu₀ huK hu₀K huM hu₀M
    hg hg₀ hgr hgr₀ hgm hgm₀ hm hang hn hq hj hi hgd d₀ horder v hv hvm t ht
  have hhigh' := enlarge_controls (hhigh t ht) (le_add_of_nonneg_left hM)
  have hcurrent : D'.Controls s (M + B) (M + B + 1) 1 (rescaledCoefficients a t) := by
    refine ⟨enlarge_controls ha.measurement hMM, enlarge_controls ha.angular hMM, ?_,
      enlarge_controls ha.normal hMM, enlarge_controls ha.reduced hMM⟩
    rw [show (rescaledCoefficients a t).high = (fun r ↦ h (t * r)) by simp [rescaledCoefficients, hah]]
    refine ⟨hhigh'.smooth, hhigh'.low, ?_⟩
    have hmono := cNorm_mono_order (s := E.carrier) (f := fun r ↦ h (t * r)) (Nat.le_succ s)
    have hbound := hhigh'.high
    change 1 + cNorm E.carrier s (fun r ↦ h (t * r)) ≤ (M + B + 1) * 1
    linarith
  have href : D'.Controls (s + 1) (M + B) (M + B + 1) 1 (rescaledCoefficients a₀ t) := by
    refine ⟨enlarge_controls ha₀.measurement hMM, enlarge_controls ha₀.angular hMM, ?_,
      enlarge_controls ha₀.normal hMM, enlarge_controls ha₀.reduced hMM⟩
    simpa only [rescaledCoefficients, ha₀h] using hhigh'
  have hradial : cNorm E.carrier s
      ((rescaledCoefficients a t).high - (rescaledCoefficients a₀ t).high) ≤ d := by
    simpa only [rescaledCoefficients, hah, ha₀h, sub_self, cNorm_zero] using hd
  have hb := hcompare (rescaledCoefficients a t) (rescaledCoefficients a₀ t)
    J u u₀ g g₀ d hd hcurrent href hJ hgap (hJM.trans hMM) hu hu₀ huK hu₀K
    (huM.trans hMM) (hu₀M.trans hMM) hg hg₀ hgr hgr₀
    (fun b ↦ (hgm b).trans hMM) (fun b ↦ (hgm₀ b).trans hMM)
    hm hang hradial hn hq hj hi hgd d₀ horder v hv hvm
  exact ⟨hb.1, hb.2.1, hb.2.2.1⟩

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
