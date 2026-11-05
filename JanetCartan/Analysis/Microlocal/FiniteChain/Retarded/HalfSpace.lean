module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Collar

/-!
# Quantitative half-space integration by parts

The half-space argument in `app:ch_regular:lem:finite-chain`, “A common
kernel estimate” and “Retarded and signed factors”. A fixed smooth collar
partition splits the amplitude into a tangentially nonstationary boundary
part and a fully nonstationary interior part. Joint derivative bounds give
`C_q L^b (L/R)^q`, with `b` fixed independently of `q`, as required by
`app:ch_regular:eq:chain-tail`.

The tangential proof includes slice integrability and Fubini; the interior
proof includes a smooth extension across a vanishing collar. Reciprocal
coefficients and transpose bounds come from the localization API. No
boundary jump is differentiated and no time frequency is inverted.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The common constant in the half-space version of
`app:ch_regular:eq:chain-tail`. It depends only on the common compact set,
directions, gaps and derivative profiles, and is independent of the phase,
amplitude, frequency, derivative scale and amplitude offset. -/
def collarDecayConstant (μ : Measure E) (K : Set (ℝ × E))
    (eT : ι → E) (eI : κ → ℝ × E) (δT δI GT GI : ℝ)
    (P H A : ℕ → ℝ) (q : ℕ) : ℝ :=
  decayConstant eT δT GT P (collarAmplitudeProfile H A) q *
      volume.real (Prod.fst '' K) * μ.real (Prod.snd '' K) +
    decayConstant eI δI GI P (collarAmplitudeProfile H A) q * (volume.prod μ).real K

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `app:ch_regular:eq:chain-tail`: the common half-space constant is nonnegative. -/
theorem collarDecayConstant_nonneg (μ : Measure E) (K : Set (ℝ × E))
    (eT : ι → E) (eI : κ → ℝ × E) (δT δI GT GI : ℝ)
    (P : ℕ → ℝ) {H A : ℕ → ℝ} (hH : ∀ r, 0 ≤ H r) (hA : ∀ r, 0 ≤ A r)
    (q : ℕ) : 0 ≤ collarDecayConstant μ K eT eI δT δI GT GI P H A q := by
  have hp := collarAmplitudeProfile_nonneg hH hA
  exact add_nonneg
    (mul_nonneg (mul_nonneg (decayConstant_nonneg _ _ _ _ _ hp q)
      measureReal_nonneg) measureReal_nonneg)
    (mul_nonneg (decayConstant_nonneg _ _ _ _ _ hp q) measureReal_nonneg)

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The quantitative half-space theorem of `app:ch_regular:lem:finite-chain`.
The fixed smooth cutoff `χ` equals one near `d = 0`. Its two closed support
pieces lie in open sets carrying respectively a tangential and a full gradient
gap. All analytic assumptions are joint derivative bounds on the original
phase and amplitude; the split amplitudes and their profiles are derived.
The fixed offset `b` is unchanged at every integration order `q`.
A real-valued collar partition can be used by viewing it as complex-valued. -/
theorem norm_halfSpaceOscillatoryIntegral_le
    {UT UI K : Set (ℝ × E)} (hUT : IsOpen UT) (hUI : IsOpen UI) (hK : IsCompact K)
    (eT : ι → E) (eI : κ → ℝ × E) (F : ℝ × E → ℝ) (a χ : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a) (hχ : ContDiff ℝ ∞ χ)
    (hsK : tsupport a ⊆ K)
    (hχT : K ∩ tsupport χ ⊆ UT)
    (hχI : (K ∩ tsupport (1 - χ)) ∩ {x | 0 < x.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ x, |x.1| < ε → χ x = 1)
    {δT δI GT GI L R : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hgapT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      δT ≤ Localization.phaseGradientSquare eT (fun w ↦ F (d, w)) z)
    (hupperT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT → ‖fderiv ℝ F (d, z)‖ ≤ GT)
    (hgapI : ∀ x ∈ UI ∩ {x | 0 < x.1}, δI ≤ Localization.phaseGradientSquare eI F x)
    (hupperI : ∀ x ∈ UI ∩ {x | 0 < x.1}, ‖fderiv ℝ F x‖ ≤ GI)
    {P H A : ℕ → ℝ} (hH : ∀ r, 0 ≤ H r) (hA : ∀ r, 0 ≤ A r) (b q : ℕ)
    (hp : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r (fderiv ℝ F) x‖ ≤ P r * L ^ r)
    (hχ_bound : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ H r)
    (ha_bound : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ A r * L ^ (r + b)) :
    ‖halfSpaceOscillatoryIntegral μ R F a‖ ≤
      collarDecayConstant μ K eT eI δT δI GT GI P H A q * L ^ b * (L / R) ^ q := by
  have hχc : ContDiff ℝ ∞ (1 - χ) := contDiff_const.sub hχ
  have htK : tsupport (χ * a) ⊆ K := tsupport_mul_subset_right.trans hsK
  have hiK : tsupport ((1 - χ) * a) ⊆ K := tsupport_mul_subset_right.trans hsK
  have htU : tsupport (χ * a) ⊆ K ∩ UT := by
    intro x hx
    exact ⟨htK hx, hχT ⟨htK hx, tsupport_mul_subset_left hx⟩⟩
  have hiU : tsupport ((1 - χ) * a) ∩ {x | 0 < x.1} ⊆ UI := by
    intro x hx
    exact hχI ⟨⟨hiK hx.1, tsupport_mul_subset_left hx.1⟩, hx.2⟩
  have ht_bound (x) (hx : x ∈ K) (r) :
      ‖iteratedFDeriv ℝ r (χ * a) x‖ ≤ collarAmplitudeProfile H A r * L ^ (r + b) :=
    norm_iteratedFDeriv_collar_mul_le hχ ha hH hA hL b
      (fun j ↦ (hχ_bound x hx j).trans (by linarith)) (ha_bound x hx) r
  have hi_bound (x) (hx : x ∈ K) (r) :
      ‖iteratedFDeriv ℝ r ((1 - χ) * a) x‖ ≤
        collarAmplitudeProfile H A r * L ^ (r + b) :=
    norm_iteratedFDeriv_collar_mul_le hχc ha hH hA hL b
      (norm_iteratedFDeriv_one_sub_le hχ (hχ_bound x hx)) (ha_bound x hx) r
  have ht := norm_halfSpaceOscillatoryIntegral_le_tangential (μ := μ) hUT hK eT F (χ * a)
    hF (hχ.mul ha) htU hδT hL hR hgapT hupperT
    (collarAmplitudeProfile_nonneg hH hA) b q hp ht_bound
  have hi := norm_halfSpaceOscillatoryIntegral_le_interior (μ := μ) hUI hK eI F ((1 - χ) * a)
    hF (hχc.mul ha) hiK hiU hε
    (fun x hx ↦ by simp [Pi.mul_apply, Pi.sub_apply, hχ_one x hx])
    hδI hL hR hgapI hupperI (collarAmplitudeProfile_nonneg hH hA) b q
    (fun x hx ↦ hp x hx.1) (fun x hx ↦ hi_bound x hx.1)
  have hsplit : a = χ * a + (1 - χ) * a := by ext x; simp; ring
  have heq : halfSpaceOscillatoryIntegral μ R F a =
      halfSpaceOscillatoryIntegral μ R F (χ * a) +
        halfSpaceOscillatoryIntegral μ R F ((1 - χ) * a) := by
    conv_lhs => rw [hsplit]
    exact halfSpaceOscillatoryIntegral_add hF (hχ.mul ha) (hχc.mul ha)
      (hK.of_isClosed_subset (isClosed_tsupport _) htK)
      (hK.of_isClosed_subset (isClosed_tsupport _) hiK) R
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add ht hi).trans_eq (by
    unfold collarDecayConstant
    ring))

/-- Parameter-uniform half-space decay for `app:ch_regular:eq:chain-tail`.
The parameter type may include base points, Taylor parameters, or an output
derivative index with a common profile and fixed offset. The constant is
chosen before the parameter and is the explicit `collarDecayConstant`;
no regularity in the external parameter is needed. -/
theorem exists_uniform_halfSpace_decay {Θ : Type*}
    {UT UI K : Set (ℝ × E)} (hUT : IsOpen UT) (hUI : IsOpen UI) (hK : IsCompact K)
    (eT : ι → E) (eI : κ → ℝ × E) (F : Θ → ℝ × E → ℝ) (a : Θ → ℝ × E → ℂ) (χ : ℝ × E → ℂ)
    (hF : ∀ p, ContDiff ℝ ∞ (F p)) (ha : ∀ p, ContDiff ℝ ∞ (a p)) (hχ : ContDiff ℝ ∞ χ)
    (hsK : ∀ p, tsupport (a p) ⊆ K)
    (hχT : K ∩ tsupport χ ⊆ UT)
    (hχI : (K ∩ tsupport (1 - χ)) ∩ {x | 0 < x.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ x, |x.1| < ε → χ x = 1)
    {δT δI GT GI : ℝ} (L R : Θ → ℝ) (hδT : 0 < δT) (hδI : 0 < δI)
    (hL : ∀ p, 1 ≤ L p) (hR : ∀ p, 1 ≤ R p)
    (hgapT : ∀ p d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      δT ≤ Localization.phaseGradientSquare eT (fun w ↦ F p (d, w)) z)
    (hupperT : ∀ p d, 0 ≤ d → ∀ z, (d, z) ∈ UT → ‖fderiv ℝ (F p) (d, z)‖ ≤ GT)
    (hgapI : ∀ p, ∀ x ∈ UI ∩ {x | 0 < x.1}, δI ≤ Localization.phaseGradientSquare eI (F p) x)
    (hupperI : ∀ p, ∀ x ∈ UI ∩ {x | 0 < x.1}, ‖fderiv ℝ (F p) x‖ ≤ GI)
    {P H A : ℕ → ℝ} (hH : ∀ r, 0 ≤ H r) (hA : ∀ r, 0 ≤ A r) (b : ℕ)
    (hp : ∀ p, ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r (fderiv ℝ (F p)) x‖ ≤ P r * (L p) ^ r)
    (hχ_bound : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ H r)
    (ha_bound : ∀ p, ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r (a p) x‖ ≤ A r * (L p) ^ (r + b)) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ ∀ p q,
      ‖halfSpaceOscillatoryIntegral μ (R p) (F p) (a p)‖ ≤
        C q * (L p) ^ b * (L p / R p) ^ q := by
  refine ⟨collarDecayConstant μ K eT eI δT δI GT GI P H A,
    collarDecayConstant_nonneg μ K eT eI δT δI GT GI P hH hA, ?_⟩
  intro p q
  exact norm_halfSpaceOscillatoryIntegral_le hUT hUI hK eT eI (F p) (a p) χ
    (hF p) (ha p) hχ (hsK p) hχT hχI hε hχ_one hδT hδI (hL p) (hR p)
    (hgapT p) (hupperT p) (hgapI p) (hupperI p) hH hA b q (hp p) hχ_bound (ha_bound p)

end JanetCartan.FiniteChain.Retarded.HalfSpace
