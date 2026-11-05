module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Scaling

/-!
# Interior half-space decay

The interior part of the half-space argument in
`app:ch_regular:lem:finite-chain`, “A common kernel estimate” and “Retarded
and signed factors”. An amplitude vanishing in a collar of the boundary has
a smooth extension obtained by retaining its nonnegative-time values and
setting its negative-time values to zero. Its derivative profiles on its
support are unchanged, so whole-space integration by parts gives the graded
decay of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

variable {E : Type*}

/-- The positive half-space extension used for the interior amplitude in
`app:ch_regular:lem:finite-chain`. Negative-time support of the original
amplitude is discarded. -/
def positiveHalfSpaceExtension (a : ℝ × E → ℂ) (x : ℝ × E) : ℂ :=
  if 0 ≤ x.1 then a x else 0

/-- `app:ch_regular:lem:finite-chain`: the extension retains the amplitude
on the closed positive half-space. -/
theorem positiveHalfSpaceExtension_eq {a : ℝ × E → ℂ} {x : ℝ × E}
    (hx : 0 ≤ x.1) : positiveHalfSpaceExtension a x = a x := by
  simp [positiveHalfSpaceExtension, hx]

/-- `app:ch_regular:lem:finite-chain`: the vanishing collar extends to the
entire region below its positive endpoint. -/
theorem positiveHalfSpaceExtension_eq_zero_of_lt {a : ℝ × E → ℂ} {ε : ℝ}
    (hvanish : ∀ x, |x.1| < ε → a x = 0) {x : ℝ × E} (hx : x.1 < ε) :
    positiveHalfSpaceExtension a x = 0 := by
  unfold positiveHalfSpaceExtension
  split_ifs with h
  · exact hvanish x (by rwa [abs_of_nonneg h])
  · rfl

variable [NormedAddCommGroup E]

/-- `app:ch_regular:lem:finite-chain`: at strictly positive times the
extension agrees locally with the original amplitude. -/
theorem positiveHalfSpaceExtension_eventuallyEq {a : ℝ × E → ℂ} {x : ℝ × E}
    (hx : 0 < x.1) : positiveHalfSpaceExtension a =ᶠ[𝓝 x] a := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hx] with y hy
  exact positiveHalfSpaceExtension_eq hy.le

/-- `app:ch_regular:lem:finite-chain`: the closed support of the extension
lies in the original closed support, at distance at least `ε` from the boundary. -/
theorem tsupport_positiveHalfSpaceExtension_subset {a : ℝ × E → ℂ} {ε : ℝ}
    (hvanish : ∀ x, |x.1| < ε → a x = 0) :
    tsupport (positiveHalfSpaceExtension a) ⊆ tsupport a ∩ {x | ε ≤ x.1} := by
  apply closure_minimal ?_ ((isClosed_tsupport a).inter
    (isClosed_le continuous_const continuous_fst))
  intro x hx
  constructor
  · apply subset_tsupport
    intro ha
    exact hx (by simp [positiveHalfSpaceExtension, ha])
  · by_contra h
    exact hx (positiveHalfSpaceExtension_eq_zero_of_lt hvanish (lt_of_not_ge h))

/-- `app:ch_regular:lem:finite-chain`: a common support set remains a common
support set after positive extension, with the collar explicitly excluded. -/
theorem tsupport_positiveHalfSpaceExtension_subset_of_subset
    {a : ℝ × E → ℂ} {K : Set (ℝ × E)} {ε : ℝ}
    (hsK : tsupport a ⊆ K) (hvanish : ∀ x, |x.1| < ε → a x = 0) :
    tsupport (positiveHalfSpaceExtension a) ⊆ K ∩ {x | ε ≤ x.1} := by
  intro x hx
  have h := tsupport_positiveHalfSpaceExtension_subset hvanish hx
  exact ⟨hsK h.1, h.2⟩

variable [NormedSpace ℝ E]

/-- `app:ch_regular:lem:finite-chain`: the extension is globally smooth.
At nonpositive times it is locally zero by the vanishing collar; at positive
times it agrees locally with the smooth original amplitude. -/
theorem contDiff_positiveHalfSpaceExtension {a : ℝ × E → ℂ} {ε : ℝ}
    (hε : 0 < ε) (ha : ContDiff ℝ ∞ a)
    (hvanish : ∀ x, |x.1| < ε → a x = 0) :
    ContDiff ℝ ∞ (positiveHalfSpaceExtension a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x.1
  · exact ha.contDiffAt.congr_of_eventuallyEq (positiveHalfSpaceExtension_eventuallyEq hx)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hxε : x.1 < ε := lt_of_le_of_lt (le_of_not_gt hx) hε
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hxε] with y hy
    exact positiveHalfSpaceExtension_eq_zero_of_lt hvanish hy

/-- `app:ch_regular:lem:finite-chain`: every joint derivative of the extension
agrees with that of the amplitude at positive times. In particular the same
derivative profile applies on the extended support when `ε > 0`. -/
theorem iteratedFDeriv_positiveHalfSpaceExtension {a : ℝ × E → ℂ} {x : ℝ × E}
    (hx : 0 < x.1) (r : ℕ) :
    iteratedFDeriv ℝ r (positiveHalfSpaceExtension a) x = iteratedFDeriv ℝ r a x :=
  ((positiveHalfSpaceExtension_eventuallyEq hx).iteratedFDeriv ℝ r).eq_of_nhds

variable [MeasurableSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:ch_regular:lem:finite-chain`: the whole-space oscillatory integral
of the extension is exactly the original half-space oscillatory integral. -/
theorem integral_positiveHalfSpaceExtension (μ : Measure E) (R : ℝ)
    (F : ℝ × E → ℝ) (a : ℝ × E → ℂ) :
    (∫ x, Localization.phaseOscillation (R • F) x * positiveHalfSpaceExtension a x
      ∂(volume.prod μ)) = halfSpaceOscillatoryIntegral μ R F a := by
  unfold halfSpaceOscillatoryIntegral halfSpaceIntegral
  rw [← integral_indicator (measurableSet_Ici.prod MeasurableSet.univ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by
    by_cases hx : 0 ≤ x.1 <;> simp [positiveHalfSpaceExtension, Set.indicator, hx])

variable [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- The interior half-space estimate of `app:ch_regular:lem:finite-chain`,
with the fixed amplitude offset and graded decay of `app:ch_regular:eq:chain-tail`.
The hypotheses on the phase and derivative profiles are needed only at positive
times. The original amplitude may also have negative-time support outside the
vanishing collar. The constant depends only on the common geometry, gradient
gap, derivative profiles and integration order, and not on `ε`, `L`, `R`, `b`
or any external parameters satisfying the same bounds. -/
theorem norm_halfSpaceOscillatoryIntegral_le_interior {μ : Measure E} [μ.IsAddHaarMeasure]
    {U K : Set (ℝ × E)} (hU : IsOpen U) (hK : IsCompact K)
    (e : ι → ℝ × E) (F : ℝ × E → ℝ) (a : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    (hsK : tsupport a ⊆ K) (hsU : tsupport a ∩ {x | 0 < x.1} ⊆ U)
    {ε : ℝ} (hε : 0 < ε) (hvanish : ∀ x, |x.1| < ε → a x = 0)
    {δ G L R : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hgap : ∀ x ∈ U ∩ {x | 0 < x.1}, δ ≤ Localization.phaseGradientSquare e F x)
    (hupper : ∀ x ∈ U ∩ {x | 0 < x.1}, ‖fderiv ℝ F x‖ ≤ G)
    {P A : ℕ → ℝ} (hA : ∀ r, 0 ≤ A r) (b q : ℕ)
    (hp : ∀ x ∈ K ∩ {x | 0 < x.1}, ∀ r,
      ‖iteratedFDeriv ℝ r (fderiv ℝ F) x‖ ≤ P r * L ^ r)
    (ha_bound : ∀ x ∈ K ∩ {x | 0 < x.1}, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ A r * L ^ (r + b)) :
    ‖halfSpaceOscillatoryIntegral μ R F a‖ ≤
      (decayConstant e δ G P A q * (volume.prod μ).real K) * L ^ b * (L / R) ^ q := by
  have hs := tsupport_positiveHalfSpaceExtension_subset hvanish
  have hspos (x : ℝ × E) (hx : x ∈ tsupport (positiveHalfSpaceExtension a)) :
      0 < x.1 := lt_of_lt_of_le hε (hs hx).2
  have hsUK : tsupport (positiveHalfSpaceExtension a) ⊆ U ∩ {x | 0 < x.1} := by
    intro x hx
    exact ⟨hsU ⟨(hs hx).1, hspos x hx⟩, hspos x hx⟩
  rw [← integral_positiveHalfSpaceExtension μ R F a]
  apply norm_oscillatoryIntegral_le
    (hU.inter (isOpen_lt continuous_const continuous_fst)) hK e F
    (positiveHalfSpaceExtension a) hF.contDiffOn
    (contDiff_positiveHalfSpaceExtension hε ha hvanish).contDiffOn hsUK
    (fun x hx ↦ hsK (hs hx).1) hδ hL hR hgap hupper hA b q
  · intro x hx r
    exact hp x ⟨hsK (hs hx).1, hspos x hx⟩ r
  · intro x hx r
    rw [iteratedFDeriv_positiveHalfSpaceExtension (hspos x hx) r]
    exact ha_bound x ⟨hsK (hs hx).1, hspos x hx⟩ r

end JanetCartan.FiniteChain.Retarded.HalfSpace
