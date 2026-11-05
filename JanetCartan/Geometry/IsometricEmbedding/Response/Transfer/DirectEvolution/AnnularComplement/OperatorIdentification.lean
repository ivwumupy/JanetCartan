module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity

/-!
# Identifying complementary integrals with the same uncut operator

The finite-frequency all-input realization and the original strong graph
limits identify the physical annular integral. The reverse branch uses the
literal Hilbert adjoint, including the conjugated frequency cutoff.
Consumer: `app:ch_response:eq:direct-envelope-profile`; source:
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Select the original bounded graph or its literal Hilbert adjoint, without
constructing a second reverse operator (`energy-carrier-jets`). -/
def annularGraphOrientation (adj : Bool) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  if adj then T.adjoint else T

/-- The actual graph constructor's test actions identify its regularizations
with the canonical full graphs. Its cutoff-preservation conclusion replaces
the support-adapted cutoffs by the fixed physical exhaustion. This is the
precise strong-limit input to `originalAnnularComplement_sobolev`, derived
from the outputs of `exists_elapsedGraphFamily_of_primitive_phase`; it works
for both the forward and literal-adjoint strong limits. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem annularGraphOrientation_strongLimit_of_testRealizations
    (adj : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (χ : ℕ → E → ℂ) (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace n r), Treg j (graphTestToLp u) =ᵐ[volume]
      graphTestOutput Θ (frequencyCutFullAmplitude (χ j) A) u)
    (hcut : ∀ j, frequencyCutFullAmplitude (χ j) A =
      frequencyCutFullAmplitude (LowBounds.FrequencyCutoff.complexPhysicalCutoff j) A)
    (hstrong : ∀ w : H, Tendsto (fun j => annularGraphOrientation adj (Treg j) w)
      atTop (𝓝 (annularGraphOrientation adj (fullGraphOperator Θ A) w))) :
    ∀ w : H, Tendsto (fun j => annularGraphOrientation adj
      (fullGraphOperator Θ
        (frequencyCutFullAmplitude (LowBounds.FrequencyCutoff.complexPhysicalCutoff j) A)) w)
      atTop (𝓝 (annularGraphOrientation adj (fullGraphOperator Θ A) w)) := by
  have he (j : ℕ) : fullGraphOperator Θ
      (frequencyCutFullAmplitude (LowBounds.FrequencyCutoff.complexPhysicalCutoff j) A) =
        Treg j := by
    rw [← hcut j]
    exact fullGraphOperator_eq_of_realizes Θ _ _ (hreal j)
  simpa only [he] using hstrong

/-- The frequency cutoff stays inside the actual amplitude. In the adjoint
orientation its scalar is conjugated (`energy-carrier-jets`). -/
theorem annularSourceKernelObservation_frequencyCut
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (θ π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    annularSourceKernelObservation adj demod Θ (frequencyCutFullAmplitude θ A)
      π φ lam a x ξ = (if adj then star (θ ξ) else θ ξ) •
        annularSourceKernelObservation adj demod Θ A π φ lam a x ξ := by
  rw [annularSourceKernelObservation_eq_integral,
    annularSourceKernelObservation_eq_integral, smul_comm (if adj then _ else _)]
  congr 1
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with z
  cases adj <;> cases demod <;>
    simp only [annularSourceIntegrand, Bool.false_eq_true, ↓reduceIte,
      forwardAnnularSourceAmplitude, adjointAnnularSourceAmplitude,
      annularComplementAmplitude, frequencyCutFullAmplitude,
      Matrix.conjTranspose_smul, Matrix.smul_mulVec, WithLp.toLp_smul,
      star_mul, smul_smul]
  all_goals congr 1; ring

/-- The full complementary scalar is retained, for arbitrary complex
selectors and both orientations (`energy-carrier-jets`). -/
theorem annularSourceKernelObservation_eq_complement_smul
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    annularSourceKernelObservation adj demod Θ A π φ lam a x ξ =
      (1 - if adj then star (π (lam⁻¹ • ξ)) else π (lam⁻¹ • ξ)) •
        annularSourceKernelObservation adj demod Θ A 0 φ lam a x ξ := by
  rw [annularSourceKernelObservation_eq_integral,
    annularSourceKernelObservation_eq_integral, smul_comm (1 - _)]
  congr 1
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with z
  cases adj <;> cases demod <;>
    simp only [annularSourceIntegrand, Bool.false_eq_true, ↓reduceIte,
      forwardAnnularSourceAmplitude, adjointAnnularSourceAmplitude,
      annularComplementAmplitude, frequencyCutFullAmplitude, Pi.zero_apply,
      sub_zero, one_smul, Matrix.conjTranspose_smul, Matrix.smul_mulVec,
      WithLp.toLp_smul, star_sub, star_one, smul_smul]
  all_goals congr 1; ring

/-- Supported phase replacement preserves every literal source kernel,
including the physical and demodulated adjoints (`energy-carrier-jets`). -/
theorem annularSourceKernelObservation_phase_congr
    (adj demod : Bool) (Θ Θ' : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F)
    (he : ∀ x z ξ, A x z ξ ≠ 0 → Θ' x ξ = Θ x ξ) (x ξ : E) :
    annularSourceKernelObservation adj demod Θ' A π φ lam a x ξ =
      annularSourceKernelObservation adj demod Θ A π φ lam a x ξ := by
  simp only [annularSourceKernelObservation_eq_integral]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => annularSourceIntegrand_phase_congr
    adj demod Θ Θ' A π φ lam a he x ξ z)

/-- Compact-frequency all-input realization on an original carrier, with its
physical vector normalization. The AE source premise only identifies the
chosen L² representative; it is not an operator estimate. -/
theorem annularGraphOrientation_frequencyCut_ae
    (adj : Bool) (Θ : E → E → ℝ) (hΘ : ContDiff ℝ ∞ (Function.uncurry Θ))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (w : H)
    (hw : w =ᵐ[volume] fun z => carrier lam φ z • a z) :
    annularGraphOrientation adj (fullGraphOperator Θ (frequencyCutFullAmplitude θ A)) w
      =ᵐ[volume] fun x => ∫ ξ, (if adj then star (θ ξ) else θ ξ) •
        annularSourceKernelObservation adj false Θ A 0 φ lam a x ξ := by
  have hr := fullGraphOperator_frequencyCut_allInput Θ hΘ A hA hX hY hs θ hθ hθs
  have hz : annularComplementAmplitude (0 : E → ℂ) lam
      (frequencyCutFullAmplitude θ A) = frequencyCutFullAmplitude θ A := by
    funext x z ξ
    simp [annularComplementAmplitude, frequencyCutFullAmplitude]
  have he (x : E) : (∫ ξ, (if adj then star (θ ξ) else θ ξ) •
      annularSourceKernelObservation adj false Θ A 0 φ lam a x ξ) =
      ∫ ξ, annularSourceKernelObservation adj false Θ
        (frequencyCutFullAmplitude θ A) 0 φ lam a x ξ := by
    simp only [annularSourceKernelObservation_frequencyCut]
  cases adj
  · apply (hr.1 w).trans
    apply ae_of_all
    intro x
    dsimp only
    rw [he x]
    simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
      integral_forwardAnnularSourceKernel, hz]
    congr 1
    unfold graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hw] with z hz
    rw [hz, WithLp.ofLp_smul]
  · apply (hr.2 w).trans
    apply ae_of_all
    intro x
    dsimp only
    rw [he x]
    simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
      integral_adjointAnnularSourceKernel, hz]
    congr 1
    unfold reverseGraphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hw] with z hz
    simp only [hz, WithLp.ofLp_smul, frequencyCutFullAmplitude, Matrix.conjTranspose_smul]

/-- Removing the original strong regularizations identifies the complementary
integral with subtraction of the SAME uncut graph and its annular cut.
`hi` is supplied by `originalAnnularComplement_sobolev`; `hc` is the original
supported-kernel regularity theorem with selector zero. Neither an uncut
remainder estimate nor a complementary strong limit is assumed. The original
strong limits in both orientations are produced by
`EvolutionIntegral.exists_elapsedGraphFamily_of_primitive_phase`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularGraphDifference_ae_of_strong_limit
    (adj : Bool) (Θ : E → E → ℝ) (hΘ : ContDiff ℝ ∞ (Function.uncurry Θ))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (π : E → ℂ) (lam : ℝ)
    (hq : ContDiff ℝ ∞ (fun ξ => π (lam⁻¹ • ξ)))
    (hqc : HasCompactSupport (fun ξ => π (lam⁻¹ • ξ)))
    (φ : E → ℝ) (a : E → F) (w : H)
    (hw : w =ᵐ[volume] fun z => carrier lam φ z • a z)
    (hc : ∀ x, Continuous (fun ξ => annularSourceKernelObservation adj false Θ A 0 φ lam a x ξ))
    (hi : ∀ x, Integrable (fun ξ => annularSourceKernelObservation adj false Θ A π φ lam a x ξ))
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχc : ∀ j, HasCompactSupport (χ j)) (hχb : ∀ j ξ, ‖χ j ξ‖ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun j => χ j ξ) atTop (𝓝 1))
    (hstrong : Tendsto (fun j => annularGraphOrientation adj
      (fullGraphOperator Θ (frequencyCutFullAmplitude (χ j) A)) w) atTop
        (𝓝 (annularGraphOrientation adj (fullGraphOperator Θ A) w))) :
    (annularGraphOrientation adj (fullGraphOperator Θ A) w -
      annularGraphOrientation adj
        (fullGraphOperator Θ (frequencyCutFullAmplitude (fun ξ => π (lam⁻¹ • ξ)) A)) w)
      =ᵐ[volume] fun x => ∫ ξ,
        annularSourceKernelObservation adj false Θ A π φ lam a x ξ := by
  let q := fun ξ => if adj then star (π (lam⁻¹ • ξ)) else π (lam⁻¹ • ξ)
  let χ' := fun j ξ => if adj then star (χ j ξ) else χ j ξ
  let k := fun x ξ => annularSourceKernelObservation adj false Θ A 0 φ lam a x ξ
  have hqcont : Continuous q := by
    cases adj
    · exact hq.continuous
    · exact hq.continuous.star
  have hqcompact : HasCompactSupport q := by
    cases adj
    · exact hqc
    · exact hqc.comp_left (star_zero ℂ)
  have hcut (x : E) : Integrable (fun ξ => q ξ • k x ξ) :=
    (hqcont.smul (hc x)).integrable_of_hasCompactSupport hqcompact.smul_right
  have hk (x : E) : Integrable (k x) := by
    apply ((hi x).add (hcut x)).congr
    filter_upwards [] with ξ
    dsimp only [Pi.add_apply]
    rw [annularSourceKernelObservation_eq_complement_smul]
    change (1 - q ξ) • k x ξ + q ξ • k x ξ = k x ξ
    rw [sub_smul, one_smul, sub_add_cancel]
  have hlit (x : E) : Tendsto (fun j => ∫ ξ, χ' j ξ • k x ξ) atTop (𝓝 (∫ ξ, k x ξ)) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ => ‖k x ξ‖)
    · intro j
      have hm : Continuous (χ' j) := by
        cases adj
        · exact (hχ j).continuous
        · exact (hχ j).continuous.star
      exact hm.aestronglyMeasurable.smul (hk x).aestronglyMeasurable
    · exact (hk x).norm
    · intro j
      filter_upwards [] with ξ
      rw [norm_smul]
      have hnorm : ‖χ' j ξ‖ ≤ 1 := by cases adj <;> simpa [χ'] using hχb j ξ
      exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [] with ξ
      have hlim : Tendsto (fun j => χ' j ξ) atTop (𝓝 (1 : ℂ)) := by
        cases adj
        · exact hχlim ξ
        · simpa [χ'] using (hχlim ξ).star
      simpa using hlim.smul_const (k x ξ)
  have hreal (j : ℕ) := annularGraphOrientation_frequencyCut_ae adj Θ hΘ A hA hX hY hs
    (χ j) (hχ j) (hχc j) φ lam a w hw
  obtain ⟨s, hs', hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  have hfull : annularGraphOrientation adj (fullGraphOperator Θ A) w =ᵐ[volume]
      fun x => ∫ ξ, k x ξ := by
    filter_upwards [hsub, ae_all_iff.mpr hreal] with x hx he
    apply tendsto_nhds_unique hx
    apply ((hlit x).comp hs'.tendsto_atTop).congr
    intro j
    exact (he (s j)).symm
  have hann := annularGraphOrientation_frequencyCut_ae adj Θ hΘ A hA hX hY hs
    (fun ξ => π (lam⁻¹ • ξ)) hq hqc φ lam a w hw
  filter_upwards [Lp.coeFn_sub (annularGraphOrientation adj (fullGraphOperator Θ A) w)
    (annularGraphOrientation adj
      (fullGraphOperator Θ (frequencyCutFullAmplitude (fun ξ => π (lam⁻¹ • ξ)) A)) w),
    hfull, hann] with x hx hf ha
  rw [hx, Pi.sub_apply, hf, ha, ← integral_sub (hk x) (hcut x)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [annularSourceKernelObservation_eq_complement_smul]
  change k x ξ - q ξ • k x ξ = (1 - q ξ) • k x ξ
  rw [sub_smul, one_smul]

/-- The same uncut identification on the original supported phase chart. A
smooth auxiliary extension is removed from both operators and both kernels.
In particular no smoothness at frequency zero is imposed on the physical
elapsed phase (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularGraphDifference_ae_of_supported_strong_limit
    (adj : Bool) (Θ : E → E → ℝ) {D Ω : Set (E × E)}
    (hD : IsClosed D) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω)
    (hΘ : ContDiffOn ℝ ∞ (Function.uncurry Θ) Ω)
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2))
    (hsD : ∀ x z ξ, A x z ξ ≠ 0 → (x, ξ) ∈ D)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (π : E → ℂ) (lam : ℝ)
    (hq : ContDiff ℝ ∞ (fun ξ => π (lam⁻¹ • ξ)))
    (hqc : HasCompactSupport (fun ξ => π (lam⁻¹ • ξ)))
    (φ : E → ℝ) (a : E → F) (w : H)
    (hw : w =ᵐ[volume] fun z => carrier lam φ z • a z)
    (hc : ∀ x, Continuous (fun ξ => annularSourceKernelObservation adj false Θ A 0 φ lam a x ξ))
    (hi : ∀ x, Integrable (fun ξ => annularSourceKernelObservation adj false Θ A π φ lam a x ξ))
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχc : ∀ j, HasCompactSupport (χ j)) (hχb : ∀ j ξ, ‖χ j ξ‖ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun j => χ j ξ) atTop (𝓝 1))
    (hstrong : Tendsto (fun j => annularGraphOrientation adj
      (fullGraphOperator Θ (frequencyCutFullAmplitude (χ j) A)) w) atTop
        (𝓝 (annularGraphOrientation adj (fullGraphOperator Θ A) w))) :
    (annularGraphOrientation adj (fullGraphOperator Θ A) w -
      annularGraphOrientation adj
        (fullGraphOperator Θ (frequencyCutFullAmplitude (fun ξ => π (lam⁻¹ • ξ)) A)) w)
      =ᵐ[volume] fun x => ∫ ξ,
        annularSourceKernelObservation adj false Θ A π φ lam a x ξ := by
  obtain ⟨Θ', hΘ', he⟩ := exists_smooth_phase_extension Θ hD hΩ hDΩ hΘ
  have heA (x z ξ : E) (h : A x z ξ ≠ 0) : Θ' x ξ = Θ x ξ :=
    (he (x, ξ) (hsD x z ξ h)).eq_of_nhds
  have hfull := fullGraphOperator_phase_congr Θ Θ' A heA
  have hcut (θ : E → ℂ) : fullGraphOperator Θ' (frequencyCutFullAmplitude θ A) =
      fullGraphOperator Θ (frequencyCutFullAmplitude θ A) := by
    apply fullGraphOperator_phase_congr
    intro x z ξ h
    exact heA x z ξ (fun hz => h (by simp [frequencyCutFullAmplitude, hz]))
  have hk (π' : E → ℂ) (x ξ : E) :=
    annularSourceKernelObservation_phase_congr adj false Θ Θ' A π' φ lam a heA x ξ
  have hc' (x : E) : Continuous (fun ξ => annularSourceKernelObservation adj false Θ' A 0 φ lam a x ξ) := by
    simpa only [hk] using hc x
  have hi' (x : E) : Integrable (fun ξ => annularSourceKernelObservation adj false Θ' A π φ lam a x ξ) := by
    simpa only [hk] using hi x
  have hstrong' : Tendsto (fun j => annularGraphOrientation adj
      (fullGraphOperator Θ' (frequencyCutFullAmplitude (χ j) A)) w) atTop
        (𝓝 (annularGraphOrientation adj (fullGraphOperator Θ' A) w)) := by
    simpa only [hfull, hcut] using hstrong
  have hr := annularGraphDifference_ae_of_strong_limit adj Θ' hΘ' A hA hX hY hs
    π lam hq hqc φ a w hw hc' hi' χ hχ hχc hχb hχlim hstrong'
  simpa only [hfull, hcut, hk] using hr

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
