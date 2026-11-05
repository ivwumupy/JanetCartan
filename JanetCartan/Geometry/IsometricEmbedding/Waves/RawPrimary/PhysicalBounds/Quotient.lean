module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Representation
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Integral

/-!
# Physical jets of the literal phase quotient

The quotient/FTC step of `app:ch_waves:eq:raw-physical-bound`. Primitive
physical derivatives of the covector derivative of the phase yield a bound
linear in the input frequency and independent of the nonzero shift size.
The consuming declaration is the raw oscillatory-atom physical bound.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.RawPrimary

variable {X P : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {U : Set X} {V : Set P} {S : X → P → ℝ}

omit [FiniteDimensional ℝ X] in
/-- Joint smoothness of the primitive covector derivative on the original
phase chart (`app:ch_waves:eq:phase-quotient`). -/
theorem contDiffOn_rawPhaseCovectorDerivative (hU : IsOpen U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : X × P ↦ fderiv ℝ (S p.1) p.2) (U ×ˢ V) := by
  have hswap : ContDiffOn ℝ ∞ (fun p : P × X ↦ S p.2 p.1) (V ×ˢ U) :=
    hS.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ h ↦ ⟨h.2, h.1⟩)
  exact (contDiffOn_parameterFDeriv hV hU hswap).comp
    (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ h ↦ ⟨h.2, h.1⟩)

omit [FiniteDimensional ℝ X] in
/-- The literal quotient equals the integral of the primitive covector derivative
on the actual shifted segment. Only containment of that segment in the original
open chart is required (`app:ch_waves:eq:phase-quotient`). -/
theorem rawPrimaryPhaseDifference_eq_segmentIntegral (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    {ζ η : P} {τ : ℝ} (hτ : τ ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + (t * τ) • η ∈ V)
    {x : X} (hx : x ∈ U) :
    rawPrimaryPhaseDifference S ζ τ x η =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (S x) (ζ + (t * τ) • η) η := by
  have hf : ContDiffOn ℝ 1 (S x) V :=
    contDiffOn_phase_slice (hS.of_le (by simp)) hx
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ S x (ζ + (t * τ) • η))
        (τ * fderiv ℝ (S x) (ζ + (t * τ) • η) η) t := by
    intro t ht
    have hmem := hseg t (by simpa using ht)
    have hs := (hf.contDiffAt (hV.mem_nhds hmem)).differentiableAt one_ne_zero
    convert hs.hasFDerivAt.comp_hasDerivAt t
      ((((hasDerivAt_id t).mul_const τ).smul_const η).const_add ζ) using 1 <;>
      simp only [Function.comp_def, id_eq, one_mul, map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun t : ℝ ↦ fderiv ℝ (S x) (ζ + (t * τ) • η) η)
      (Icc 0 1) :=
    ((hf.continuousOn_fderiv_of_isOpen hV le_rfl).comp (by fun_prop) hseg).clm_apply
      continuousOn_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_const.mul hc).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  rw [intervalIntegral.integral_const_mul] at he
  simp only [one_mul, zero_mul, zero_smul, add_zero] at he
  rw [rawPrimaryPhaseDifference, ← he, mul_div_cancel_left₀ _ hτ]

/-- The exact quotient has physical jets bounded by primitive covector jets
times the input frequency. The segment integral is differentiated using the
checked compact-parameter calculus, without a derivative-interchange premise
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_rawPrimaryPhaseDifference_le
    (hU : IsOpen U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    {ζ η : P} {τ : ℝ} (hτ : τ ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + (t * τ) • η ∈ V)
    {x : X} (hx : x ∈ U) (r : ℕ) {B : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ (S y) (ζ + (t * τ) • η)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ r (fun y ↦ rawPrimaryPhaseDifference S ζ τ y η) x‖ ≤
      ‖η‖ * B := by
  let W : Set ℝ := {t | ζ + (t * τ) • η ∈ V}
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hIW : Icc (0 : ℝ) 1 ⊆ W := hseg
  let G : X × ℝ → ℝ := fun p ↦ fderiv ℝ (S p.1) (ζ + (p.2 * τ) • η) η
  have hD := contDiffOn_rawPhaseCovectorDerivative hU hV hS
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ W) := by
    apply (hD.comp (contDiffOn_fst.prodMk
      (contDiffOn_const.add ((contDiffOn_snd.mul contDiffOn_const).smul contDiffOn_const)))
      (fun p hp ↦ ⟨hp.1, hp.2⟩)).clm_apply contDiffOn_const
  have heq : (fun y ↦ rawPrimaryPhaseDifference S ζ τ y η) =ᶠ[𝓝 x]
      (fun y ↦ ∫ t in (0 : ℝ)..1, G (y, t)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact rawPrimaryPhaseDifference_eq_segmentIntegral hV hS hτ hseg hy
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) (n := r)).eq_of_nhds]
  apply FullPhaseCharts.InverseEstimates.norm_iteratedFDeriv_unitIntervalParameterIntegral_le
    hU hW hIW hG hx r
  intro t ht
  let ev : (P →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ η
  have hDt : ContDiffAt ℝ ∞ (fun y ↦ fderiv ℝ (S y) (ζ + (t * τ) • η)) x :=
    (hD.contDiffAt ((hU.prod hV).mem_nhds
      (show (x, ζ + (t * τ) • η) ∈ U ×ˢ V from ⟨hx, hIW ht⟩))).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  change ‖iteratedFDeriv ℝ r (ev ∘ (fun y ↦ fderiv ℝ (S y) (ζ + (t * τ) • η))) x‖ ≤ _
  rw [ev.iteratedFDeriv_comp_left hDt (by simp)]
  apply (ev.norm_compContinuousMultilinearMap_le _).trans
  apply mul_le_mul _ (hb t ht) (norm_nonneg _) (norm_nonneg η)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg η)
    (fun f ↦ by simpa [ev, mul_comm] using f.le_opNorm η)

/-- The primitive grade in the paper gives `K L^(r-1)` for the exact
nonzero quotient, uniformly on the initial ball of radius `c K`
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_rawPrimaryPhaseDifference_le_grade
    (hU : IsOpen U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    {ζ η : P} {τ : ℝ} (hτ : τ ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + (t * τ) • η ∈ V)
    {x : X} (hx : x ∈ U) (r : ℕ) {s c K L : ℝ}
    (hs : 0 ≤ s) (hL : 0 ≤ L) (hη : ‖η‖ ≤ c * K)
    (hb : ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ (S y) ξ) x‖ ≤ s * L ^ (r - 1)) :
    ‖iteratedFDeriv ℝ r (fun y ↦ rawPrimaryPhaseDifference S ζ τ y η) x‖ ≤
      (c * s) * K * L ^ (r - 1) := by
  apply (norm_iteratedFDeriv_rawPrimaryPhaseDifference_le hU hV hS
    hτ hseg hx r (fun t ht ↦ hb _ (hseg t ht))).trans
  convert mul_le_mul_of_nonneg_right hη (mul_nonneg hs (pow_nonneg hL _)) using 1
  ring

end JanetCartan.RawPrimary
