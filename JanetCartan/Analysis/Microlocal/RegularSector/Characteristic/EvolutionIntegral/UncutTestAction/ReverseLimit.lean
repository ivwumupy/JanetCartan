module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.ReversePairing

/-!
# The literal reversed triangle is the constructed Hilbert adjoint

The adjoint strong limits and cutoff-preservation identity exported by
`PrimitiveRetarded` identify all uncut test pairings with the reversed time
triangle. Only zeroth-order multiplier and amplitude bounds enter cutoff
removal. Neither an uncut action nor convergence to it is an input.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Every test pairing of the actual Hilbert adjoint is the absolutely
convergent, original reversed triangle in frequency. The operator order is
`Mχsource* Bβ* E_b* Mχout*`: the source mask is inside the test's transform,
the conjugate multiplier is outside the reversed time triangle, and the
conjugate output mask acts before the adjoint spatial evolution.

The inputs `hcut` and `hstrong` are exact conclusions of
`exists_retardedOperator_of_primitive_data`. Its primitive symbol budgets
supply `hβbound` through `norm_multiplier_le_finite_normalized_budgets`
and `hbound` through `norm_elapsedSpatialAmplitude_le_orderSeminorm`.
This deduction uses no all-orders multiplier hypothesis. Source:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem retardedOperator_adjoint_pairing_reverseTriangle_of_strongLimit
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (hocs : HasCompactSupport χout)
    (hs : ContDiff ℝ ∞ χsource)
    (Cβ Cb : ℝ) (hCβ : 0 ≤ Cβ) (hCb : 0 ≤ Cb)
    (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ Cb)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (hcut : ∀ A : FullAmplitude (d + 1) q,
      (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) → ∀ j,
      frequencyCutFullAmplitude (χ j) A = frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (u v : graphTestSpace (d + 1) q)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (cutReverseRetardedFourier Ψ b χout χsource β (χ j)
          (fun x ↦ (u.val x).ofLp) a (a + Δ) x)) ∧
      Tendsto R atTop (𝓝 (Q.adjoint (graphTestToLp u)))) :
    Integrable (fun ξ ↦ inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
      (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
      (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
        (fun x ↦ (u.val x).ofLp) a (a + Δ) ξ))) ∧
    inner ℂ (graphTestToLp v) (Q.adjoint (graphTestToLp u)) =
      ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
        inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
          (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
          (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
            (fun x ↦ (u.val x).ofLp) a (a + Δ) ξ)) := by
  have hu : Continuous (fun x ↦ (u.val x).ofLp) :=
    (PiLp.continuous_ofLp 2 _).comp u.property.1.continuous
  have hcΔ : a + Δ - a ≤ Δ := by linarith
  have hW := continuous_reverseRetardedFrequency Ψ b χout β Δ hΔ hΨ hb ho hβ
    hocs a (a + Δ) hcΔ hout hzero _ hu
  obtain ⟨B, _hB, hB⟩ := exists_bound_reverseRetardedFrequency
    Ψ b χout β Δ hΔ hΨ hb ho hβ hocs a (a + Δ) hcΔ hout hzero _ hu
    Cβ Cb hCβ hCb hβbound hbound
  have hpair := integrable_and_tendsto_reverseFrequency_pairing
    (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) _ hW B hB
  refine ⟨hpair.1, ?_⟩
  obtain ⟨R, hR, hlim⟩ := hstrong
  have hecut (r : ℝ) (j : ℕ) :
      frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose) =
      frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose) := by
    have he := hcut (elapsedAmplitude b χout χsource β r)
      (fun x z ξ hξ ↦ elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ
        (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ)))) j
    funext x z ξ
    have h := congrArg Matrix.conjTranspose (congrFun (congrFun (congrFun he x) z) ξ)
    simpa only [frequencyCutFullAmplitude, Matrix.conjTranspose_smul] using h
  have he (j : ℕ) (x : E) : cutReverseRetardedFourier Ψ b χout χsource β (χ j)
      (fun x ↦ (u.val x).ofLp) a (a + Δ) x =
      cutReverseRetardedFourier Ψ b χout χsource β (complexPhysicalCutoff j)
        (fun x ↦ (u.val x).ofLp) a (a + Δ) x := by
    rw [← integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier_of_support
      Ψ b χout χsource β Δ hΔ hΨ hb ho hβ (χ j) (hχ j).continuous
      hocs (hχcs j) a (a + Δ) hcΔ hout hzero _ hu x,
      ← integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier_of_support
      Ψ b χout χsource β Δ hΔ hΨ hb ho hβ (complexPhysicalCutoff j)
      (complexPhysicalCutoff_contDiff j).continuous hocs
      (complexPhysicalCutoff_hasCompactSupport j) a (a + Δ) hcΔ hout hzero _ hu x]
    simp_rw [hecut]
  have hp (j : ℕ) : inner ℂ (graphTestToLp v) (R j) =
      ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
        inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
          (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
          (WithLp.toLp 2 (star (complexPhysicalCutoff j ξ) • reverseRetardedFrequency
            Ψ b χout β (fun x ↦ (u.val x).ofLp) a (a + Δ) ξ)) := by
    rw [L2.inner_def]
    trans ∫ x, inner ℂ (v.val x) (WithLp.toLp 2
      (cutReverseRetardedFourier Ψ b χout χsource β (complexPhysicalCutoff j)
        (fun x ↦ (u.val x).ofLp) a (a + Δ) x))
    · apply integral_congr_ae
      filter_upwards [hR j, (graphTest_memLp v).coeFn_toLp] with x hx hv
      rw [show graphTestToLp v x = v.val x from hv, hx, he]
    · exact cutReverseRetardedFourier_pairing Ψ b χout χsource β _ hs
        (complexPhysicalCutoff_contDiff j).continuous
        (complexPhysicalCutoff_hasCompactSupport j) a (a + Δ) u v hW
  exact tendsto_nhds_unique
    (((tendsto_const_nhds (x := graphTestToLp v)).inner (𝕜 := ℂ) hlim).congr hp)
    (hpair.2.const_mul _)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
