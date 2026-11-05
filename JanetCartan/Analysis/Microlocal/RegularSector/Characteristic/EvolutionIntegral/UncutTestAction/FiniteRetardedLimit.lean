module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteRetarded

/-!
# Identifying the constructed retarded operator on the original test space

The exact cutoff-preservation and strong-limit conclusions of
`exists_retardedOperator_of_primitive_data` identify its bounded operator with
`Mχout E_b Bβ Mχsource`. Pointwise uncut convergence is proved here from the
original symbol bound; it is not an input to the identification.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The retarded strong limit exported by `PrimitiveRetarded` acts on every
original graph test as the literal uncut retarded evolution. The hypotheses
`hcut` and `hstrong` are its exact exported conclusions. The symbol bound is
produced by `norm_elapsedSpatialAmplitude_le_orderSeminorm`, and multiplier
derivative bounds by `norm_iteratedFDeriv_multiplier_le_normalized_budgets`
through order `d+2`, which is below the parent's finite low reserve. No desired test action or integrated Sobolev
bound is assumed. Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem retardedOperator_eq_uncutPhysicalIntegral_of_strongLimit
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℕ → ℝ)
    (hβbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ Cβ k)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (hcut : ∀ A : FullAmplitude (d + 1) q,
      (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) → ∀ j,
      frequencyCutFullAmplitude (χ j) A = frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (u : graphTestSpace (d + 1) q)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (cutRetardedPhysical Ψ b χout χsource β (χ j) hs hβ (hχ j) (hχcs j) a u x)) ∧
      Tendsto R atTop (𝓝 (Q (graphTestToLp u)))) :
    Q (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (retardedPhysicalIntegral Ψ b χout χsource β hs a u x) := by
  obtain ⟨R, hR, hlim⟩ := hstrong
  have hecut (r : ℝ) := hcut (elapsedAmplitude b χout χsource β r)
    (fun x y ξ hξ ↦ elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ
      (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ))))
  have hreal (j : ℕ) : R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude b χout χsource β r))
        (fun z ↦ (u.val z).ofLp) x) := by
    apply (hR j).trans
    apply Eventually.of_forall
    intro x
    apply congrArg (WithLp.toLp 2)
    rw [← integral_cut_elapsedGraph_eq_retardedPhysical_of_support Ψ b χout χsource β Δ hΔ
      hΨ hb ho hs hβ hocs hscs (χ j) (hχ j) (hχcs j) a hout hzero u x]
    simp_rw [hecut]
  obtain ⟨s, hs', hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hsub, ae_all_iff.mpr hreal] with x hx he
  have ht := (integrable_and_tendsto_integral_uncut_elapsedGraph_of_bound Ψ b χout χsource β Δ hΔ
    hΨ hb ho hs hβ (Cβ 0)
    (fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hβbound 0 (by omega) ξ)
    hocs hscs C hC hbound u x).2
  rw [integral_uncut_elapsedGraph_eq_retardedPhysicalIntegral Ψ b χout χsource β Δ hΔ
    hΨ hb ho hs hβ Cβ hβbound hocs hscs C hC hbound a hout hzero u x] at ht
  have ht' := (PiLp.continuous_toLp 2 (fun _ : Fin q ↦ ℂ)).tendsto _ |>.comp ht
  exact tendsto_nhds_unique hx
    ((ht'.comp hs'.tendsto_atTop).congr (fun j ↦ (he (s j)).symm))

/-- Every pairing of the actual Hilbert adjoint is the pairing with the
original uncut physical retarded action. The scalar integrand is integrable,
by the proved L² realization, rather than assigned an undefined Bochner
integral. Consumer: rewriting this pairing as the literal reversed time
triangle in `app:ch_regular_base:lem:retarded-kernel`. This statement itself
retains the forward time integral; the triangle reversal is a separate step. -/
theorem retardedOperator_adjoint_pairing_uncutPhysicalIntegral
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℕ → ℝ)
    (hβbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ Cβ k)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
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
        (cutRetardedPhysical Ψ b χout χsource β (χ j) hs hβ (hχ j) (hχcs j) a u x)) ∧
      Tendsto R atTop (𝓝 (Q (graphTestToLp u)))) :
    Integrable (fun x ↦ inner ℂ
      (WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x)) (v.val x)) ∧
    inner ℂ (graphTestToLp u) (Q.adjoint (graphTestToLp v)) =
      ∫ x, inner ℂ (WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x)) (v.val x) := by
  have hreal := retardedOperator_eq_uncutPhysicalIntegral_of_strongLimit Ψ b χout χsource β Δ hΔ
    hΨ hb ho hs hβ Cβ hβbound hocs hscs C hC hbound χ hχ hχcs hcut a hout hzero Q u hstrong
  have he : (fun x ↦ inner ℂ (Q (graphTestToLp u) x) (graphTestToLp v x)) =ᵐ[volume]
      fun x ↦ inner ℂ (WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x))
        (v.val x) := by
    filter_upwards [hreal, (graphTest_memLp v).coeFn_toLp] with x hx hv
    rw [hx, show graphTestToLp v x = v.val x from hv]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (Q (graphTestToLp u)) (graphTestToLp v)).congr he, ?_⟩
  rw [Q.adjoint_inner_right, L2.inner_def]
  exact integral_congr_ae he

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
