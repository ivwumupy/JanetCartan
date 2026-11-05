module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongLocalization
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

/-!
# Localized limits of the actual elapsed operator and its adjoint

The finite forward/adjoint realizations are exactly the outputs of
`exists_fullGraphFamily_of_wholeImage_phase`. Supported primitive regularity
proves measurability, and the common LOW bound permits elapsed integration.
This deduction uses neither an integrated Sobolev estimate nor a fixed-time
zero-energy relation. The physical shell identification is a separate step.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Both localized strong limits concern one and the same bounded realization
of `elapsedGraphIntegral`. Its literal adjoint is obtained by adjunction of
that realization; the two outside localizers keep their order. All realization
inputs are finite test identities, the LOW bound and per-r strong limits from
`exists_fullGraphFamily_of_wholeImage_phase`. The parent must instantiate that
producer; `ActualOperator` connects the physical localizers and their shell
kernel to these bounded maps. Consumer: the unregularized
bound in `app:ch_regular:eq:chain-tail`, using
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_localized_elapsedGraphIntegral_limits
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    {C : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) :
    ∃ Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
      ‖Q‖ ≤ Δ * C ∧
      (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
      (∀ u, Q.adjoint u =
        ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
      (∀ u, (1 - Mo) (Q (Mi u)) =
        ∫ r in Icc 0 Δ, (1 - Mo) (elapsedGraph Ψ b χout χsource β r (Mi u))) ∧
      (∀ u, (1 - Mo) (Q.adjoint (Mi u)) =
        ∫ r in Icc 0 Δ, (1 - Mo) ((elapsedGraph Ψ b χout χsource β r).adjoint (Mi u))) ∧
      (∀ u, Tendsto (fun j ↦ ∫ r in Icc 0 Δ, (1 - Mo) (Treg j r (Mi u))) atTop
        (𝓝 ((1 - Mo) (Q (Mi u))))) ∧
      (∀ u, Tendsto (fun j ↦ ∫ r in Icc 0 Δ, (1 - Mo) ((Treg j r).adjoint (Mi u))) atTop
        (𝓝 ((1 - Mo) (Q.adjoint (Mi u))))) := by
  have hm := supported_elapsedGraph_measurability_and_integral_limits Ψ b χout χsource β
    Δ hΔ hΨ hb ho hs hβ hocs hscs χ hχ hχcs Treg hreal hrealAdj hbound hlim hlimAdj
  have hmreg := aestronglyMeasurable_supported_elapsed_regularizations Ψ b χout χsource β
    Δ hΔ hΨ hb ho hs hβ hocs hscs χ hχ hχcs Treg hreal hrealAdj
  have hC : 0 ≤ C := (norm_nonneg (Treg 0 0)).trans (hbound 0 0 ⟨le_rfl, hΔ⟩)
  have hT : ∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C := by
    intro r hr
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    apply le_of_tendsto (hlim r hr u).norm
    exact Eventually.of_forall (fun j ↦ (Treg j r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound j r hr) (norm_nonneg u)))
  let Q := strongIntegral (elapsedGraph Ψ b χout χsource β) Δ C hm.1 hT
  have hQA (u : SpacetimeL2 d q) : Q.adjoint u =
      ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u :=
    strongIntegral_adjoint_apply hm.1 hT hm.2.1 u
  refine ⟨Q, norm_strongIntegral_le hΔ hC hm.1 hT, fun _ ↦ rfl, hQA,
    localized_strongIntegral_apply Mi Mo hm.1 hT,
    localized_strongIntegral_adjoint_apply Mi Mo hm.1 hT hm.2.1, ?_, ?_⟩
  · exact tendsto_localized_regularized_strongIntegral Mi Mo hm.1 hT Treg
      (fun j u ↦ (hmreg j u).1) hbound hlim
  · intro u
    have h := (1 - Mo).continuous.continuousAt.tendsto.comp (hm.2.2.2 (Mi u))
    have he (j : ℕ) : (∫ r in Icc 0 Δ, (1 - Mo) ((Treg j r).adjoint (Mi u))) =
        (1 - Mo) (∫ r in Icc 0 Δ, (Treg j r).adjoint (Mi u)) := by
      apply (1 - Mo).integral_comp_comm
      apply integrableOn_apply_of_uniform_bound (C := C) (fun v ↦ (hmreg j v).2)
      intro r hr
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound j r hr
    simpa only [he, Function.comp_def, hQA] using h

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
