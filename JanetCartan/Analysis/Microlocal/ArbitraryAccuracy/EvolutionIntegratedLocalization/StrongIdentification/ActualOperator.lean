module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ShellLimit
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.StrongLimits

/-!
# The summed elapsed kernel is the actual localized elapsed operator

Only the primitive producer's finite forward/adjoint realizations, common LOW
bound, orbit measurability and per-time strong limits are used. Both literal
orientations identify one bounded realization of `elapsedGraphIntegral`.
The quantitative shell majorant remains an explicit input to be discharged
by the parent using `ShellSummation` and `UniformDecay`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The physical elapsed shell sum represents the actual localized
`elapsedGraphIntegral`, and in reverse orientation the literal adjoint of
that SAME bounded integral. The localizers are constructed from the fixed
compact symbols. The graph family inputs are precisely finite test actions,
the uniform LOW bound, measurability and per-r strong limits; `hχeq` is the
cutoff identity exported by `exists_elapsedGraphFamily_of_primitive_phase`.

The only summation premise is the pointwise summable Frobenius majorant `C`
of the actual elapsed shells, whose producers are `ShellSummation` and
`UniformDecay`. Its instantiation and the final Sobolev estimate belong to the
parent task. No uncut test action, integrated Sobolev bound, or fixed-r
zero-energy stationary relation is assumed
(`app:ch_regular_base:eq:fixed-time-representation`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_localized_elapsedGraphIntegral_shell_identification
    {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : ∀ backward, Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hSs : ∀ r ∈ Icc 0 Δ, ∀ x ξ, ξ ≠ 0 →
      ContDiffAt ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (x, ξ))
    (hAs : ∀ backward r, r ∈ Icc 0 Δ → ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (F : Set E) (hF : IsClosed F) (hzero : (0 : E) ∉ F) (hβF : tsupport β ⊆ F)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (A : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (Treg : ℕ → ℝ → H →L[ℂ] H)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {B : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ B)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u))) :
    ∃ Mi Mo Q : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦
        WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ‖Q‖ ≤ Δ * B ∧
      (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
      (∀ u, Q.adjoint u =
        ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
      (∀ (backward : Bool) (u : H),
        Tendsto (fun p : ℕ × ℕ ↦ (1 - Mo) (multiplier (n := d + 1) (r := q) (2 ^ p.2 - 1)
          (∫ r in Icc 0 Δ,
            (if backward then (Treg (2 ^ p.1 - 1) r).adjoint else Treg (2 ^ p.1 - 1) r)
              (Mi u)))) atTop
          (𝓝 ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))))) ∧
      ∀ (backward : Bool) (C : ℕ × ℕ → ℝ), Summable C →
        (∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
          mi mo (graphCutoff j) (outputCutoff k) x y‖ ≤ C (j, k)) →
        ∀ u : graphTestSpace (d + 1) q,
          (1 - Mo) ((if backward then Q.adjoint else Q) (Mi (graphTestToLp u))) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (∫ y,
              (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
                mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec (u.val y).ofLp) := by
  have hLi := exists_bounded_physicalLocalizers (n := d + 1) (q := q) hρ mi hi.continuous his
  have hLo := exists_bounded_physicalLocalizers (n := d + 1) (q := q) hρ mo ho hos
  let Li : H →L[ℂ] H := hLi.choose
  let Mo : H →L[ℂ] H := hLo.choose
  have hMi := hLi.choose_spec.2
  have hMo := hLo.choose_spec.1
  have hmT (u : H) : AEStronglyMeasurable
      (fun r ↦ elapsedGraph Ψ b χout χsource β r u) (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ Treg j r u) (fun j ↦ hm j u)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlim r hr u
  have hmTA (u : H) : AEStronglyMeasurable
      (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun j r ↦ (Treg j r).adjoint u) (fun j ↦ hmAdj j u)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlimAdj r hr u
  have hB : 0 ≤ B := (norm_nonneg (Treg 0 0)).trans (hbound 0 0 ⟨le_rfl, hΔ⟩)
  have hT : ∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ B := by
    intro r hr
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro u
    apply le_of_tendsto (hlim r hr u).norm
    exact Eventually.of_forall (fun j ↦ (Treg j r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound j r hr) (norm_nonneg u)))
  let Q := strongIntegral (elapsedGraph Ψ b χout χsource β) Δ B hmT hT
  have hQA (u : H) : Q.adjoint u =
      ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u :=
    strongIntegral_adjoint_apply hmT hT hmTA u
  have hstrong (backward : Bool) (u : H) :
      Tendsto (fun p : ℕ × ℕ ↦ (1 - Mo) (multiplier (n := d + 1) (r := q) (2 ^ p.2 - 1)
        (∫ r in Icc 0 Δ,
          (if backward then (Treg (2 ^ p.1 - 1) r).adjoint else Treg (2 ^ p.1 - 1) r)
            (Li.adjoint u)))) atTop
        (𝓝 ((1 - Mo) ((if backward then Q.adjoint else Q) (Li.adjoint u)))) := by
    cases backward
    · simpa only [Bool.false_eq_true, ite_false, Q, strongIntegral_apply, Function.comp_def] using
        tendsto_outputMultiplier_independent Mo _ _
          ((tendsto_integral_apply_of_uniform_bound Treg hm hbound hlim (Li.adjoint u)).comp
            tendsto_graphShell_producer_indices)
    · have hba : ∀ j r, r ∈ Icc 0 Δ → ‖(Treg j r).adjoint‖ ≤ B := by
        intro j r hr
        simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound j r hr
      simpa only [ite_true, hQA, Function.comp_def] using
        tendsto_outputMultiplier_independent Mo _ _
          ((tendsto_integral_apply_of_uniform_bound (fun j r ↦ (Treg j r).adjoint)
            hmAdj hba hlimAdj (Li.adjoint u)).comp tendsto_graphShell_producer_indices)
  refine ⟨Li.adjoint, Mo, Q, hMi, hMo, norm_strongIntegral_le hΔ hB hmT hT,
    fun _ ↦ rfl, hQA, hstrong, ?_⟩
  intro backward C hs hb u
  have hsupport (r : ℝ) (x y ξ : E) (hξ : ξ ∉ F) :
      elapsedAmplitude b χout χsource β r x y ξ = 0 := by
    apply elapsedAmplitude_eq_zero_of_mask
    exact Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (hβF h))))
  have hpref : ∀ᶠ N in atTop, ∀ r ∈ Icc 0 Δ, ∀ v : graphTestSpace (d + 1) q,
      (if backward then (Treg (2 ^ N - 1) r).adjoint else Treg (2 ^ N - 1) r)
          (graphTestToLp v) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun x y ξ ↦ ((∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ) : ℂ) •
            orientedElapsedAmplitude backward b χout χsource β r x y ξ)
          (fun y ↦ (v.val y).ofLp)) x) := by
    cases backward
    · filter_upwards [eventually_graphShell_prefix_eq_producer hF hzero χ hχeq] with N hN
      intro r hr v
      have he := hN (elapsedAmplitude b χout χsource β r) (hsupport r)
      have hv := hreal (2 ^ N - 1) r hr v
      rw [← he] at hv
      delta graphTestOutput frequencyCutFullAmplitude at hv
      simpa only [Bool.false_eq_true, ite_false, orientedElapsedAmplitude] using hv
    · filter_upwards [eventually_graphShell_prefix_eq_producer_adjoint hF hzero χ hχeq] with N hN
      intro r hr v
      have he := hN (elapsedAmplitude b χout χsource β r) (hsupport r)
      have hv := hrealAdj (2 ^ N - 1) r hr v
      rw [← he] at hv
      delta frequencyCutFullAmplitude at hv
      simpa only [ite_true, orientedElapsedAmplitude] using hv
  have hmo : ∀ j v, AEStronglyMeasurable
      (fun r ↦ (if backward then (Treg j r).adjoint else Treg j r) v)
      (volume.restrict (Icc 0 Δ)) := by
    cases backward
    · exact hm
    · exact hmAdj
  have hbo : ∀ j r, r ∈ Icc 0 Δ →
      ‖if backward then (Treg j r).adjoint else Treg j r‖ ≤ B := by
    cases backward
    · exact hbound
    · simpa only [ite_true, ContinuousLinearMap.adjoint.norm_map] using hbound
  have hlo : ∀ r ∈ Icc 0 Δ, ∀ v,
      Tendsto (fun j ↦ (if backward then (Treg j r).adjoint else Treg j r) v) atTop
        (𝓝 ((if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
          else elapsedGraph Ψ b χout χsource β r) v)) := by
    cases backward
    · exact hlim
    · exact hlimAdj
  have he := localized_elapsed_shells_ae_integral backward hρ Δ Ψ b χout χsource β mi mo
    hi ho his hos hocs hscs Li.adjoint Mo hMi hMo hS (hA backward) hSs (hAs backward)
    (fun j r ↦ if backward then (Treg j r).adjoint else Treg j r)
    (fun r ↦ if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
      else elapsedGraph Ψ b χout χsource β r)
    hpref hmo hbo hlo C hs hb u
  cases backward
  · simpa only [Bool.false_eq_true, ite_false, Q, strongIntegral_apply] using he
  · simpa only [ite_true, hQA] using he

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
