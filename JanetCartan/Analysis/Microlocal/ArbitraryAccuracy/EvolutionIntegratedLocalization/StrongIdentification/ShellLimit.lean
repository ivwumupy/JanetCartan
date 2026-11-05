module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.IntegratedFinite
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.PhysicalCutoffs

/-!
# Identifying the shell sum with the bounded elapsed strong limit

The finite kernel and the bounded operator have the same representatives.
Their diagonal limits agree almost everywhere by L² convergence. Absolute
summability is assumed only for the pointwise elapsed shell majorant produced
by `ShellSummation` and `UniformDecay`; there is no operator-tail premise.
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

/-- A cofinal sequence of finite graph/output kernels converges to the SAME
localized elapsed integral. `hreal` is the eventual finite prefix realization
obtained from `eventually_graphShell_prefix_eq_producer` (and its literal
adjoint variant). The pointwise summable majorant `C` is the precise remaining
quantitative input from `ShellSummation` / `UniformDecay`. This identification
does not assume the integrated Sobolev estimate
(`app:ch_regular_base:eq:fixed-time-representation`, `app:ch_regular:eq:chain-tail`). -/
theorem localized_elapsed_shells_ae_integral
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (Mi Mo : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hSs : ∀ r ∈ Icc 0 Δ, ∀ x ξ, ξ ≠ 0 →
      ContDiffAt ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (x, ξ))
    (hAs : ∀ r ∈ Icc 0 Δ, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (Treg : ℕ → ℝ → H →L[ℂ] H) (T : ℝ → H →L[ℂ] H)
    (hreal : ∀ᶠ N in atTop, ∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
      Treg (2 ^ N - 1) r (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun x y ξ ↦ ((∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ) : ℂ) •
            orientedElapsedAmplitude backward b χout χsource β r x y ξ)
          (fun y ↦ (u.val y).ofLp)) x))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    {B : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ B)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop (𝓝 (T r u)))
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (graphCutoff j) (outputCutoff k) x y‖ ≤ C (j, k))
    (u : graphTestSpace (d + 1) q) :
    (1 - Mo) (∫ r in Icc 0 Δ, T r (Mi (graphTestToLp u))) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (∫ y,
        (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
          mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec (u.val y).ofLp) := by
  let Ki := Prod.fst '' tsupport mi
  let Kη := Prod.snd '' tsupport mi
  have hiSupport (y η : E) (h : (y, η) ∉ Ki ×ˢ Kη) : mi (y, η) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact h ⟨⟨(y, η), hm, rfl⟩, ⟨(y, η), hm, rfl⟩⟩
  have hz (r : ℝ) (x z ξ : E) (h : (x, z) ∉ tsupport χout ×ˢ tsupport χsource) :
      orientedElapsedAmplitude backward b χout χsource β r x z ξ = 0 := by
    have he : elapsedAmplitude b χout χsource β r x z ξ = 0 := by
      apply elapsedAmplitude_eq_zero_of_mask
      by_cases hx : x ∈ tsupport χout
      · exact Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport (fun hz ↦ h ⟨hx, hz⟩)))
      · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)
    cases backward <;> simp [orientedElapsedAmplitude, he]
  let c := fun r j k ↦ physicalInputCarriers
    (cutoffPairCarriers (orientedElapsedAmplitude backward b χout χsource β r) mi
      (tsupport χout ×ˢ tsupport χsource) Ki Kη (hocs.prod hscs)
      (his.image continuous_fst) (his.image continuous_snd) (hz r) hiSupport j k) hρ
  let cp (r : ℝ) (N M : ℕ) : RegularizedCarriers
      (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun ξ ↦ ∑ j ∈ Finset.range N, graphCutoff j ξ)
      (physicalCutoff (2 ^ M - 1)) :=
    { RegularizedCarriers.finsetCutoffs (c r) (Finset.range N) (Finset.range (M + 1)) with
      compact_outputCutoff := physicalCutoff_hasCompactSupport (2 ^ M - 1) }
  let v (N : ℕ) : H := (1 - Mo) (multiplier (2 ^ N - 1)
    (∫ r in Icc 0 Δ, Treg (2 ^ N - 1) r (Mi (graphTestToLp u))))
  let f (N : ℕ) (x : E) := WithLp.toLp 2 (∫ y,
    (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (fun ξ ↦ ∑ j ∈ Finset.range N, graphCutoff j ξ)
      (fun ζ ↦ ∑ k ∈ Finset.range (N + 1), outputCutoff k ζ) x y).mulVec (u.val y).ofLp)
  have he : ∀ᶠ N in atTop, v N =ᵐ[volume] f N := by
    filter_upwards [hreal] with N hN
    simpa only [v, f, outputPrefix_eq_physicalCutoff] using
      bounded_elapsed_outputMultiplier_realization backward hρ Δ Ψ b χout χsource β mi mo
        hi ho hos Mi Mo hMi hMo hS hA hSs hAs
        (fun ξ ↦ ∑ j ∈ Finset.range N, graphCutoff j ξ) (2 ^ N - 1)
        (ContDiff.sum (fun j _ ↦ contDiff_graphCutoff j)) (zero_notMem_tsupport_graphPrefix N)
        (fun r ↦ cp r N N) (fun _ ↦ rfl) (fun _ ↦ rfl)
        (Treg (2 ^ N - 1)) hN (hm (2 ^ N - 1)) (hbound (2 ^ N - 1)) u
  have hv : Tendsto v atTop
      (𝓝 ((1 - Mo) (∫ r in Icc 0 Δ, T r (Mi (graphTestToLp u))))) :=
    tendsto_outputMultiplier_diagonal Mo _ _
      ((tendsto_integral_apply_of_uniform_bound Treg hm hbound hlim
        (Mi (graphTestToLp u))).comp tendsto_graphShell_producer_indices)
  apply ae_eq_of_strongLimit_of_representatives v _ f _ he hv
  apply Eventually.of_forall
  intro x
  have hf : Integrable (fun y ↦ (u.val y).ofLp) :=
    ((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous).integrable_of_hasCompactSupport
      (u.property.2.comp_left (g := WithLp.ofLp) rfl)
  have hkernel := tendsto_elapsedPhysicalShellKernel_test_cutoffs backward ρ Δ Ψ b
    χout χsource β mi mo graphCutoff outputCutoff hS hA hi.continuous ho
    (fun j ↦ (contDiff_graphCutoff j).continuous) (fun k ↦ (contDiff_outputCutoff k).continuous)
    c (fun _ _ _ ↦ rfl) C hs hb (fun y ↦ (u.val y).ofLp) hf x
  have hdiag : Tendsto (fun N : ℕ ↦ (Finset.range N, Finset.range (N + 1))) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_finset_range.prodMk (tendsto_finset_range.comp (tendsto_add_atTop_nat 1))
  simpa only [f, Function.comp_def] using
    (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (hkernel.comp hdiag)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
