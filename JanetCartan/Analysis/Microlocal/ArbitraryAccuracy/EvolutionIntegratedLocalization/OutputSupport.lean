module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.CompactKernels
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Removing the auxiliary output cutoff from the same elapsed operator

The finite test realizations retain the original physical masks. Density and
the actual per-time strong limits transfer those masks to both orientations
of the bounded graph. Bounded elapsed integration and the literal left
localizer then preserve a fixed cutoff covering their physical supports.
This closes the support step of `app:ch_regular:eq:chain-tail` without making
a false compact-support assertion about finite output-frequency kernels.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits LowBounds LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Choose one physical output cutoff for a finite family, before elapsed
time, frequency, derivative order or accuracy. Its plateau covers both
original masks and each complementary localizer's base carrier, including
the identity contribution. Consumer: the Sobolev realization and its cutoff
removal (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_finiteFamily_elapsed_output_cutoff {α : Type*} [Finite α]
    (χout χsource : α → E → ℂ) (mo : α → LocalizerSymbol (d + 1))
    (hout : ∀ a, HasCompactSupport (χout a)) (hsource : ∀ a, HasCompactSupport (χsource a))
    (hmo : ∀ a, HasCompactSupport (mo a)) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧
      (∀ a (backward : Bool) x, x ∈ (if backward then tsupport (χsource a) else tsupport (χout a)) →
        ψ x = 1) ∧ ∀ a, ∀ x ∈ Prod.fst '' tsupport (mo a), ψ x = 1 := by
  let K := ⋃ a, (tsupport (χout a) ∪ tsupport (χsource a)) ∪ Prod.fst '' tsupport (mo a)
  have hK : IsCompact K := isCompact_iUnion (fun a ↦
    ((hout a).union (hsource a)).union ((hmo a).image continuous_fst))
  obtain ⟨ψ, hψ, hrange, hsψ, _, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK isOpen_univ (subset_univ K)
  refine ⟨ψ, hψ, hsψ, ?_, ?_, ?_⟩
  · intro x
    rw [Real.norm_of_nonneg (hrange x).1]
    exact (hrange x).2
  · intro a backward x hx
    change x ∈ {ξ | ψ ξ = 1}
    apply interior_subset (hplateau (mem_iUnion.mpr ⟨a, ?_⟩))
    cases backward
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
  · intro a x hx
    change x ∈ {ξ | ψ ξ = 1}
    exact interior_subset (hplateau (mem_iUnion.mpr ⟨a, Or.inr hx⟩))

private theorem sourceCutMultiplier_eq_of_test_support
    (ψ : E → ℝ) (hψ : Continuous ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (T : H →L[ℂ] H) (F : graphTestSpace (d + 1) q → E → EuclideanSpace ℂ (Fin q))
    (he : ∀ u, T (graphTestToLp u) =ᵐ[volume] F u)
    (hs : ∀ u x, ψ x ≠ 1 → F u x = 0) (u : H) :
    sourceCutMultiplier ψ hψ hψb (T u) = T u := by
  have heq : (sourceCutMultiplier ψ hψ hψb).comp T = T := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer
      ((sourceCutMultiplier ψ hψ hψb).comp T).continuous T.continuous
    funext v
    apply Lp.ext
    filter_upwards [sourceCutMultiplier_coeFn ψ hψ hψb (T (graphTestToLp v)), he v]
      with x hx hv
    change sourceCutMultiplier ψ hψ hψb (T (graphTestToLp v)) x = T (graphTestToLp v) x
    rw [hx, hv]
    by_cases hp : ψ x = 1
    · simp only [hp, Complex.ofReal_one, one_smul]
    · simp only [hs v x hp, smul_zero]
  exact congrArg (fun A : H →L[ℂ] H ↦ A u) heq

/-- The exact finite realizations and their per-time strong limits recover
the original output mask, or the original source mask for the literal
adjoint. No integrated tail or uncut test representation is assumed.
Consumer: removal of the fixed Sobolev cutoff (`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem sourceCutMultiplier_orientedElapsedGraph_eq
    (backward : Bool) (r : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (ψ : E → ℝ)
    (hψ : Continuous ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hplateau : ∀ x, x ∈ (if backward then tsupport χsource else tsupport χout) → ψ x = 1)
    (χ : ℕ → E → ℂ) (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace (d + 1) q), Treg j (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ r) (frequencyCutFullAmplitude (χ j)
        (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j (u : graphTestSpace (d + 1) q), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
      fun z ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
          (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
        (fun x ↦ (u.val x).ofLp) z))
    (hlim : ∀ u, Tendsto (fun j ↦ (if backward then (Treg j).adjoint else Treg j) u) atTop
      (𝓝 ((if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
        else elapsedGraph Ψ b χout χsource β r) u))) (u : H) :
    sourceCutMultiplier ψ hψ hψb
      ((if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
        else elapsedGraph Ψ b χout χsource β r) u) =
      (if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
        else elapsedGraph Ψ b χout χsource β r) u := by
  have he (j : ℕ) (v : H) : sourceCutMultiplier ψ hψ hψb
      ((if backward then (Treg j).adjoint else Treg j) v) =
        (if backward then (Treg j).adjoint else Treg j) v := by
    cases backward
    · apply sourceCutMultiplier_eq_of_test_support ψ hψ hψb (Treg j) _ (hreal j) _ v
      intro w x hx
      have hz : χout x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs ↦ hx (hplateau x hs))
      simp [graphTestOutput, graphOperator, frequencyCutFullAmplitude, elapsedAmplitude, hz]
    · apply sourceCutMultiplier_eq_of_test_support ψ hψ hψb (Treg j).adjoint _ (hrealAdj j) _ v
      intro w x hx
      have hz : χsource x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs ↦ hx (hplateau x hs))
      simp [reverseGraphOperator, frequencyCutFullAmplitude, elapsedAmplitude, hz]
  exact tendsto_nhds_unique
    (((sourceCutMultiplier ψ hψ hψb).continuous.tendsto _).comp (hlim u))
    ((hlim u).congr' (Eventually.of_forall (fun j ↦ (he j u).symm)))

/-- The bounded left localizer has its literal symbol's physical base
support on every L² input. The exact L¹ realization is the one already
exported by `exists_bounded_physicalLocalizers`; density supplies all inputs
(`app:ch_regular:eq:chain-tail`). -/
theorem sourceCutMultiplier_leftLocalizer_eq
    (ρ : ℝ) (mo : LocalizerSymbol (d + 1)) (Mo : H →L[ℂ] H)
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (ψ : E → ℝ) (hψ : Continuous ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hplateau : ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1) (u : H) :
    sourceCutMultiplier ψ hψ hψb (Mo u) = Mo u := by
  apply sourceCutMultiplier_eq_of_test_support ψ hψ hψb Mo
    (fun v x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (graphTestToLp v y).ofLp) x)) _ _ u
  · intro v
    apply hMo
    intro i
    apply ((graphTestToSchwartz v).integrable.eval i).congr
    filter_upwards [(graphTest_memLp v).coeFn_toLp] with y hy
    exact (congrArg (fun z : EuclideanSpace ℂ (Fin q) ↦ z i) hy).symm
  · intro v x hx
    have hz : ∀ ξ, mo (x, ξ) = 0 := fun ξ ↦ image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (hplateau x ⟨(x, ξ), h, rfl⟩))
    simp [leftLocalizer, graphOperator, hz]

/-- A cutoff covering the graph's actual output and the left symbol's base
support fixes the complete localized strong integral, with the identity in
`1 - Mo` and the outside right localizer intact. The per-time support premise
is produced by `sourceCutMultiplier_orientedElapsedGraph_eq`, from finite
realizations and actual strong limits; measurability and LOW bounds are the
graph producer's original outputs (`app:ch_regular:eq:chain-tail`). -/
theorem sourceCutMultiplier_localized_strongIntegral_eq
    (T : ℝ → H →L[ℂ] H) (Δ B : ℝ)
    (hm : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hb : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ B)
    (Mi Mo : H →L[ℂ] H) (ρ : ℝ) (mo : LocalizerSymbol (d + 1))
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (ψ : E → ℝ) (hψ : Continuous ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hplateau : ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1)
    (hT : ∀ r ∈ Icc 0 Δ, ∀ u, sourceCutMultiplier ψ hψ hψb (T r u) = T r u)
    (u : H) :
    sourceCutMultiplier ψ hψ hψb ((1 - Mo) (strongIntegral T Δ B hm hb (Mi u))) =
      (1 - Mo) (strongIntegral T Δ B hm hb (Mi u)) := by
  have hQ : sourceCutMultiplier ψ hψ hψb (strongIntegral T Δ B hm hb (Mi u)) =
      strongIntegral T Δ B hm hb (Mi u) := by
    rw [strongIntegral_apply, ← (sourceCutMultiplier ψ hψ hψb).integral_comp_comm
      (integrableOn_apply_of_uniform_bound hm hb (Mi u))]
    exact setIntegral_congr_fun measurableSet_Icc (fun r hr ↦ hT r hr (Mi u))
  simp only [sub_apply, one_apply_eq_self, map_sub, hQ,
    sourceCutMultiplier_leftLocalizer_eq ρ mo Mo hMo ψ hψ hψb hplateau]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
