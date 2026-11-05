module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.LocalizedFinite

/-!
# Output cutoff recovery for the bounded finite graph

Fourier inversion removes the independent output regularizer and recovers the
same bounded localized graph constructed from the finite test realization.
The identity term is retained. This deduction concerns each finite graph
cutoff; `IntegratedFinite` handles elapsed integration through the bounded
Fourier output multipliers.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- One pair of constructed bounded localizers identifies all finite graph
output-cutoff limits. The finite graph can be forward or the literal adjoint,
and the graph cutoff remains fixed while the independent output cutoff is
removed. `PhysicalShells` supplies the bounded output partial sums, including
their zeroth ball. No operator tail estimate or uncut test action is assumed.
Consumer: identification of the elapsed shell sum in
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular:eq:chain-tail`. -/
theorem exists_bounded_finiteGraph_outputCutoff_limits
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo) :
    ∃ Mi Mo : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦
        WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume] fun x ↦
        WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ∀ (backward : Bool) (S : E → E → ℝ) (A : FullAmplitude n q),
      Continuous (Function.uncurry S) →
      (∀ x ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, ξ)) →
      ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) →
      ∀ (χA : E → ℝ) (χo : ℕ → E → ℝ), ContDiff ℝ ∞ χA → (0 : E) ∉ tsupport χA →
      (∀ k, RegularizedCarriers A (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA (χo k)) →
      (∀ k, Continuous (χo k)) → (∀ k ξ, |χo k ξ| ≤ 1) →
      (∀ ξ, Tendsto (fun k ↦ χo k ξ) atTop (𝓝 1)) →
      ∀ (T : H →L[ℂ] H),
      (∀ u : graphTestSpace n q, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
          S (fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ) (fun y ↦ (u.val y).ofLp)) x)) →
      ∀ u : graphTestSpace n q, ∀ᵐ x ∂volume,
        Tendsto (fun k ↦ WithLp.toLp 2 (∫ y,
          (regularizedJointKernel backward S A
            (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
            χA (χo k) x y).mulVec (u.val y).ofLp)) atTop
          (𝓝 (((1 - Mo) (T (Mi (graphTestToLp u)))) x)) := by
  obtain ⟨Mi, Mo, hMi, hMo, hfinite⟩ :=
    exists_bounded_localized_finiteGraph_realization (q := q) hρ mi mo hi ho his hos
  refine ⟨Mi, Mo, hMi, hMo, ?_⟩
  intro backward S A hSc hS hA χA χo hχ hχ0 c hχo hχob hχolim T hreal u
  have hi' : ContDiff ℝ ∞ (fun p : E × E ↦ mi (p.1, ρ⁻¹ • p.2)) :=
    hi.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have ho' : Continuous (fun p : E × E ↦ mo (p.1, ρ⁻¹ • p.2)) :=
    ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))
  obtain ⟨B, hB⟩ := hos.exists_bound_of_continuous ho
  have hb (x ξ : E) : |mo (x, ρ⁻¹ • ξ)| ≤ B := by simpa using hB (x, ρ⁻¹ • ξ)
  have ht : IsCompact (Prod.fst '' tsupport mo) := hos.image continuous_fst
  have hmt (x : E) (hx : x ∉ Prod.fst '' tsupport mo) (ξ : E) :
      mo (x, ρ⁻¹ • ξ) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx ⟨(x, ρ⁻¹ • ξ), h, rfl⟩)
  have hf : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).contDiff.comp u.property.1
  have he := hfinite backward S A hSc hS hA χA (χo 0) hχ hχ0 (c 0) T hreal u
  filter_upwards [he] with x hx
  rw [hx]
  apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
  cases backward
  · simpa only [Bool.false_eq_true, ite_false, forwardLeakage, rightLocalizer,
      leftLocalizer, inv_one, one_smul] using
      (tendsto_forwardJointKernel_outputCutoff S A _ _ χA χo c hSc hS hA hi' ho'
        hχ hχ0 hχo hχob hχolim B hb _ ht hmt _ hf).1 x
  · simpa only [ite_true, reverseLeakage, rightLocalizer, leftLocalizer, inv_one, one_smul] using
      (tendsto_reverseJointKernel_outputCutoff S A _ _ χA χo c hSc hS hA hi' ho'
        hχ hχ0 hχo hχob hχolim B hb _ ht hmt _ hf).1 x

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
