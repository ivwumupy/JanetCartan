module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.BoundedLocalizers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ContinuousInputs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.TestOutputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.OutputMultipliers

/-!
# Finite graph realizations with both physical localizers

The maps representing the proof symbols are constructed from their compact
supports. Compact-kernel uniqueness extends the primitive finite test action
to the right-localized datum. The left map then gives the actual complementary
output, in either literal graph orientation. This is the finite graph stage
of `app:ch_regular:eq:chain-tail`. The independent output regularization is
identified with the contractive Fourier multiplier; `IntegratedFinite`
then passes this identity through elapsed integration.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits LowBounds.FrequencyCutoff
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem graphOperator_eq_of_ae_input
    (S : E → E → ℝ) (A : FullAmplitude n q) {f g : E → Fin q → ℂ}
    (h : f =ᵐ[volume] g) : graphOperator S A f = graphOperator S A g := by
  funext x
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- For a finite graph frequency cutoff, the physical leakage is the actual
bounded localized graph on tests. The same two bounded localizers work for every finite graph;
the only graph realization premise is the primitive finite test identity.
The reverse orientation uses its supplied literal amplitude without moving
either position. Consumer: elapsed integration and output-cutoff recovery
for `app:ch_regular:eq:chain-tail`. -/
theorem exists_bounded_localized_finiteGraph_realization
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
      ∀ (χA χo : E → ℝ), ContDiff ℝ ∞ χA → (0 : E) ∉ tsupport χA →
      RegularizedCarriers A (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA χo →
      ∀ (T : H →L[ℂ] H),
      (∀ u : graphTestSpace n q, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
          S (fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ) (fun y ↦ (u.val y).ofLp)) x)) →
      ∀ u : graphTestSpace n q, (1 - Mo) (T (Mi (graphTestToLp u))) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2
          (((if backward then reverseLeakage else forwardLeakage)
            S (fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ) ρ mi mo
            (fun y ↦ (u.val y).ofLp)) x) := by
  obtain ⟨Li, _, hRi⟩ := exists_bounded_physicalLocalizers (q := q) hρ mi hi.continuous his
  obtain ⟨Mo, hMo, _⟩ := exists_bounded_physicalLocalizers (q := q) hρ mo ho hos
  refine ⟨Li.adjoint, Mo, hRi, hMo, ?_⟩
  intro backward S A hSc hS hA χA χo hχ hχ0 c T hreal u
  let f : E → Fin q → ℂ := fun y ↦ (u.val y).ofLp
  let v := rightLocalizer ρ mi f
  let B : FullAmplitude n q := fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ
  let g := (if backward then reverseGraphOperator else graphOperator) S B v
  have hf : ContDiff ℝ ∞ f :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).contDiff.comp u.property.1
  have hi' : ContDiff ℝ ∞ (fun p : E × E ↦ mi (p.1, ρ⁻¹ • p.2)) :=
    hi.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hv : ContDiff ℝ ∞ v := by
    simpa only [v, rightLocalizer, inv_one, one_smul] using
      contDiff_rightLocalizer A _ χA χo c hi' f hf
  have hiv : Li.adjoint (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x) := by
    have he : (fun y ↦ ((graphTestToLp u) y).ofLp) =ᵐ[volume] f := by
      filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
      exact congrArg WithLp.ofLp hy
    have hr := graphOperator_eq_of_ae_input (fun x ξ : E ↦ inner ℝ x ξ)
      (fun _ y η ↦ (mi (y, ρ⁻¹ • η) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)) he
    exact (hRi (graphTestToLp u)).trans (Eventually.of_forall (fun x ↦
      congrArg (fun w : E → Fin q → ℂ ↦ WithLp.toLp 2 (w x)) hr))
  have hB : Continuous (fun p : (E × E) × E ↦ B p.1.1 p.1.2 p.2) :=
    (Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_snd)).smul hA.continuous
  have hBs : HasCompactSupport (fun p : (E × E) × E ↦ B p.1.1 p.1.2 p.2) := by
    apply HasCompactSupport.intro (c.compact_amplitudeBase.prod c.compact_graphCutoff)
    intro p hp
    by_cases hb : p.1 ∈ c.amplitudeBase
    · have hξ : p.2 ∉ tsupport χA := fun hξ ↦ hp ⟨hb, hξ⟩
      simp [B, image_eq_zero_of_notMem_tsupport hξ]
    · simp [B, c.amplitude_zero _ _ _ hb]
  have hTg : T (Li.adjoint (graphTestToLp u)) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (g x) :=
    compactOrientedGraph_test_realization_on_continuous_input backward S B hSc hB hBs T
      hreal _ v hv.continuous hiv
  have hg : ContDiff ℝ ∞ g := by
    cases backward
    · exact contDiff_regularizedGraph S A _ χA χo c hS hA hχ hχ0 v hv
    · exact contDiff_regularizedReverseGraph S A _ χA χo c hS hA hχ hχ0 v hv
  have hgs : HasCompactSupport g := by
    cases backward
    · exact regularizedGraph_hasCompactSupport S A _ χA χo c v
    · exact regularizedReverseGraph_hasCompactSupport S A _ χA χo c v
  have hiT (i : Fin q) : Integrable (fun y ↦ T (Li.adjoint (graphTestToLp u)) y i) := by
    apply ((continuous_apply i).comp hg.continuous).integrable_of_hasCompactSupport
      (hgs.comp_left (g := fun w ↦ w i) rfl) |>.congr
    filter_upwards [hTg] with y hy
    exact (congrArg (fun w : EuclideanSpace ℂ (Fin q) ↦ w i) hy).symm
  have heT : (fun y ↦ (T (Li.adjoint (graphTestToLp u)) y).ofLp) =ᵐ[volume] g := by
    filter_upwards [hTg] with y hy
    exact congrArg WithLp.ofLp hy
  have hleft := graphOperator_eq_of_ae_input (fun x ξ : E ↦ inner ℝ x ξ)
    (fun x _ ζ ↦ (mo (x, ρ⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)) heT
  have hMoT := hMo (T (Li.adjoint (graphTestToLp u))) hiT
  filter_upwards [Lp.coeFn_sub (T (Li.adjoint (graphTestToLp u)))
    (Mo (T (Li.adjoint (graphTestToLp u)))), hTg, hMoT] with x hx ht hm
  change (T (Li.adjoint (graphTestToLp u)) - Mo (T (Li.adjoint (graphTestToLp u)))) x = _
  rw [hx, Pi.sub_apply, ht, hm]
  have he := congrFun hleft x
  change leftLocalizer ρ mo _ x = leftLocalizer ρ mo g x at he
  rw [he]
  cases backward <;> rfl


/-- Each finite joint kernel is represented by the same bounded input and
output localizers and the independent contractive Fourier output cutoff.
The graph realization is required only on the primitive test space; the
extension to the right-localized input is proved. This is the finite L²
identity used before elapsed integration in
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular:eq:chain-tail`. -/
theorem bounded_finiteGraph_outputMultiplier_realization
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi mo : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo) (hos : HasCompactSupport mo)
    (Mi Mo : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (backward : Bool) (S : E → E → ℝ) (A : FullAmplitude n q)
    (hSc : Continuous (Function.uncurry S))
    (hS : ∀ x ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    (χA : E → ℝ) (j : ℕ) (hχ : ContDiff ℝ ∞ χA) (hχ0 : (0 : E) ∉ tsupport χA)
    (c : RegularizedCarriers A (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA
      (LowBounds.FrequencyCutoff.physicalCutoff j))
    (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n q, T (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        S (fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ) (fun y ↦ (u.val y).ofLp)) x))
    (u : graphTestSpace n q) :
    (1 - Mo) (LowBounds.FrequencyCutoff.multiplier j (T (Mi (graphTestToLp u)))) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (∫ y,
        (regularizedJointKernel backward S A
          (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          χA (LowBounds.FrequencyCutoff.physicalCutoff j) x y).mulVec (u.val y).ofLp) := by
  let χo : E → ℝ := LowBounds.FrequencyCutoff.physicalCutoff j
  let f : E → Fin q → ℂ := fun y ↦ (u.val y).ofLp
  let v := rightLocalizer ρ mi f
  let B : FullAmplitude n q := fun x y ξ ↦ (χA ξ : ℂ) • A x y ξ
  let g := (if backward then reverseGraphOperator else graphOperator) S B v
  have hf : ContDiff ℝ ∞ f :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).contDiff.comp u.property.1
  have hi' : ContDiff ℝ ∞ (fun p : E × E ↦ mi (p.1, ρ⁻¹ • p.2)) :=
    hi.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hv : ContDiff ℝ ∞ v := by
    simpa only [v, rightLocalizer, inv_one, one_smul] using
      contDiff_rightLocalizer A _ χA χo c hi' f hf
  have hiv : Mi (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x) := by
    have he : (fun y ↦ ((graphTestToLp u) y).ofLp) =ᵐ[volume] f := by
      filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
      exact congrArg WithLp.ofLp hy
    have hr := graphOperator_eq_of_ae_input (fun x ξ : E ↦ inner ℝ x ξ)
      (fun _ y η ↦ (mi (y, ρ⁻¹ • η) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)) he
    exact (hMi (graphTestToLp u)).trans (Eventually.of_forall (fun x ↦
      congrArg (fun w : E → Fin q → ℂ ↦ WithLp.toLp 2 (w x)) hr))
  have hB : Continuous (fun p : (E × E) × E ↦ B p.1.1 p.1.2 p.2) :=
    (Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_snd)).smul hA.continuous
  have hBs : HasCompactSupport (fun p : (E × E) × E ↦ B p.1.1 p.1.2 p.2) := by
    apply HasCompactSupport.intro (c.compact_amplitudeBase.prod c.compact_graphCutoff)
    intro p hp
    by_cases hb : p.1 ∈ c.amplitudeBase
    · have hξ : p.2 ∉ tsupport χA := fun hξ ↦ hp ⟨hb, hξ⟩
      simp [B, image_eq_zero_of_notMem_tsupport hξ]
    · simp [B, c.amplitude_zero _ _ _ hb]
  have hTg : T (Mi (graphTestToLp u)) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (g x) :=
    compactOrientedGraph_test_realization_on_continuous_input backward S B hSc hB hBs T
      hreal _ v hv.continuous hiv
  have hg : ContDiff ℝ ∞ g := by
    cases backward
    · exact contDiff_regularizedGraph S A _ χA χo c hS hA hχ hχ0 v hv
    · exact contDiff_regularizedReverseGraph S A _ χA χo c hS hA hχ hχ0 v hv
  have hgs : HasCompactSupport g := by
    cases backward
    · exact regularizedGraph_hasCompactSupport S A _ χA χo c v
    · exact regularizedReverseGraph_hasCompactSupport S A _ χA χo c v
  let w := hgs.toSchwartzMap hg
  have heT : T (Mi (graphTestToLp u)) = schwartzVectorToLp w :=
    Lp.ext (hTg.trans (schwartzVectorToLp_ae w).symm)
  rw [heT]
  refine (bounded_outputMultiplier_schwartz_realization hρ mo ho hos Mo hMo j w).trans ?_
  apply Eventually.of_forall
  intro x
  apply congrArg (WithLp.toLp 2)
  change leftLocalizer ρ (fun p ↦ χo (ρ • p.2) * (1 - mo p)) g x = _
  cases backward
  · exact forward_composition_scaled_eq_jointKernel S A ρ mi mo χA χo hSc hA.continuous
      hi.continuous ho hχ.continuous (LowBounds.FrequencyCutoff.physicalCutoff_contDiff j).continuous
      c f hf.continuous x hρ
  · exact reverse_composition_scaled_eq_jointKernel S A ρ mi mo χA χo hSc hA.continuous
      hi.continuous ho hχ.continuous (LowBounds.FrequencyCutoff.physicalCutoff_contDiff j).continuous
      c f hf.continuous x hρ

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
