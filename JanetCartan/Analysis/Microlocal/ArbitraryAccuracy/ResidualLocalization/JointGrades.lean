module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.AmplitudeGrades
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Profiles

/-!
# Primitive joint grades of the complete residual amplitudes

The consumer is the `hab` input of
`exists_directResidual_integral_fourier_bound_of_joint_grades`.
The two physical masks, multiplier, original two-time symbol, input proof mask,
both dyadic cutoffs and elapsed extension cutoff are multiplied here. The
dyadic derivative estimates are proved by `PhysicalShells.Profiles`; only the
original symbol and mask grades remain inputs from `RegularSector` and the
protected-mask construction. Literal adjunction retains both amplitude bases.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual
open FiniteChain.Graph KernelEstimates PhysicalShells PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
open RegularSector.Characteristic.EvolutionIntegral EvolutionIntegratedLocalization
open FiniteChain.Retarded.KernelDecay
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local fun_prop] ContDiff.inner

/-- The original normalized two-time phase grades give a uniform joint
gradient profile on compact physical bases. The fixed quadratic Fourier
phase contributes only a compact seminorm, independently of the coefficient
scale and requested accuracy. Consumer: `hp` in the integrated residual
leakage estimate (`app:ch_regular:eq:high-phase`,
`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_residual_joint_phase_profile
    {X Y : Set E} {K : Set V} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (P₀ : ℕ → ℝ) (hP₀ : ∀ j, 0 ≤ P₀ j) :
    ∃ P : ℕ → ℝ, (∀ j, 0 ≤ P j) ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ (Ψ : TwoTimePhase d),
    ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ) →
    ∀ (backward : Bool) x, x ∈ X → ∀ y, y ∈ Y → ∀ p, p ∈ K →
    (∀ j, ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase Ψ))
      (elapsedJointCoordinates p)‖ ≤ P₀ j * L ^ j) →
    ∀ j, ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ x y)) p‖ ≤
      P j * L ^ j := by
  let F (backward : Bool) (t : (E × E) × V) :=
    jointElapsedPhase backward (fun _ _ _ _ ↦ 0) t.1.1 t.1.2 t.2
  have hF (backward : Bool) : ContDiff ℝ ∞ (F backward) := by
    unfold F jointElapsedPhase jointPhase forwardPhase reversePhase elapsedPhase
    cases backward <;>
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> fun_prop
  let Q (backward : Bool) (j : ℕ) := cNorm ((X ×ˢ Y) ×ˢ K) (j + 1) (F backward)
  have hQ (b : Bool) (j : ℕ) : 0 ≤ Q b j := cNorm_nonneg _ _ _
  refine ⟨fun j ↦ P₀ j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1) +
      Q false j + Q true j,
    fun j ↦ add_nonneg (add_nonneg (mul_nonneg (hP₀ j) (pow_nonneg (norm_nonneg _) _))
      (hQ false j)) (hQ true j), ?_⟩
  intro L hL Ψ hΨ backward x hx y hy p hp hb j
  let π : V →L[ℝ] (E × E) × V := ContinuousLinearMap.inr ℝ _ _
  have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by intro p; simp [π])
  let a : (E × E) × V := ((x, y), 0)
  let f := fun t ↦ F backward (a + t)
  have hf : ContDiff ℝ ∞ f := (hF backward).comp (contDiff_const.add contDiff_id)
  have he : f ∘ π = jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y := by
    funext p
    simp [f, F, a, π]
  have hpoly (k : ℕ) :
      ‖iteratedFDeriv ℝ k (jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y) p‖ ≤
        cNorm ((X ×ˢ Y) ×ˢ K) k (F backward) := by
    rw [← he, π.iteratedFDeriv_comp_right hf p (by simp)]
    apply ((iteratedFDeriv ℝ k f (π p)).norm_compContinuousLinearMap_le (fun _ ↦ π)).trans
    simp only [Finset.prod_const, Finset.card_univ]
    apply (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hπ)
      (norm_nonneg _)).trans
    rw [mul_one]
    dsimp only [f]
    rw [iteratedFDeriv_comp_add_left]
    apply norm_iteratedFDeriv_le_cNorm ((hX.prod hY).prod hK)
      ((hF backward).of_le (by simp)) ?_ le_rfl
    simpa only [a, π, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
      using (show ((x, y), p) ∈ (X ×ˢ Y) ×ˢ K from ⟨⟨hx, hy⟩, hp⟩)
  -- Use the same linear pullback as PhaseGrades, with the uniform polynomial bound.
  let g := SymbolBudgets.jointPhase Ψ ∘ elapsedJointCoordinates (d := d)
  have hg : ContDiff ℝ ∞ g := hΨ.comp (elapsedJointCoordinates (d := d)).contDiff
  have hgb : ‖iteratedFDeriv ℝ (j + 1) g p‖ ≤
      (P₀ j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1)) * L ^ j := by
    dsimp only [g]
    rw [(elapsedJointCoordinates (d := d)).iteratedFDeriv_comp_right hΨ p (by simp)]
    apply ((iteratedFDeriv ℝ (j + 1) (SymbolBudgets.jointPhase Ψ)
      (elapsedJointCoordinates p)).norm_compContinuousLinearMap_le (fun _ ↦ elapsedJointCoordinates)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hh := hb j
    rw [norm_iteratedFDeriv_fderiv] at hh
    exact (mul_le_mul_of_nonneg_right hh (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
  have hqb : ‖iteratedFDeriv ℝ (j + 1)
      (jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y) p‖ ≤
      (Q false j + Q true j) * L ^ j := by
    apply (hpoly (j + 1)).trans
    apply le_trans (b := Q false j + Q true j)
    · cases backward
      · exact le_add_of_nonneg_right (hQ true j)
      · exact le_add_of_nonneg_left (hQ false j)
    · exact le_mul_of_one_le_right (add_nonneg (hQ false j) (hQ true j)) (one_le_pow₀ hL)
  have hsplit : jointElapsedPhase backward Ψ x y =
      (if backward then -g else g) + jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y := by
    funext p
    cases backward <;>
      simp only [jointElapsedPhase, jointPhase, Bool.false_eq_true, ↓reduceIte,
        forwardPhase, reversePhase, elapsedPhase, Pi.add_apply, Pi.neg_apply,
        g, Function.comp_apply, SymbolBudgets.jointPhase, elapsedJointCoordinates,
        LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] <;> ring
  have hsg : ContDiff ℝ ∞ (if backward then -g else g) := by
    cases backward
    · exact hg
    · exact hg.neg
  have hsgb : ‖iteratedFDeriv ℝ (j + 1) (if backward then -g else g) p‖ ≤
      (P₀ j * ‖elapsedJointCoordinates (d := d)‖ ^ (j + 1)) * L ^ j := by
    cases backward
    · exact hgb
    · simpa only [↓reduceIte, iteratedFDeriv_neg_apply, norm_neg] using hgb
  rw [norm_iteratedFDeriv_fderiv, hsplit,
    iteratedFDeriv_add_apply (hsg.contDiffAt.of_le (by simp))
      ((contDiff_jointElapsedPhase_zero backward x y).contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add hsgb hqb).trans_eq (by ring))

/-- Primitive symbol and mask grades produce the full cut joint amplitude
profile for either direct residual branch and its literal adjoint. The
offset and profile are chosen before frequency, coefficient scale, branch,
orientation and shell indices. Negative order is retained as `ρ ^ s`.
Consumer: `hab` in the integrated residual leakage estimate
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_directResidual_joint_amplitude_profile
    (c C a₀ b₀ s : ℝ) (ha₀ : 0 < a₀)
    (T U G B I Z : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (hU : ∀ j, 0 ≤ U j) (hG : ∀ j, 0 ≤ G j)
    (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j) (hZ : ∀ j, 0 ≤ Z j)
    (bt bs bg bb bi : ℕ) :
    ∃ (ba : ℕ) (A : ℕ → ℝ), (∀ j, 0 ≤ A j) ∧
      ba = bi + (bt + (bs + (bg + bb))) ∧
    ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
    ∀ (Ac : E → Fin (d + 1) → Mat) (Bc : E → Mat)
      (W₀ W₁ : TwoTimeAmplitude d q) (branch backward : Bool)
      (χout χsource β : E → ℂ) (mi : LocalizerSymbol (d + 1)) (θ : ℝ → ℂ),
    let b := directRetardedAmplitudes Ac Bc W₀ W₁ branch
    ContDiff ℝ ∞ (normalizedElapsedSymbol ρ b) →
    ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource → ContDiff ℝ ∞ β →
    ContDiff ℝ ∞ mi → ContDiff ℝ ∞ θ →
    ∀ (low : Bool) (j k : ℕ), IsComparablePair c C a₀ b₀ ρ low j k →
    ∀ (y : E) (p : V),
    (∀ l, ‖iteratedFDeriv ℝ l (fun w : V ↦ χout w.2.1.1) p‖ ≤ T l * L ^ (l + bt)) →
    (∀ l, ‖iteratedFDeriv ℝ l (fun w : V ↦ χsource w.2.1.2) p‖ ≤ U l * L ^ (l + bs)) →
    (∀ l, ‖iteratedFDeriv ℝ l (fun w : V ↦ β (ρ • w.2.2.1)) p‖ ≤ G l * L ^ (l + bg)) →
    (∀ l, ‖iteratedFDeriv ℝ l (normalizedElapsedSymbol ρ b) p‖ ≤
      ρ ^ s * B l * L ^ (l + bb)) →
    (∀ l, ‖iteratedFDeriv ℝ l (fun w : V ↦ (mi (y, w.2.2.2.1) : ℂ)) p‖ ≤
      I l * L ^ (l + bi)) →
    (∀ l, ‖iteratedFDeriv ℝ l θ p.1‖ ≤ Z l) →
    ∀ l, ‖iteratedFDeriv ℝ l (fun w : V ↦ θ w.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y w) p‖ ≤
      ρ ^ s * A l * L ^ (l + ba) := by
  let D : AmplitudeProfiles := {
    symbol := derivativeConvolution T (derivativeConvolution U (derivativeConvolution G B))
    graphCutoff := comparableCutoffProfile (d + 1) ((8 * annulusFactor c C) / a₀)
    outputCutoff := comparableCutoffProfile (d + 1) ((8 * annulusFactor c C) / a₀)
    inputMask := I
    outputMask := fun _ ↦ 0
    symbol_nonneg := derivativeConvolution_nonneg hT
      (derivativeConvolution_nonneg hU (derivativeConvolution_nonneg hG hB))
    graphCutoff_nonneg := comparableCutoffProfile_nonneg
      (by have := two_le_annulusFactor c C; positivity)
    outputCutoff_nonneg := comparableCutoffProfile_nonneg
      (by have := two_le_annulusFactor c C; positivity)
    inputMask_nonneg := hI
    outputMask_nonneg := fun _ ↦ le_rfl
    symbolOffset := bt + (bs + (bg + bb))
    graphCutoffOffset := 0
    outputCutoffOffset := 0
    inputMaskOffset := bi
    outputMaskOffset := 0 }
  refine ⟨D.offset, derivativeConvolution Z D.productProfile,
    derivativeConvolution_nonneg hZ D.productProfile_nonneg, by simp [D, AmplitudeProfiles.offset], ?_⟩
  intro ρ L hρ hL Ac Bc W₀ W₁ branch backward χout χsource β mi θ b
    hb hout hsource hβ hi hθ low j k hpair y p ht hs hg hbb hmi hz l
  change E × E → ℝ at mi
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hat : ContDiff ℝ ∞ (fun w : V ↦ χout w.2.1.1) := by fun_prop
  have has : ContDiff ℝ ∞ (fun w : V ↦ χsource w.2.1.2) := by fun_prop
  have hag : ContDiff ℝ ∞ (fun w : V ↦ β (ρ • w.2.2.1)) := by fun_prop
  have hfull : ContDiff ℝ ∞ (fun w : V ↦
      elapsedAmplitude b χout χsource β w.1 w.2.1.1 w.2.1.2 (ρ • w.2.2.1)) :=
    ((hat.mul has).mul hag).smul hb
  have ha : ContDiff ℝ ∞ (fun w : V ↦
      orientedElapsedAmplitude backward b χout χsource β w.1 w.2.1.1 w.2.1.2
        (ρ • w.2.2.1)) := by
    cases backward
    · exact hfull
    · let J : Mat ≃ₗᵢ[ℝ] Mat := {
        Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ with
        norm_map' := Matrix.frobenius_norm_conjTranspose }
      exact J.contDiff.comp hfull
  have haGrade l := norm_iteratedFDeriv_orientedElapsedAmplitude_le backward ρ b
    χout χsource β hat has hag hb hT hU hG hL0 bt bs bg bb p ht hs hg hbb l
  let π : V →L[ℝ] JointVariables E := ContinuousLinearMap.snd ℝ _ _
  have hπ : ‖π‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ _ _
  have hcut (f : JointVariables E → ℂ) (hf : ContDiff ℝ ∞ f)
      (hbound : ∀ l, ‖iteratedFDeriv ℝ l f p.2‖ ≤ D.graphCutoff l) (l : ℕ) :
      ‖iteratedFDeriv ℝ l (f ∘ π) p‖ ≤ D.graphCutoff l * L ^ (l + 0) := by
    have hh := norm_iteratedFDeriv_comp_linear_le_grades hf π zero_le_one hπ
      D.graphCutoff_nonneg zero_le_one hL0 0 p l
      (by simpa only [π, ContinuousLinearMap.coe_snd', one_mul] using
        (hbound l).trans (le_mul_of_one_le_right (D.graphCutoff_nonneg l) (one_le_pow₀ hL)))
    simpa only [one_pow, one_mul, mul_one] using hh
  have hgraph : ContDiff ℝ ∞ (fun w : JointVariables E ↦
      (graphBranchCutoff low j (ρ • w.2.1) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_graphBranchCutoff low j).comp (by fun_prop))
  have houtput : ContDiff ℝ ∞ (fun w : JointVariables E ↦
      (outputCutoff k (ρ • w.2.2.2) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_outputCutoff k).comp (by fun_prop))
  have hjoint := contDiff_jointElapsedAmplitude backward ρ b χout χsource β mi
    (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y hb hout hsource hβ hi
    contDiff_const (contDiff_graphBranchCutoff low j) (contDiff_outputCutoff k)
  apply norm_iteratedFDeriv_cut_jointElapsedAmplitude_le backward ρ b χout χsource β
    mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y θ hθ hjoint hZ hL
    D.offset p hz ?_ l
  intro l
  apply norm_iteratedFDeriv_jointElapsedAmplitude_le D backward ρ b χout χsource β
    mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y
    (hgraph.comp π.contDiff) (houtput.comp π.contDiff)
    (Complex.ofRealCLM.contDiff.comp (hi.comp (by fun_prop))) contDiff_const ha hL p
    (hcut _ hgraph (fun l ↦ norm_iteratedFDeriv_joint_graphCutoff_le ha₀ hρ hpair l p.2))
    (hcut _ houtput (fun l ↦ norm_iteratedFDeriv_joint_outputCutoff_le ha₀ hρ hpair l p.2))
    hmi (fun l ↦ by simp [D]) haGrade l

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
