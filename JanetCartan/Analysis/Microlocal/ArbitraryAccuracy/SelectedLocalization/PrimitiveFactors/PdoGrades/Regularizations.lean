module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedFactors
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization

/-!
# Literal PDO regularizations on the common selected output

For `app:ch_regular_base:eq:energy-complete-residual`, transfer the retained
normal-amplitude certificates through the physical frequency conversion and
the smaller output mask. The adjoint is the reverse integral of the conjugate
transpose of the full amplitude, including both masks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FullLowBounds LowBounds LowBounds.FrequencyCutoff
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.FiniteAssembly
open RegularSector.FiniteResidual.SelectedChart
open CharacteristicTransport.CompleteResidual Pseudodifferential AmplitudeBound
open ResidualLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => SpacetimeL2 d q

/-- Undo the physical `2π` frequency conversion in the retained certificate.
Consumer: joint smoothness of the literal PDO amplitude in `CompleteFactor`
(`app:ch_regular:eq:chain-tail`). This does not infer joint derivative bounds
from the certificate's physical derivative bounds. -/
theorem contDiff_fullAmplitude_of_cycleSymbol
    (A : FullAmplitude (d+1) q) {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds (physicalPDOCycleSymbol A) R M) :
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) := by
  have hc := hb.smooth.comp
    ((contDiff_snd.const_smul ((2 * Real.pi)⁻¹)).prodMk
      (contDiff_pairedPosition.comp contDiff_fst))
  simpa only [Function.comp_def, Function.uncurry_apply_pair,
    physicalPDOCycleSymbol_pairedPosition, smul_smul,
    mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul] using hc

private theorem oriented_smooth (A : FullAmplitude (d+1) q)
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    (backward : Bool) :
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      if backward then (A p.1.1 p.1.2 p.2).conjTranspose else A p.1.1 p.1.2 p.2) := by
  cases backward
  · exact hA
  · exact (Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hA

/-- Construct literal forward and adjoint regularizations from the retained
PDO certificate, using the SAME real physical cutoff sequence in both
orientations. Consumer: `hAp`, `hrealp`, and `hlimp` of `CompleteFactor`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_maskedPDO_oriented_regularizations
    (χout χsource : E → ℂ) (c : E → E → Mat)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M) :
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedMaskedPDOAmplitude backward χout χsource c p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ l, Preg true l = (Preg false l).adjoint) ∧
      (∀ backward l (u : graphTestSpace (d+1) q),
        Preg backward l (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l)
              (orientedMaskedPDOAmplitude backward χout χsource c))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward u, Tendsto (fun l ↦ Preg backward l u) atTop
        (𝓝 ((if backward then (maskedPhysicalPDO χout χsource c).adjoint
          else maskedPhysicalPDO χout χsource c) u))) := by
  let A : FullAmplitude (d+1) q := fun x y ξ ↦ (χout x * χsource y) • c x ξ
  let T := fun l ↦ fullGraphOperator (fun x ξ : E ↦ inner ℝ x ξ)
    (frequencyCutFullAmplitude (complexPhysicalCutoff l) A)
  have hA := contDiff_fullAmplitude_of_cycleSymbol A hb
  have hreal l (u : graphTestSpace (d+1) q) :=
    canonicalGraph_frequencyCut_realizes (Nat.succ_pos d) A hb _
      (complexPhysicalCutoff_contDiff l) zero_le_one (complexPhysicalCutoff_norm_le l) u
  refine ⟨fun backward ↦ oriented_smooth A hA backward,
    fun backward l ↦ if backward then (T l).adjoint else T l, fun _ ↦ rfl, ?_, ?_⟩
  · intro backward l u
    cases backward
    · exact hreal l u
    · have ha := compactFullGraph_adjoint_ae (fun x ξ : E ↦ inner ℝ x ξ)
        (contDiff_fst.inner ℝ contDiff_snd) A
        (hA.comp (contDiff_fst.prodMk contDiff_snd.fst |>.prodMk contDiff_snd.snd))
        hout hsource (fun x y ξ h ↦ by
          rcases h with hx | hy
          · simp [A, image_eq_zero_of_notMem_tsupport hx]
          · simp [A, image_eq_zero_of_notMem_tsupport hy])
        _ (complexPhysicalCutoff_contDiff l) (complexPhysicalCutoff_hasCompactSupport l)
        (T l) (hreal l) u
      have hstar : (fun ξ : E ↦ star (complexPhysicalCutoff l ξ)) = complexPhysicalCutoff l := by
        funext ξ
        exact Complex.conj_ofReal _
      rw [hstar] at ha
      exact ha
  · intro backward u
    cases backward
    · exact tendsto_canonicalGraph_frequencyCut (Nat.succ_pos d) A hb _
        complexPhysicalCutoff_contDiff le_rfl complexPhysicalCutoff_norm_le
        complexPhysicalCutoff_tendsto u
    · exact tendsto_canonicalGraph_frequencyCut_adjoint (Nat.succ_pos d) A hb _
        complexPhysicalCutoff_contDiff le_rfl complexPhysicalCutoff_norm_le
        complexPhysicalCutoff_tendsto u

/-- Transfer the retained PDO certificate to the smaller physical output by
literal multiplication. The common-output operator and BOTH strong limits
are derived, without assuming a new certificate for the smaller amplitude.
Consumer: the differentiated algebraic branch of `CompleteFactor` on the
SAME selected witnesses (`app:ch_regular:eq:chain-tail`). -/
theorem exists_commonOutputPDO_oriented_regularizations
    (χout χsource : E → ℂ) (c : E → E → Mat)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1) (hp : ∀ x, (ψ x : ℂ) * χout x = (ψ x : ℂ)) :
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedMaskedPDOAmplitude backward (fun x ↦ (ψ x : ℂ)) χsource c p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ l, Preg true l = (Preg false l).adjoint) ∧
      (∀ backward l (u : graphTestSpace (d+1) q),
        Preg backward l (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l)
              (orientedMaskedPDOAmplitude backward (fun x ↦ (ψ x : ℂ)) χsource c))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward u, Tendsto (fun l ↦ Preg backward l u) atTop
        (𝓝 ((if backward then (maskedPhysicalPDO (fun x ↦ (ψ x : ℂ)) χsource c).adjoint
          else maskedPhysicalPDO (fun x ↦ (ψ x : ℂ)) χsource c) u))) := by
  let A : FullAmplitude (d+1) q := fun x y ξ ↦ (χout x * χsource y) • c x ξ
  let As : FullAmplitude (d+1) q := fun x y ξ ↦ ((ψ x : ℂ) * χsource y) • c x ξ
  let Mo : H →L[ℂ] H := sourceCutMultiplier ψ hψ.continuous hψb
  have he (x y ξ : E) : (ψ x : ℂ) • A x y ξ = As x y ξ := by
    simp only [A, As, smul_smul, ← mul_assoc, hp]
  have hA := contDiff_fullAmplitude_of_cycleSymbol A hb
  have hAs : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ As p.1.1 p.1.2 p.2) := by
    have hh := (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst.fst)).smul hA
    change ContDiff ℝ ∞ (fun p : (E × E) × E ↦ (ψ p.1.1 : ℂ) • A p.1.1 p.1.2 p.2) at hh
    simpa only [he] using hh
  obtain ⟨_, T, hTa, hT, hlim⟩ := exists_maskedPDO_oriented_regularizations
    χout χsource c hout hsource hb
  let Ts := fun l ↦ Mo.comp (T false l)
  have hP : Mo.comp (maskedPhysicalPDO χout χsource c) =
      maskedPhysicalPDO (fun x ↦ (ψ x : ℂ)) χsource c :=
    sourceCutMultiplier_maskedPhysicalPDO χout χsource c R M hb ψ hψ.continuous hψb hp
  have hreal l (u : graphTestSpace (d+1) q) :
      Ts l (graphTestToLp u) =ᵐ[volume] graphTestOutput (fun x ξ ↦ inner ℝ x ξ)
        (frequencyCutFullAmplitude (complexPhysicalCutoff l) As) u := by
    filter_upwards [sourceCutMultiplier_coeFn ψ hψ.continuous hψb
      (T false l (graphTestToLp u)), hT false l u] with x hx ht
    change Mo (T false l (graphTestToLp u)) x = _
    rw [hx, ht]
    change WithLp.toLp 2 ((ψ x : ℂ) • graphOperator _ _ _ x) = _
    apply congrArg (WithLp.toLp 2)
    change (ψ x : ℂ) • graphOperator (fun x ξ : E ↦ inner ℝ x ξ)
      (frequencyCutFullAmplitude (complexPhysicalCutoff l) A) (fun y ↦ (u.val y).ofLp) x = _
    rw [← graphOperator_target_mul (fun x ξ : E ↦ inner ℝ x ξ)
      (frequencyCutFullAmplitude (complexPhysicalCutoff l) A)
      (fun x ↦ (ψ x : ℂ))]
    congr 1
    funext x y ξ
    change (ψ x : ℂ) • (complexPhysicalCutoff l ξ • A x y ξ) =
      complexPhysicalCutoff l ξ • As x y ξ
    rw [smul_comm, he]
  refine ⟨fun backward ↦ oriented_smooth As hAs backward,
    fun backward l ↦ if backward then (Ts l).adjoint else Ts l,
    fun _ ↦ rfl, ?_, ?_⟩
  · intro backward l u
    cases backward
    · exact hreal l u
    · have ha := compactFullGraph_adjoint_ae (fun x ξ : E ↦ inner ℝ x ξ)
        (contDiff_fst.inner ℝ contDiff_snd) As
        (hAs.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))
        (hcψ.comp_left Complex.ofReal_zero) hsource (fun x y ξ h ↦ by
          rcases h with hx | hy
          · have hz : (ψ x : ℂ) = 0 := by
              change (Complex.ofReal ∘ ψ) x = 0
              exact image_eq_zero_of_notMem_tsupport hx
            simp only [As, hz, zero_mul, zero_smul]
          · simp only [As, image_eq_zero_of_notMem_tsupport hy, mul_zero, zero_smul])
        _ (complexPhysicalCutoff_contDiff l) (complexPhysicalCutoff_hasCompactSupport l)
        (Ts l) (hreal l) u
      have hstar : (fun ξ : E ↦ star (complexPhysicalCutoff l ξ)) = complexPhysicalCutoff l := by
        funext ξ
        exact Complex.conj_ofReal _
      rw [hstar] at ha
      exact ha
  · intro backward u
    cases backward
    · have hh := Mo.continuous.continuousAt.tendsto.comp (hlim false u)
      simpa only [← hP, Ts, Bool.false_eq_true, ↓reduceIte,
        ContinuousLinearMap.comp_apply, Function.comp_def] using hh
    · have hh := hlim true (Mo u)
      have hPa := congrArg ContinuousLinearMap.adjoint hP
      simp only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint, Mo] at hPa
      simpa only [Ts, ContinuousLinearMap.adjoint_comp, Mo, sourceCutMultiplier_adjoint,
        ContinuousLinearMap.comp_apply, hTa, ← hPa, ↓reduceIte] using hh

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
