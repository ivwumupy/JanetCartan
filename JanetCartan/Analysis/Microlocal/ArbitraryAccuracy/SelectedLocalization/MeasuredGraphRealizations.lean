module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedLetterRestriction
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Regularizations
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteFixedTimeLimit

/-!
# Literal measurement masks on elapsed graphs and PDO regularizations

The original two measurement cutoffs multiply the corresponding positions of
 the full amplitude. The phase, frequency regularization, elapsed interval and
literal adjoint retain their original order. These identities prepare the
measured letters for the supported-collar estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds FourierIntegral.LowBounds.FrequencyCutoff
open FourierIntegral.FullLowBounds RegularSector.FiniteAssembly
open JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

private theorem measured_fullGraph_test_action
    (S : E → E → ℝ) (A : FullAmplitude (d+1) q) (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace (d+1) q,
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (u : graphTestSpace (d+1) q) :
    measuredOperator μ ν hμ.continuous hν.continuous hμb hνb T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y ξ ↦ ((μ x : ℂ)*(ν y : ℂ)) • A x y ξ) u := by
  change sourceCutMultiplier μ hμ.continuous hμb
    (T (sourceCutMultiplier ν hν.continuous hνb (graphTestToLp u))) =ᵐ[volume] _
  rw [sourceCutMultiplier_graphTestToLp ν hν hνb]
  filter_upwards [sourceCutMultiplier_coeFn μ hμ.continuous hμb
    (T (graphTestToLp (sourceCutTest ν hν u))), hT (sourceCutTest ν hν u)] with x hx ht
  rw [hx, ht]
  change WithLp.toLp 2 ((μ x : ℂ) • graphOperator S A
      (fun y ↦ (ν y : ℂ) • (u.val y).ofLp) x) = _
  apply congrArg (WithLp.toLp 2)
  rw [graphOperator_source_mul]
  simpa only [smul_smul] using (graphOperator_target_mul S
    (fun x y ξ ↦ (ν y : ℂ) • A x y ξ) (fun x ↦ (μ x : ℂ))
    (fun y ↦ (u.val y).ofLp) x).symm

private theorem measured_reverseGraph_test_action
    (S : E → E → ℝ) (A : FullAmplitude (d+1) q) (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace (d+1) q,
      T (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator S A (fun x ↦ (u.val x).ofLp) y))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (u : graphTestSpace (d+1) q) :
    measuredOperator ν μ hν.continuous hμ.continuous hνb hμb T (graphTestToLp u) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
        (fun x y ξ ↦ ((μ x : ℂ)*(ν y : ℂ)) • A x y ξ) (fun x ↦ (u.val x).ofLp) y) := by
  change sourceCutMultiplier ν hν.continuous hνb
    (T (sourceCutMultiplier μ hμ.continuous hμb (graphTestToLp u))) =ᵐ[volume] _
  rw [sourceCutMultiplier_graphTestToLp μ hμ hμb]
  filter_upwards [sourceCutMultiplier_coeFn ν hν.continuous hνb
    (T (graphTestToLp (sourceCutTest μ hμ u))), hT (sourceCutTest μ hμ u)] with y hy ht
  rw [hy, ht]
  change WithLp.toLp 2 ((ν y : ℂ) • reverseGraphOperator S A
      (fun x ↦ (μ x : ℂ) • (u.val x).ofLp) y) = _
  apply congrArg (WithLp.toLp 2)
  rw [reverseGraphOperator_source_mul]
  simpa only [smul_smul, mul_comm] using (reverseGraphOperator_target_mul S
    (fun x y ξ ↦ (μ x : ℂ) • A x y ξ) (fun y ↦ (ν y : ℂ))
    (fun x ↦ (u.val x).ofLp) y).symm

/-- The actual measured regularization realizes the same elapsed phase with
both measurement masks in the full amplitude. The reverse formula is the
literal adjoint, including the conjugated frequency cutoff. Consumer: measured
retarded letters in `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular_base:eq:fixed-time-representation`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measured_elapsed_regularization_test_actions
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β κ : E → ℂ)
    (r : ℝ) (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace (d+1) q,
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude κ (elapsedAmplitude b χout χsource β r)) u)
    (hTadj : ∀ u : graphTestSpace (d+1) q,
      T.adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (κ ξ))
            (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb T
    let A := elapsedAmplitude b (fun x ↦ (μ x : ℂ)*χout x)
      (fun y ↦ (ν y : ℂ)*χsource y) β r
    (∀ u : graphTestSpace (d+1) q, P (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ r) (frequencyCutFullAmplitude κ A) u) ∧
    (∀ u : graphTestSpace (d+1) q, P.adjoint (graphTestToLp u) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (κ ξ))
          (fun x y ξ ↦ (A x y ξ).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) := by
  intro P A
  have hforward : frequencyCutFullAmplitude κ A =
      (fun x y ξ ↦ ((μ x : ℂ)*(ν y : ℂ)) •
        frequencyCutFullAmplitude κ (elapsedAmplitude b χout χsource β r) x y ξ) := by
    funext x y ξ
    simp only [A, elapsedAmplitude, frequencyCutFullAmplitude, smul_smul]
    congr 1
    ring
  have hreverse : frequencyCutFullAmplitude (fun ξ ↦ star (κ ξ))
      (fun x y ξ ↦ (A x y ξ).conjTranspose) =
      (fun x y ξ ↦ ((μ x : ℂ)*(ν y : ℂ)) •
        frequencyCutFullAmplitude (fun ξ ↦ star (κ ξ))
          (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose) x y ξ) := by
    funext x y ξ
    simp only [A, elapsedAmplitude, frequencyCutFullAmplitude, Matrix.conjTranspose_smul,
      map_mul, Complex.star_def, Complex.conj_ofReal, smul_smul]
    congr 1
    ring
  constructor
  · intro u
    rw [hforward]
    exact measured_fullGraph_test_action _ _ T hT μ ν hμ hν hμb hνb u
  · intro u
    dsimp only [P]
    rw [measuredOperator_adjoint, hreverse]
    exact measured_reverseGraph_test_action _ _ T.adjoint hTadj μ ν hμ hν hμb hνb u

/-- Bounded uniqueness identifies the measured original graph with the
canonical elapsed graph of the measured amplitude. The original graph's test
action is the one supplied by the primitive full-graph constructor; no leakage
or choice of a new phase is assumed. Consumer: the canonical strong-limit input
of the supported measured residual estimate
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem measured_elapsedGraph_eq
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (r : ℝ)
    (hreal : ∀ u : graphTestSpace (d+1) q,
      elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r) u)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (elapsedGraph Ψ b χout χsource β r) =
      elapsedGraph Ψ b (fun x ↦ (μ x : ℂ)*χout x)
        (fun y ↦ (ν y : ℂ)*χsource y) β r := by
  symm
  apply fullGraphOperator_eq_of_realizes
  intro u
  have h := measured_fullGraph_test_action _ _ _ hreal μ ν hμ hν hμb hνb u
  convert h using 1
  congr 2
  funext x y ξ
  simp only [elapsedAmplitude, smul_smul]
  congr 1
  ring

/-- The actual physical regularizations and their strong limit determine the
uncut test action from primitive supported continuity and a zeroth symbol bound.
This discharges the canonical realization input for measurement covariance,
without assuming an uncut kernel formula
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedGraph_test_action_of_physical_regularizations
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ) (r : ℝ)
    (hΨ : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ (x 0) (x 0-r) (spatialPart x) (spatialPart ξ)) ξ)
    (hb : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b (x 0) (x 0-r) (spatialPart x) (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0-r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace (d+1) q),
      Treg j (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude b χout χsource β r)) u)
    (hlim : ∀ u, Tendsto (fun j ↦ Treg j u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u))) :
    ∀ u : graphTestSpace (d+1) q,
      elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r) u := by
  intro u
  obtain ⟨s, hs', hsub⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hlim (graphTestToLp u))).exists_seq_tendsto_ae
  filter_upwards [hsub, ae_all_iff.mpr (fun j ↦ hreal j u)] with x hx he
  have ht := (PiLp.continuous_toLp 2 (fun _ : Fin q ↦ ℂ)).tendsto _ |>.comp
    (UncutTestAction.tendsto_uncut_elapsedGraph_test_of_bound Ψ b χout χsource β
      hs hβ Cβ hβbound r u x (hΨ x) (hb x) C (hbound x))
  exact tendsto_nhds_unique hx
    ((ht.comp hs'.tendsto_atTop).congr (fun j ↦ (he (s j)).symm))

/-- Both original measurement masks multiply their own position in the
canonical PDO amplitude. The retained normal-amplitude certificate supplies
its test action; no new PDO realization is assumed. Consumer: the measured
characteristic PDO letters of `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measured_maskedPhysicalPDO_eq
    (χout χsource : E → ℂ) (c : E → E → Matrix (Fin q) (Fin q) ℂ)
    {R M : ℝ}
    (hc : GraphNormalAmplitudeBounds
      (RegularSector.Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
        (maskedPhysicalPDO χout χsource c) =
      maskedPhysicalPDO (fun x ↦ (μ x : ℂ)*χout x)
        (fun y ↦ (ν y : ℂ)*χsource y) c := by
  have ht (u : graphTestSpace (d+1) q) :
      maskedPhysicalPDO χout χsource c (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (fun x ξ ↦ inner ℝ x ξ)
          (fun x y ξ ↦ (χout x * χsource y) • c x ξ) u := by
    have hh := RegularSector.Characteristic.PdoRealization.canonicalGraph_frequencyCut_realizes
      (Nat.succ_pos d) _ hc (fun _ ↦ 1) contDiff_const zero_le_one (fun _ ↦ by simp) u
    have he : frequencyCutFullAmplitude (fun _ : E ↦ (1 : ℂ))
        (fun x y ξ ↦ (χout x * χsource y) • c x ξ) =
        (fun x y ξ ↦ (χout x * χsource y) • c x ξ) := by
      funext x y ξ
      exact one_smul ℂ _
    rw [he] at hh
    exact hh
  symm
  apply fullGraphOperator_eq_of_realizes
  intro u
  have h := measured_fullGraph_test_action _ _ _ ht μ ν hμ hν hμb hνb u
  convert h using 1
  congr 2
  funext x y ξ
  simp only [smul_smul]
  congr 1
  ring

/-- Apply the original PDO regularization producer and retain both
measurement masks in every finite kernel and in its strong limit. This supplies
all literal graph realizations for the measured characteristic PDO branches;
no new normal-amplitude certificate is required after measurement
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_measured_maskedPDO_oriented_regularizations
    (χout χsource : E → ℂ) (c : E → E → Matrix (Fin q) (Fin q) ℂ)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {R M : ℝ}
    (hc : GraphNormalAmplitudeBounds
      (RegularSector.Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    let χo := fun x ↦ (μ x : ℂ)*χout x
    let χs := fun y ↦ (ν y : ℂ)*χsource y
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      ResidualLocalization.orientedMaskedPDOAmplitude backward χo χs c p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ j, Preg true j = (Preg false j).adjoint) ∧
      (∀ backward j (u : graphTestSpace (d+1) q),
        Preg backward j (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff j)
              (ResidualLocalization.orientedMaskedPDOAmplitude backward χo χs c))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward u, Tendsto (fun j ↦ Preg backward j u) atTop
        (𝓝 ((if backward then (maskedPhysicalPDO χo χs c).adjoint
          else maskedPhysicalPDO χo χs c) u))) := by
  intro χo χs
  obtain ⟨hsm, T, hTa, hT, hlim⟩ := exists_maskedPDO_oriented_regularizations
    χout χsource c hout hsource hc
  let Tm := fun j ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (T false j)
  have hP := measured_maskedPhysicalPDO_eq χout χsource c hc μ ν hμ hν hμb hνb
  have hAm (backward : Bool) (j : ℕ) :
      frequencyCutFullAmplitude (complexPhysicalCutoff j)
        (ResidualLocalization.orientedMaskedPDOAmplitude backward χo χs c) =
      (fun x y ξ ↦ ((μ x : ℂ)*(ν y : ℂ)) •
        frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (ResidualLocalization.orientedMaskedPDOAmplitude backward χout χsource c) x y ξ) := by
    funext x y ξ
    cases backward
    · simp only [frequencyCutFullAmplitude, ResidualLocalization.orientedMaskedPDOAmplitude,
        Bool.false_eq_true, ite_false, χo, χs, smul_smul]
      congr 1
      ring
    · simp only [frequencyCutFullAmplitude, ResidualLocalization.orientedMaskedPDOAmplitude,
        ite_true, χo, χs, Matrix.conjTranspose_smul, map_mul,
        Complex.star_def, Complex.conj_ofReal, smul_smul]
      congr 1
      ring
  have hAm0 : ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      (χo p.1.1 * χs p.1.2) • c p.1.1 p.2) := by
    have hm := ((Complex.ofRealCLM.contDiff.comp (hμ.comp contDiff_fst.fst)).mul
      (Complex.ofRealCLM.contDiff.comp (hν.comp contDiff_fst.snd))).smul (hsm false)
    change ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      ((μ p.1.1 : ℂ) * (ν p.1.2 : ℂ)) •
        ((χout p.1.1 * χsource p.1.2) • c p.1.1 p.2)) at hm
    convert hm using 1
    funext p
    simp only [χo, χs, smul_smul]
    congr 1
    ring
  refine ⟨?_, fun backward j ↦ if backward then (Tm j).adjoint else Tm j,
    fun _ ↦ rfl, ?_, ?_⟩
  · intro backward
    cases backward
    · exact hAm0
    · exact (Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hAm0
  · intro backward j u
    cases backward
    · change Tm j (graphTestToLp u) =ᵐ[volume] _
      rw [hAm false j]
      exact measured_fullGraph_test_action _ _ (T false j) (hT false j)
        μ ν hμ hν hμb hνb u
    · change (Tm j).adjoint (graphTestToLp u) =ᵐ[volume] _
      dsimp only [Tm]
      rw [measuredOperator_adjoint, hAm true j]
      exact measured_reverseGraph_test_action _ _ (T false j).adjoint
        (fun v ↦ by rw [← hTa j]; exact hT true j v) μ ν hμ hν hμb hνb u
  · intro backward u
    cases backward
    · change Tendsto (fun j ↦ Tm j u) atTop (𝓝 (maskedPhysicalPDO χo χs c u))
      rw [← hP]
      exact (sourceCutMultiplier μ hμ.continuous hμb).continuous.continuousAt.tendsto.comp
        (hlim false (sourceCutMultiplier ν hν.continuous hνb u))
    · change Tendsto (fun j ↦ (Tm j).adjoint u) atTop
        (𝓝 ((maskedPhysicalPDO χo χs c).adjoint u))
      rw [← hP]
      simp only [Tm, measuredOperator_adjoint]
      have ht := (sourceCutMultiplier ν hν.continuous hνb).continuous.continuousAt.tendsto.comp
        (hlim true (sourceCutMultiplier μ hμ.continuous hμb u))
      simpa only [hTa, ite_true, measuredOperator, ContinuousLinearMap.comp_apply,
        Function.comp_def] using ht

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
