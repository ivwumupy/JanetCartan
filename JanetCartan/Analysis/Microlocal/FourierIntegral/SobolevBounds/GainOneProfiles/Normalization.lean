module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches

/-!
# Order-minus-one normalization of the original primitives

The gain-one paragraph after `app:ch_regular_base:eq:graph-derivative-transfer`
uses the complete amplitude `R • A(x,y,Rη)`. Its joint seminorm retains both
positions and every mask. The estimates below supply the physical weights for
`exists_graph_gain_one_constant_of_primitive_profiles` and its adjoint version.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles
variable {n r : ℕ}

/-- Actual order-minus-one normalization, including every mask and both positions.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def orderMinusOneField (R : ℝ) (A : FullAmplitude n r) : Point n → Matrix (Fin r) (Fin r) ℂ :=
  R • normalizedField R (uncurry A)

/-- The order-minus-one symbol seminorm is the supremum of joint `cNorm`s of
`R • A(x,y,Rη)` over `R ≥ 1`. Source: `app:ch_regular_base:eq:fio-input`, `d=1`. -/
def orderMinusOneSeminorm (K : Set (Point n)) (j : ℕ) (A : FullAmplitude n r) : ℝ :=
  sSup (Set.range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm K j (orderMinusOneField R A))

/-- Symbol-class finiteness for the actual order-minus-one normalized amplitude.
Source: `app:ch_regular_base:eq:fio-input`. -/
def BoundedOrderMinusOneSeminorm (K : Set (Point n)) (j : ℕ)
    (A : FullAmplitude n r) : Prop :=
  BddAbove (Set.range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm K j (orderMinusOneField R A))

/-- Nonnegativity of the gain-one amplitude seminorm (`app:ch_regular_base:eq:fio-input`). -/
theorem orderMinusOneSeminorm_nonneg (K : Set (Point n)) (j : ℕ) (A : FullAmplitude n r) :
    0 ≤ orderMinusOneSeminorm K j A := by
  apply Real.sSup_nonneg
  rintro _ ⟨R, rfl⟩
  exact cNorm_nonneg _ _ _

/-- Each actual normalized radius is controlled by the symbol seminorm used
in the gain-one high quantity (`app:ch_regular_base:eq:fio-input`). -/
theorem cNorm_orderMinusOneField_le {K : Set (Point n)} {j : ℕ} {A : FullAmplitude n r}
    (hb : BoundedOrderMinusOneSeminorm K j A) {R : ℝ} (hR : 1 ≤ R) :
    cNorm K j (orderMinusOneField R A) ≤ orderMinusOneSeminorm K j A :=
  le_csSup hb ⟨⟨R, hR⟩, rfl⟩

/-- Ordinary physical smoothness produces smooth normalized order-minus-one
amplitudes; no weighted derivative estimate is assumed. Source: Step 3. -/
theorem contDiffOn_orderMinusOneField {U V : Set (Point n)} {A : FullAmplitude n r}
    (hA : ContDiffOn ℝ ∞ (uncurry A) V)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {R : ℝ} (hR : 1 ≤ R) : ContDiffOn ℝ ∞ (orderMinusOneField R A) U :=
  (contDiffOn_normalizedField_of_dilations hA hrad hR).const_smul R

/-- A single normalized radius controls the ordered physical jet, with exactly
one radius per covector letter. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem weighted_jet_le_cNorm_normalizedField
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : Point n) {δ : ℝ} {U V : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {f : Field n F} (hf : ContDiffOn ℝ ∞ (uncurry f) V)
    {R : ℝ} (hR : 1 ≤ R) {v : Point n} (hv : v ∈ Metric.closedBall z δ)
    (w : List (Coordinate n)) :
    R ^ frequencyOrder w * ‖uncurry (jet w f) (v.1, R • v.2)‖ ≤
      cNorm (Metric.closedBall z δ) w.length (normalizedField R (uncurry f)) := by
  have hp := hrad R hR v (hball hv)
  rw [jet_eq_iteratedFDeriv hV hf w hp, ← card_frequencySlots]
  apply (norm_transportMixedJet_weight_le w.length (lt_of_lt_of_le zero_lt_one hR)
    hV (hf.of_le (by simp)) v hp (frequencySlots w)
    (fun i ↦ coordinateDirection (w.get i)) (coordinateDirection_slots w)
    (fun i ↦ (norm_coordinateDirection (w.get i)).le)).trans
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z δ)
    (fun p hp ↦ ((contDiffOn_normalizedField_of_dilations hf hrad hR).contDiffAt
      (hU.mem_nhds (hball hp))).of_le (by simp)) hv le_rfl

/-- The order-minus-one normalization proves the required `1/ρ` decay on a
normalized chart. Neither position nor any cutoff is removed from the jets.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem weighted_amplitude_jet_le
    (z : Point n) {δ : ℝ} {U V : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {A : FullAmplitude n r} (hA : ContDiffOn ℝ ∞ (uncurry A) V)
    {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    {v : Point n} (hv : v ∈ Metric.closedBall z δ) (w : List (Coordinate n)) :
    ρ ^ frequencyOrder w * ‖uncurry (jet w A) (v.1, R • v.2)‖ ≤
      cNorm (Metric.closedBall z δ) w.length (orderMinusOneField R A) / ρ := by
  have hn := weighted_jet_le_cNorm_normalizedField z hU hV hball hrad hA hR hv w
  have hs : cNorm (Metric.closedBall z δ) w.length (orderMinusOneField R A) =
      R * cNorm (Metric.closedBall z δ) w.length (normalizedField R (uncurry A)) := by
    rw [orderMinusOneField, cNorm_smul_of_contDiffAt R
      (fun p hp ↦ ((contDiffOn_normalizedField_of_dilations hA hrad hR).contDiffAt
        (hU.mem_nhds (hball hp))).of_le (by simp)), Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hR)]
  apply (le_div_iff₀ hρ).mpr
  rw [hs]
  have hw := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ.le hρR _) (norm_nonneg _)).trans hn
  exact (mul_le_mul hw hρR hρ.le (cNorm_nonneg _ _ _)).trans_eq (mul_comm _ _)

private theorem cNorm_eq_of_eqOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set (Point n)} (hU : IsOpen U) (hKU : K ⊆ U)
    {f g : Point n → F} (he : Set.EqOn f g U) (j : ℕ) : cNorm K j f = cNorm K j g := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Set.image_congr
  intro p hp
  rw [((Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hp)) he).iteratedFDeriv
    (𝕜 := ℝ) k).self_of_nhds]

/-- The fixed factor `i` in the actual phase primitive preserves every joint
seminorm. Source: first-output amplitudes in Step 3 of the actual-calculus theorem. -/
theorem cNorm_phasePrimitive_eq {K U : Set (Point n)} (hU : IsOpen U) (hKU : K ⊆ U)
    {S : Euclidean n → Euclidean n → ℝ}
    (hS : ContDiffOn ℝ ∞ (fun p : Point n ↦ S p.1.1 p.2) U) (j : ℕ) :
    cNorm K j (uncurry (phasePrimitive S)) =
      cNorm K j (fun p : Point n ↦ S p.1.1 p.2) := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Set.image_congr
  intro p hp
  have hreal := (hS.contDiffAt (hU.mem_nhds (hKU hp))).of_le
    (show (k : ℕ∞ω) ≤ ∞ by simp)
  have hc : ContDiffAt ℝ (k : ℕ) (fun p : Point n ↦ (S p.1.1 p.2 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  change ‖iteratedFDeriv ℝ k (fun p : Point n ↦ Complex.I • (S p.1.1 p.2 : ℂ)) p‖ = _
  rw [iteratedFDeriv_const_smul_apply' hc, norm_smul, Complex.norm_I, one_mul]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hreal le_rfl

/-- Degree-one phase normalization and the two-sided geometric radius comparison
give the exact order-one physical weight. Source: gain one in Step 3. -/
theorem weighted_phase_jet_le
    (z : Point n) {δ : ℝ} {U V : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {S : Euclidean n → Euclidean n → ℝ}
    (hS : ContDiffOn ℝ ∞ (fun p : Point n ↦ S p.1.1 p.2) V)
    (hhom : ∀ R : ℝ, 0 < R → ∀ p ∈ U, S p.1.1 (R • p.2) = R * S p.1.1 p.2)
    {R ρ c : ℝ} (hR : 1 ≤ R) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hRc : R ≤ c * ρ)
    {v : Point n} (hv : v ∈ Metric.closedBall z δ) (w : List (Coordinate n)) :
    ρ ^ frequencyOrder w * ‖uncurry (jet w (phasePrimitive S)) (v.1, R • v.2)‖ ≤
      c * cNorm (Metric.closedBall z δ) w.length (fun p : Point n ↦ S p.1.1 p.2) * ρ := by
  have hUV : U ⊆ V := by intro p hp; simpa using hrad 1 le_rfl p hp
  have hSU := hS.mono hUV
  have hc : ContDiffOn ℝ ∞ (uncurry (phasePrimitive S)) V :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hS).const_smul Complex.I
  have he : Set.EqOn (normalizedField R (uncurry (phasePrimitive S)))
      (R • uncurry (phasePrimitive S)) U := by
    intro p hp
    simp only [normalizedField, uncurry, phasePrimitive, Pi.smul_apply,
      hhom R (lt_of_lt_of_le zero_lt_one hR) p hp, Complex.ofReal_mul,
      Complex.real_smul]
    ring
  have hs := cNorm_eq_of_eqOn hU hball he w.length
  rw [cNorm_smul_of_contDiffAt R (fun p hp ↦ (hc.contDiffAt
    (hV.mem_nhds (hUV (hball hp)))).of_le (by simp)),
    Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hR),
    cNorm_phasePrimitive_eq hU hball hSU] at hs
  have hn := weighted_jet_le_cNorm_normalizedField z hU hV hball hrad hc hR hv w
  rw [hs] at hn
  calc
    _ ≤ R ^ frequencyOrder w * ‖uncurry (jet w (phasePrimitive S)) (v.1, R • v.2)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρR _) (norm_nonneg _)
    _ ≤ R * cNorm (Metric.closedBall z δ) w.length (fun p : Point n ↦ S p.1.1 p.2) := hn
    _ ≤ (c * ρ) * cNorm (Metric.closedBall z δ) w.length (fun p : Point n ↦ S p.1.1 p.2) :=
      mul_le_mul_of_nonneg_right hRc (cNorm_nonneg _ _ _)
    _ = _ := by ring

end JanetCartan.FourierIntegral.GainOneProfiles
