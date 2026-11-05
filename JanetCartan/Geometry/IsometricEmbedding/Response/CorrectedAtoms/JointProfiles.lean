module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Regularity

/-!
# Joint and mixed profiles after the same response

For `app:ch_response:cor:current-atoms`, apply the exact raw polynomial estimate
and the literal response derivative estimate on the unchanged joint compact.
The leading tensor remains the original one. No corrected amplitude profile is
a premise. The actual coefficient profiles belong to the retained raw family;
the SAME response's joint regularity and derivative jets belong to
`both-fixed-response-parameters` and `both-response-transfer`.

These deductions give the mixed profiles consumed by the canonical raw and
sampling constructions. They do not produce the response estimate or complete
its substitution on the initialized history.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The local jet triangle inequality used on the literal corrected field
(`app:ch_response:eq:current-atomic-amplitudes`). -/
private theorem norm_iteratedFDeriv_sub_le {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f - g) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖ := by
  rw [iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact norm_sub_le _ _

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    {τ L : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L C)
    (hpν₀ : HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L B₁)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    (hresponseJets : ∀ j, ∀ w ∈ J,
      ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
        τ * Cresp j * L ^ (j - rpar))

include hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
  hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets

/-- Joint derivative and leading-error estimates for the literal corrected
amplitude. The raw estimates are derived from their five coefficient profiles;
the only response estimates concern its actual physical derivative. The error
retains its factor `τ` and baseline `rpar`
(`app:ch_response:eq:current-atomic-amplitudes`, `app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem fullCorrectedDerivativeAmplitude_joint_bounds
    (j : ℕ) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ j (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
      (derivativeProfile n N C A₀ A₁ B₀ B₁ j + Cresp j) * L ^ (j - rpar) ∧
    ‖iteratedFDeriv ℝ j (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) w‖ ≤
      τ * (errorProfile n N C A₀ A₁ B₀ B₁ j + Cresp j) * L ^ (j - rpar) := by
  have hraw := full_amplitude_joint_bounds T Q F row col Φ Y r hJ hΩ hJΩ hphase
    hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ j hw
  have hp := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ.ne').2
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hl : ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r) Ω := by
    apply (contDiffOn_normalTensor hξ hν₀).neg.congr
    intro x _
    exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r x
  have hy := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphase χ B τ hresponse
  have hsmall : τ * Cresp j * L ^ (j - rpar) ≤ Cresp j * L ^ (j - rpar) := by
    calc
      _ = τ * (Cresp j * L ^ (j - rpar)) := by ring
      _ ≤ 1 * (Cresp j * L ^ (j - rpar)) :=
        mul_le_mul_of_nonneg_right hτ₁ (mul_nonneg (hCresp j) (pow_nonneg (by linarith) _))
      _ = _ := one_mul _
  have hx := hΩ.mem_nhds (hJΩ hw)
  constructor
  · exact (norm_iteratedFDeriv_sub_le (hp.contDiffAt hx) (hy.contDiffAt hx) j).trans
      ((add_le_add hraw.2.1 ((hresponseJets j w hw).trans hsmall)).trans_eq (by ring))
  · have he : fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r =
        (fullDerivativeAmplitude T Q F row col Φ Y r τ -
          fullLeadingPrincipalMatrix T Q F row col Φ Y r) -
        fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ := by
      change (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) - _ = _
      abel
    rw [he]
    exact (norm_iteratedFDeriv_sub_le ((hp.sub hl).contDiffAt hx) (hy.contDiffAt hx) j).trans
      ((add_le_add hraw.2.2 (hresponseJets j w hw)).trans_eq (by ring))

/-- The same joint estimates give all physical/carrier mixed orders `s+k`
for `k ≤ rpar`, preserving the inverse-frequency error and the original phase
(`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem fullCorrectedDerivativeAmplitude_mixed_bounds
    (s k : ℕ) (hk : k ≤ rpar)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ (s + k) (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
      (derivativeProfile n N C A₀ A₁ B₀ B₁ (s + k) + Cresp (s + k)) * L ^ s ∧
    ‖iteratedFDeriv ℝ (s + k) (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) w‖ ≤
      τ * (errorProfile n N C A₀ A₁ B₀ B₁ (s + k) + Cresp (s + k)) * L ^ s := by
  have hh := fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
    hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
    hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets (s + k) hw
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ (s + k)
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (add_nonneg hc.2.2.2.2 (hCresp _))),
    hh.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg hτ.le (add_nonneg hc.2.2.2.1 (hCresp _))))⟩

/-- The literal corrected derivative and error satisfy the corresponding
`cNorm` profiles on the SAME compact, with the original baseline and explicit
sums of fixed constants (`app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedDerivativeAmplitude_profiles :
    HasDerivativeProfile J (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ)
      rpar L (fun j ↦ ∑ i ∈ Finset.range (j + 1),
        (derivativeProfile n N C A₀ A₁ B₀ B₁ i + Cresp i)) ∧
    HasDerivativeProfile J (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) rpar L
      (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), (errorProfile n N C A₀ A₁ B₀ B₁ i + Cresp i)) := by
  have hh (j) (w) (hw : w ∈ J) :=
    fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
      hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
      hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets j hw
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁
  constructor
  · simpa only [one_mul] using profile_of_jet_bounds hL zero_le_one
      (fun j ↦ add_nonneg (hc j).2.2.2.2 (hCresp j))
      (fun j w hw ↦ by simpa only [one_mul] using (hh j w hw).1)
  · exact profile_of_jet_bounds hL hτ.le
      (fun j ↦ add_nonneg (hc j).2.2.2.1 (hCresp j)) (fun j w hw ↦ (hh j w hw).2)

omit hresponseJets in
/-- The literal corrected displacement has the original mixed-order reserve,
and its change from the raw displacement retains the response's factor `τ²`.
Only the SAME response's displacement jets are required here; the raw bound
comes from the published coefficient profiles
(`app:ch_response:eq:current-atomic-amplitudes`,
`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem fullCorrectedDisplacementAmplitude_joint_bounds
    (hresponseDisplacementJets : ∀ j, ∀ w ∈ J,
      ‖iteratedFDeriv ℝ j (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
        τ ^ 2 * Cresp j * L ^ (j - rpar))
    (j : ℕ) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ j (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
      τ * (displacementProfile A₀ A₁ B₀ B₁ j + Cresp j) * L ^ (j - rpar) ∧
    ‖iteratedFDeriv ℝ j (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ -
      fullDisplacementAmplitude T Q F row col Φ Y r τ) w‖ ≤
      τ ^ 2 * Cresp j * L ^ (j - rpar) := by
  have hraw := (full_amplitude_joint_bounds T Q F row col Φ Y r hJ hΩ hJΩ hphase
    hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ j hw).1
  have hdisp := (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).1
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega : j - (rpar + 1) ≤ j - rpar))
    (mul_nonneg hτ.le hdisp))
  have hsmall : τ ^ 2 * Cresp j * L ^ (j - rpar) ≤ τ * Cresp j * L ^ (j - rpar) := by
    have hτ2 : τ ^ 2 ≤ τ := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hτ2 (hCresp j)) (pow_nonneg (by linarith) _)
  have hp := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ.ne').1
  have hy := contDiffOn_fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r
    hphase τ hresponse
  constructor
  · exact (norm_iteratedFDeriv_sub_le (hp.contDiffAt (hΩ.mem_nhds (hJΩ hw)))
      (hy.contDiffAt (hΩ.mem_nhds (hJΩ hw))) j).trans
      ((add_le_add hraw' ((hresponseDisplacementJets j w hw).trans hsmall)).trans_eq (by ring))
  · have he : fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ -
        fullDisplacementAmplitude T Q F row col Φ Y r τ =
        -fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ := by
      change (fullDisplacementAmplitude T Q F row col Φ Y r τ -
        fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) - _ = _
      abel
    rw [he, iteratedFDeriv_neg_apply, norm_neg]
    exact hresponseDisplacementJets j w hw

omit hresponseJets in
/-- Every physical/carrier order `s+k`, `k ≤ rpar`, has the displacement
bound `τ L^s`; its change from the raw family has the sharper factor `τ²`.
These are bounds for the same literal field and original phase consumed by
the raw and sampling constructions (`app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedDisplacementAmplitude_mixed_bounds
    (hresponseDisplacementJets : ∀ j, ∀ w ∈ J,
      ‖iteratedFDeriv ℝ j (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
        τ ^ 2 * Cresp j * L ^ (j - rpar))
    (s k : ℕ) (hk : k ≤ rpar)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ (s + k) (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
      τ * (displacementProfile A₀ A₁ B₀ B₁ (s + k) + Cresp (s + k)) * L ^ s ∧
    ‖iteratedFDeriv ℝ (s + k) (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ -
      fullDisplacementAmplitude T Q F row col Φ Y r τ) w‖ ≤
      τ ^ 2 * Cresp (s + k) * L ^ s := by
  have hh := fullCorrectedDisplacementAmplitude_joint_bounds T Q F row col Φ Y χ B r
    hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
    hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseDisplacementJets (s + k) hw
  have hc := (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ (s + k)).1
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg hτ.le (add_nonneg hc (hCresp _)))),
    hh.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (sq_nonneg τ) (hCresp _)))⟩

omit hresponseJets in
/-- The displacement and its correction have the original joint `cNorm`
profiles with explicit constants, keeping the factors `τ` and `τ²`
respectively (`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem fullCorrectedDisplacementAmplitude_profiles
    (hresponseDisplacementJets : ∀ j, ∀ w ∈ J,
      ‖iteratedFDeriv ℝ j (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
        τ ^ 2 * Cresp j * L ^ (j - rpar)) :
    HasDerivativeProfile J (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ)
      rpar L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1),
        (displacementProfile A₀ A₁ B₀ B₁ i + Cresp i)) ∧
    HasDerivativeProfile J (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ -
      fullDisplacementAmplitude T Q F row col Φ Y r τ) rpar L
      (fun j ↦ τ ^ 2 * ∑ i ∈ Finset.range (j + 1), Cresp i) := by
  have hh (j) (w) (hw : w ∈ J) :=
    fullCorrectedDisplacementAmplitude_joint_bounds T Q F row col Φ Y χ B r
      hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
      hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseDisplacementJets j hw
  exact ⟨profile_of_jet_bounds hL hτ.le
    (fun j ↦ add_nonneg (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).1 (hCresp j))
    (fun j w hw ↦ (hh j w hw).1),
    profile_of_jet_bounds hL (sq_nonneg τ) hCresp (fun j w hw ↦ (hh j w hw).2)⟩

end JanetCartan.CorrectedAtoms
