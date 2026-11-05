module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity.InverseArray

/-!
# Literal shell-density differences from primitive finite norms

This is the density input to `AmplitudeDifference.Integration` for
`paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:eq:bg-full-complex-amplitude`. Both positions, both normal
factors, every mask, the covector norm and the Jacobian division remain in the
literal `inputDensity`. No density or composed-coefficient estimate is assumed.

The five coefficient differences are on the existing primitive norm carriers.
The two additional quantitative inputs, the Jacobian and inverse-coordinate
differences, are produced by
`CarrierVariation.exists_transportForwardJacobian_sub_le`. Its fixed reference
Jacobian supplies the reference smooth jets used here. The parent construction
must instantiate these inputs and the common buffered domains and gaps.

Both sets of coefficient functions occur after the constant. Consequently the
same constant applies to `high := fun r ↦ high (t * r)` for every `t ≥ 1` when
the primitive controls and primitive differences have the stated uniform bounds.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol PrimitiveDensity
variable {n N : ℕ}

/-- Primitive-to-density comparison on a fixed normalized shell, together with
the pointwise jet conclusion consumed by
`norm_iteratedFDeriv_amplitude_sub_le_of_substituted`. All constants precede
both coefficient sets, both genuine inverse functions, the varying Jacobian
and `d`. The reference Jacobian is fixed; its next jets may enter the constant.

`D.Controls` states smoothness and common finite bounds for the five original
functions before any evaluation, at order `s` for `a` and `s+1` for `a₀`. The five small differences
are explicitly measured at order `s` on their original carriers. The final two
small differences are precisely components of the checked producer
`CarrierVariation.exists_transportForwardJacobian_sub_le`. The division is
estimated through the smooth, fixed `shellDensityCoefficient` on a compact
set separated from zero Jacobian and zero covector. Thus no reciprocal- or
density-difference assumption is needed. Source:
`app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_inputDensity_inverse_sub_le_of_primitive_norms
    (D : CoefficientNormCharts n)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ContDiffOn ℝ ∞ J₀ W)
    (hgap₀ : ∀ p ∈ K, δ ≤ |J₀ p|)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (hJ₀M : cNorm K s J₀ ≤ M) :
    ∃ C > 0, ∀ (a a₀ : Coefficients n N) (J : InputVariables n → ℝ)
      (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (d : ℝ),
      0 ≤ d → D.Controls s M (M + 1) 1 a →
      D.Controls (s + 1) M (M + 1) 1 a₀ →
      ContDiffOn ℝ ∞ J W → (∀ p ∈ K, δ ≤ |J p|) → cNorm K s J ≤ M →
      ContDiffOn ℝ ∞ u Ω → ContDiffOn ℝ ∞ u₀ Ω →
      MapsTo (inverseCoordinates u) Q K → MapsTo (inverseCoordinates u₀) Q K →
      cNorm Q s (inverseCoordinates u) ≤ M → cNorm Q s (inverseCoordinates u₀) ≤ M →
      cNorm D.measurement.carrier s (a.measurement - a₀.measurement) ≤ d →
      cNorm D.angular.carrier s (a.angular - a₀.angular) ≤ d →
      cNorm D.high.carrier s (a.high - a₀.high) ≤ d →
      cNorm D.field.carrier s (a.normal - a₀.normal) ≤ d →
      cNorm D.field.carrier s (a.reduced - a₀.reduced) ≤ d →
      cNorm K s (J - J₀) ≤ d →
      cNorm Q s (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      cNorm Q s (inputDensity a J ∘ inverseCoordinates u) ≤ C ∧
      cNorm Q s (inputDensity a₀ J₀ ∘ inverseCoordinates u₀) ≤ C ∧
      cNorm Q s (inputDensity a J ∘ inverseCoordinates u -
        inputDensity a₀ J₀ ∘ inverseCoordinates u₀) ≤ C * d ∧
      ∀ p ∈ Q, ∀ j ≤ s,
        ‖iteratedFDeriv ℝ j (fun q ↦ inputDensity a J (inverseCoordinates u q) -
          inputDensity a₀ J₀ (inverseCoordinates u₀ q)) p‖ ≤ C * d := by
  have hJ₀at : ∀ p ∈ K, ContDiffAt ℝ ∞ J₀ p :=
    fun p hp ↦ hJ₀.contDiffAt (hW.mem_nhds (hKW hp))
  obtain ⟨R, hR, harray⟩ := exists_shellPrimitiveValues_inverse_sub_le_of_norms
    (N := N) D hK hQ (fun p hp ↦ norm_pos_iff.mp (hε.trans_le (hη p hp)))
    hrange hJ₀at s hM
  let P : Set (ShellPrimitiveValues n N) :=
    {v | ‖v‖ ≤ R ∧ δ ≤ |v.1.2.2.2.2| ∧ ε ≤ ‖v.2.1‖}
  have hP : IsCompact P :=
    (isCompact_closedBall (0 : ShellPrimitiveValues n N) R).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        ((isClosed_le continuous_const continuous_fst.snd.snd.snd.snd.abs).inter
          (isClosed_le continuous_const continuous_snd.fst.norm)))
      (fun p hp ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1)
  have hco : ∀ v ∈ P, ContDiffAt ℝ ∞ (@shellDensityCoefficient n N) v :=
    fun v hv ↦ shellDensityCoefficient_contDiffAt
      (abs_pos.mp (hδ.trans_le hv.2.1)) (norm_pos_iff.mp (hε.trans_le hv.2.2))
  obtain ⟨L, hL, hcomp⟩ := exists_cNorm_comp_sub_le_fixed_reference hQ hP hco s hR.le
  let B := compositionMultiplicity s * cNorm P s (@shellDensityCoefficient n N) * (1 + R) ^ s
  have hB : 0 ≤ B := by
    have hh := cNorm_nonneg P s (@shellDensityCoefficient n N)
    dsimp [B, compositionMultiplicity]
    positivity
  refine ⟨1 + B + L * R, by positivity, ?_⟩
  intro a a₀ J u u₀ d hd ha ha₀ hJ hgap hJM hu hu₀ huK hu₀K huM hu₀M hm hang hh hn hq hj hi
  have hJat : ∀ p ∈ K, ContDiffAt ℝ ∞ J p :=
    fun p hp ↦ hJ.contDiffAt (hW.mem_nhds (hKW hp))
  have huat : ∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u) p :=
    fun p hp ↦ (inverseCoordinates_contDiffOn hu).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hu₀at : ∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u₀) p :=
    fun p hp ↦ (inverseCoordinates_contDiffOn hu₀).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hb := harray a a₀ J u u₀ d hd ha ha₀ hJat hJM hJ₀M huat hu₀at
    huK hu₀K huM hu₀M hm hang hh hn hq hj hi
  have hr : MapsTo (shellPrimitiveValues a J ∘ inverseCoordinates u) Q P := by
    intro p hp
    refine ⟨?_, hgap _ (huK hp), hη _ (huK hp)⟩
    have hv := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
      (fun p hp ↦ (hb.1 p hp).1.of_le (by simp)) hp (Nat.zero_le s)
    simpa only [norm_iteratedFDeriv_zero] using hv.trans hb.2.1
  have hr₀ : MapsTo (shellPrimitiveValues a₀ J₀ ∘ inverseCoordinates u₀) Q P := by
    intro p hp
    refine ⟨?_, hgap₀ _ (hu₀K hp), hη _ (hu₀K hp)⟩
    have hv := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
      (fun p hp ↦ (hb.1 p hp).2.of_le (by simp)) hp (Nat.zero_le s)
    simpa only [norm_iteratedFDeriv_zero] using hv.trans hb.2.2.1
  have hsmooth : ∀ p ∈ Q,
      ContDiffAt ℝ ∞ (inputDensity a J ∘ inverseCoordinates u) p ∧
      ContDiffAt ℝ ∞ (inputDensity a₀ J₀ ∘ inverseCoordinates u₀) p :=
    fun p hp ↦ ⟨(hco _ (hr hp)).comp p (hb.1 p hp).1,
      (hco _ (hr₀ hp)).comp p (hb.1 p hp).2⟩
  have hdiff := hcomp shellDensityCoefficient
    (shellPrimitiveValues a J ∘ inverseCoordinates u)
    (shellPrimitiveValues a₀ J₀ ∘ inverseCoordinates u₀) (R * d) (mul_nonneg hR.le hd)
    hco (fun p hp ↦ (hb.1 p hp).1) (fun p hp ↦ (hb.1 p hp).2)
    hr hr₀ hb.2.1 hb.2.2.1
    (by simpa only [sub_self, cNorm_zero] using mul_nonneg hR.le hd) hb.2.2.2
  change cNorm Q s (inputDensity a J ∘ inverseCoordinates u -
    inputDensity a₀ J₀ ∘ inverseCoordinates u₀) ≤ L * (R * d) at hdiff
  have hfinal : cNorm Q s (inputDensity a J ∘ inverseCoordinates u -
      inputDensity a₀ J₀ ∘ inverseCoordinates u₀) ≤ (1 + B + L * R) * d :=
    hdiff.trans (by nlinarith)
  refine ⟨?_, ?_, hfinal, ?_⟩
  · exact (cNorm_comp_le_from_bounds hQ hP s hco (fun p hp ↦ (hb.1 p hp).1)
      hr (cNorm_nonneg _ _ _) le_rfl hb.2.1).trans (by change B ≤ _; nlinarith)
  · exact (cNorm_comp_le_from_bounds hQ hP s hco (fun p hp ↦ (hb.1 p hp).2)
      hr₀ (cNorm_nonneg _ _ _) le_rfl hb.2.2.1).trans (by change B ≤ _; nlinarith)
  · intro p hp j hj'
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
      (fun q hq ↦ ((hsmooth q hq).1.sub (hsmooth q hq).2).of_le (by simp)) hp hj').trans
        hfinal

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
