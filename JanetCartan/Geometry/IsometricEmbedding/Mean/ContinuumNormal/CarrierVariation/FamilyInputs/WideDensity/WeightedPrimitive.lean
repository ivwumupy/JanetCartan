module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity

/-!
# Original wider-density comparison of the full substituted matrix density

The two actual ODE labels are multiplied into the complete canonical density,
including both normal factors, both reduced covectors, every mask and the
Jacobian division. The estimate is derived from the original primitive norms
and the two footpoint differences. It does not assume a density or amplitude
continuity conclusion. The consumer is the source/positive-reference assembly
for `app:ch_background:prop:bg-normalized` and `app:ch_osc:prop:osc-normal`,
Step 4'. Instantiating the primitive bounds remains the parent's obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ContinuumNormalReduction.TransportSymbol AmplitudeDifference
open AmplitudeDifference.PrimitiveDensity
variable {n N : ℕ}

/-- The full inverse-substituted matrix density varies in every finite norm,
uniformly over the original fixed-low density class. The two ODE footpoints
are independent of the Hamilton transport and are retained separately at both
physical positions. Constants precede the density, both coefficient sets,
both inverse maps and the error. The only density reserve is `s + 1 ≤ d₀`;
there is no small-density hypothesis. Sources:
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_weighted_inputDensity_inverse_sub_le_of_primitive_norms
    (D : CoefficientNormCharts n)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ContDiffOn ℝ ∞ J₀ W)
    (hgap₀ : ∀ p ∈ K, δ ≤ |J₀ p|)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (hJ₀M : cNorm K s J₀ ≤ M) :
    ∃ C > 0, ∀ (a a₀ : Coefficients n N) (J : InputVariables n → ℝ)
      (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (g g₀ : Bool → Variables n × Euclidean 2 → Euclidean (n - 1) × Euclidean 3)
      (d : ℝ), 0 ≤ d →
      D.Controls s M (M + 1) 1 a → D.Controls (s + 1) M (M + 1) 1 a₀ →
      ContDiffOn ℝ ∞ J W → (∀ p ∈ K, δ ≤ |J p|) → cNorm K s J ≤ M →
      ContDiffOn ℝ ∞ u Ω → ContDiffOn ℝ ∞ u₀ Ω →
      MapsTo (inverseCoordinates u) Q K → MapsTo (inverseCoordinates u₀) Q K →
      cNorm Q s (inverseCoordinates u) ≤ M → cNorm Q s (inverseCoordinates u₀) ≤ M →
      (∀ b p, p ∈ Q → ContDiffAt ℝ ∞ (g b) p) →
      (∀ b p, p ∈ Q → ContDiffAt ℝ ∞ (g₀ b) p) →
      (∀ b, MapsTo (g b) Q L) → (∀ b, MapsTo (g₀ b) Q L) →
      (∀ b, cNorm Q s (g b) ≤ M) → (∀ b, cNorm Q s (g₀ b) ≤ M) →
      cNorm D.measurement.carrier s (a.measurement - a₀.measurement) ≤ d →
      cNorm D.angular.carrier s (a.angular - a₀.angular) ≤ d →
      cNorm D.high.carrier s (a.high - a₀.high) ≤ d →
      cNorm D.field.carrier s (a.normal - a₀.normal) ≤ d →
      cNorm D.field.carrier s (a.reduced - a₀.reduced) ≤ d →
      cNorm K s (J - J₀) ≤ d →
      cNorm Q s (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      (∀ b, cNorm Q s (g b - g₀ b) ≤ d) →
      ∀ (d₀ : ℕ), s + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      let b := fun p ↦ densityPair v g p • inputDensity a J (inverseCoordinates u p)
      let b₀ := fun p ↦ densityPair v g₀ p • inputDensity a₀ J₀ (inverseCoordinates u₀ p)
      cNorm Q s b ≤ C ∧ cNorm Q s b₀ ≤ C ∧ cNorm Q s (b - b₀) ≤ C * d ∧
      ∀ p ∈ Q, ∀ j ≤ s, ‖iteratedFDeriv ℝ j (b - b₀) p‖ ≤ C * d := by
  have hJ₀at : ∀ p ∈ K, ContDiffAt ℝ ∞ J₀ p :=
    fun p hp ↦ hJ₀.contDiffAt (hW.mem_nhds (hKW hp))
  obtain ⟨R, hR, harray⟩ := exists_shellPrimitiveValues_inverse_sub_le_of_norms
    (N := N) D hK hQ (fun p hp ↦ norm_pos_iff.mp (hε.trans_le (hη p hp)))
    hrange hJ₀at s hM
  obtain ⟨B, hB, hpair⟩ := exists_densityPair_sub_bound hQ hL hconv s hM
  let P : Set (ℝ × ShellPrimitiveValues n N) :=
    {v | ‖v‖ ≤ B + R ∧ δ ≤ |v.2.1.2.2.2.2| ∧ ε ≤ ‖v.2.2.1‖}
  have hP : IsCompact P :=
    (isCompact_closedBall (0 : ℝ × ShellPrimitiveValues n N) (B + R)).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        ((isClosed_le continuous_const continuous_snd.fst.snd.snd.snd.snd.abs).inter
          (isClosed_le continuous_const continuous_snd.snd.fst.norm)))
      (fun p hp ↦ by simpa only [mem_closedBall, dist_zero_right] using hp.1)
  let H : ℝ × ShellPrimitiveValues n N → Matrix (Fin n) (Fin n) ℝ :=
    fun v ↦ v.1 • shellDensityCoefficient v.2
  have hH : ∀ v ∈ P, ContDiffAt ℝ ∞ H v := by
    intro v hv
    exact contDiffAt_fst.smul ((shellDensityCoefficient_contDiffAt
      (abs_pos.mp (hδ.trans_le hv.2.1))
      (norm_pos_iff.mp (hε.trans_le hv.2.2))).comp v contDiffAt_snd)
  obtain ⟨C, hC, hproduct⟩ := exists_fixed_evaluation_bounds hQ hP hH s
    (add_nonneg hB.le hR.le)
  refine ⟨1 + C + C * (B + R), by positivity, ?_⟩
  intro a a₀ J u u₀ g g₀ d hd ha ha₀ hJ hgap hJM hu hu₀ huK hu₀K huM hu₀M
    hg hg₀ hgr hgr₀ hgm hgm₀ hm hang hh hn hq hj hi hgd d₀ horder v hv hvm
  have hJat : ∀ p ∈ K, ContDiffAt ℝ ∞ J p :=
    fun p hp ↦ hJ.contDiffAt (hW.mem_nhds (hKW hp))
  have huat : ∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u) p :=
    fun p hp ↦ (inverseCoordinates_contDiffOn hu).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hu₀at : ∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u₀) p :=
    fun p hp ↦ (inverseCoordinates_contDiffOn hu₀).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have ha' := harray a a₀ J u u₀ d hd ha ha₀ hJat hJM hJ₀M huat hu₀at
    huK hu₀K huM hu₀M hm hang hh hn hq hj hi
  have hv' := hpair v g g₀ d hd hv ((cNorm_mono_order horder).trans hvm)
    hg hg₀ hgr hgr₀ hgm hgm₀ hgd
  have hp := pair_evaluation_bounds hQ s hv' ha'
  let f := fun p ↦ (densityPair v g p, shellPrimitiveValues a J (inverseCoordinates u p))
  let f₀ := fun p ↦ (densityPair v g₀ p, shellPrimitiveValues a₀ J₀ (inverseCoordinates u₀ p))
  have hfr : MapsTo f Q P := by
    intro p hmem
    refine ⟨?_, hgap _ (huK hmem), hη _ (huK hmem)⟩
    have hb := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
      (fun p hp' ↦ (hp.1 p hp').1.of_le (by simp)) hmem (Nat.zero_le s)).trans hp.2.1
    simpa only [norm_iteratedFDeriv_zero, f, f₀, Function.comp_def] using hb
  have hfr₀ : MapsTo f₀ Q P := by
    intro p hmem
    refine ⟨?_, hgap₀ _ (hu₀K hmem), hη _ (hu₀K hmem)⟩
    have hb := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
      (fun p hp' ↦ (hp.1 p hp').2.of_le (by simp)) hmem (Nat.zero_le s)).trans hp.2.2.1
    simpa only [norm_iteratedFDeriv_zero, f, f₀, Function.comp_def] using hb
  have hb := hproduct f f₀ ((B + R) * d) (by positivity)
    (fun p hmem ↦ (hp.1 p hmem).1) (fun p hmem ↦ (hp.1 p hmem).2)
    hfr hfr₀ hp.2.1 hp.2.2.1 hp.2.2.2
  change (∀ p ∈ Q, ContDiffAt ℝ ∞ (H ∘ f) p ∧ ContDiffAt ℝ ∞ (H ∘ f₀) p) ∧
    cNorm Q s (H ∘ f) ≤ C ∧ cNorm Q s (H ∘ f₀) ≤ C ∧
    cNorm Q s (H ∘ f - H ∘ f₀) ≤ C * ((B + R) * d) at hb
  have hfinal : cNorm Q s (H ∘ f - H ∘ f₀) ≤ (1 + C + C * (B + R)) * d :=
    hb.2.2.2.trans (by nlinarith)
  refine ⟨hb.2.1.trans (by nlinarith), hb.2.2.1.trans (by nlinarith), hfinal, ?_⟩
  intro p hmem j hj'
  exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ
    (fun q hmem' ↦ ((hb.1 q hmem').1.sub (hb.1 q hmem').2).of_le (by simp))
      hmem hj').trans hfinal

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
