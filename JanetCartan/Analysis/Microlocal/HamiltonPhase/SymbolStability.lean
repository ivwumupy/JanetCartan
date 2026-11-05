module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SectionData
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolRegularity
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SmoothBufferedChart
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Stability
public import JanetCartan.Analysis.ODE.FlowStability

/-!
# Low-order symbol perturbation estimates

For `app:lem:common-hamilton-phase`, the scalar `cNorm` controls the actual
Hamilton field with one derivative of loss. All estimates are local to the
common symbol domain, so they apply to compact normalized covector patches.
The scalar estimates construct common phase-space flows and stable roots of the
initial energy equation. Inserting these roots gives common section-flow domains
and quantitative joint `C¹` stability of their augmented projections. These bounds
produce common buffered smooth inverse charts and the normalized half gap, with
all domains and perturbation thresholds fixed before the perturbed symbol.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Recover the Hamilton field from the scalar differential, using the product
maximum norm and the Riesz isometry (`app:lem:common-hamilton-phase`). -/
def hamiltonFieldOfDifferential : ((E × E) →L[ℝ] ℝ) →L[ℝ] E × E :=
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (R.comp ((ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip
    (ContinuousLinearMap.inr ℝ E E))).prod
  (-(R.comp ((ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip
    (ContinuousLinearMap.inl ℝ E E))))

set_option backward.isDefEq.respectTransparency false in
/-- Scalar differentiation to Hamilton velocity has norm at most one
(`app:lem:common-hamilton-phase`). -/
theorem norm_hamiltonFieldOfDifferential_le :
    ‖hamiltonFieldOfDifferential (E := E)‖ ≤ 1 := by
  refine (hamiltonFieldOfDifferential (E := E)).opNorm_le_bound zero_le_one ?_
  intro L
  change ‖((InnerProductSpace.toDual ℝ E).symm
    (L.comp (ContinuousLinearMap.inr ℝ E E)),
    -(InnerProductSpace.toDual ℝ E).symm
      (L.comp (ContinuousLinearMap.inl ℝ E E)))‖ ≤ 1 * ‖L‖
  simp only [Prod.norm_def, norm_neg, LinearIsometryEquiv.norm_map, one_mul]
  apply max_le
  · refine (L.comp (ContinuousLinearMap.inr ℝ E E)).opNorm_le_bound (norm_nonneg L) ?_
    intro v
    simpa using L.le_opNorm (0, v)
  · refine (L.comp (ContinuousLinearMap.inl ℝ E E)).opNorm_le_bound (norm_nonneg L) ?_
    intro v
    simpa using L.le_opNorm (v, 0)

/-- The recorded Hamilton field is the field of the actual scalar derivative
on the symbol's domain (`app:lem:common-hamilton-phase`). -/
theorem HomogeneousSymbol.vectorField_eq_differential (H : HomogeneousSymbol E)
    {z : E × E} (hz : z ∈ H.domain) :
    H.vectorField z = hamiltonFieldOfDifferential (fderiv ℝ H.h z) := by
  rw [(H.hasFDerivAt_h z hz).fderiv]
  have hx : (hamiltonDifferential (H.hx z) (H.hp z)).comp
      (ContinuousLinearMap.inl ℝ E E) = InnerProductSpace.toDual ℝ E (H.hx z) := by
    ext v
    simp
  have hp : (hamiltonDifferential (H.hx z) (H.hp z)).comp
      (ContinuousLinearMap.inr ℝ E E) = InnerProductSpace.toDual ℝ E (H.hp z) := by
    ext v
    simp
  simp [hamiltonFieldOfDifferential, hx, hp, HomogeneousSymbol.vectorField]

/-- Hamilton regularity on a smaller open scalar-symbol patch, with one
derivative of loss (`app:lem:common-hamilton-phase`). -/
theorem HomogeneousSymbol.contDiffOn_vectorField_of_subset (H : HomogeneousSymbol E)
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain) {n : ℕ∞ω}
    (hH : ContDiffOn ℝ (n + 1) H.h D) : ContDiffOn ℝ n H.vectorField D := by
  apply (hamiltonFieldOfDifferential.contDiff.comp_contDiffOn
    (hH.fderiv_of_isOpen hD le_rfl)).congr
  intro z hz
  exact H.vectorField_eq_differential (hDH hz)

omit [CompleteSpace E] in
/-- Each scalar jet through order three is bounded by the existing `cNorm`
on a compact common patch (`app:lem:common-hamilton-phase`). -/
theorem norm_symbol_jet_sub_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) {n : ℕ} (hn : n ≤ 3)
    {z : E × E} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ n (fun w ↦ H.h w - H₀.h w) z‖ ≤
      cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  apply CompositionBounds.norm_iteratedFDeriv_le_cNorm ?_ hn hz
  apply hK.bddAbove_image
  intro w hw
  exact (((hH.sub hH₀).contDiffAt (hD.mem_nhds (hKD hw))).continuousAt_iteratedFDeriv
    (by exact_mod_cast hn)).norm.continuousWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise Hamilton-field jet differences cost exactly one scalar-symbol
derivative (`app:lem:common-hamilton-phase`). -/
theorem norm_iteratedFDeriv_vectorField_sub_le
    (H H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    {n : ℕ} (hH : ContDiffOn ℝ (n + 1) H.h D)
    (hH₀ : ContDiffOn ℝ (n + 1) H₀.h D) {z : E × E} (hz : z ∈ D) :
    ‖iteratedFDeriv ℝ n (fun w ↦ H.vectorField w - H₀.vectorField w) z‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) (fun w ↦ H.h w - H₀.h w) z‖ := by
  have he : (fun w ↦ H.vectorField w - H₀.vectorField w) =ᶠ[𝓝 z]
      hamiltonFieldOfDifferential ∘ fderiv ℝ (fun w ↦ H.h w - H₀.h w) := by
    filter_upwards [hD.mem_nhds hz] with w hw
    have hd := (H.hasFDerivAt_h w (hDH hw)).sub (H₀.hasFDerivAt_h w (hDH₀ hw))
    change HasFDerivAt (fun w ↦ H.h w - H₀.h w) _ w at hd
    simp only [Function.comp_apply, hd.fderiv,
      H.vectorField_eq_differential (hDH hw), H₀.vectorField_eq_differential (hDH₀ hw),
      (H.hasFDerivAt_h w (hDH hw)).fderiv,
      (H₀.hasFDerivAt_h w (hDH₀ hw)).fderiv, map_sub]
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hd : ContDiffAt ℝ n (fderiv ℝ (fun w ↦ H.h w - H₀.h w)) z :=
    ((hH.sub hH₀).fderiv_of_isOpen hD (by simp)).contDiffAt (hD.mem_nhds hz)
  calc
    _ ≤ ‖hamiltonFieldOfDifferential (E := E)‖ *
        ‖iteratedFDeriv ℝ n (fderiv ℝ (fun w ↦ H.h w - H₀.h w)) z‖ :=
      (hamiltonFieldOfDifferential (E := E)).norm_iteratedFDeriv_comp_left (n := n) hd le_rfl
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun w ↦ H.h w - H₀.h w)) z‖ :=
      mul_le_mul_of_nonneg_right (norm_hamiltonFieldOfDifferential_le (E := E)) (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- On a compact common patch the `C³` scalar seminorm controls every Hamilton
field jet through order two. Bounded derivative images are derived from local
smoothness and compactness (`app:lem:common-hamilton-phase`). -/
theorem norm_vectorField_jet_sub_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) {n : ℕ} (hn : n ≤ 2)
    {z : E × E} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ n (fun w ↦ H.vectorField w - H₀.vectorField w) z‖ ≤
      cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  have hn' : (n + 1 : ℕ∞ω) ≤ 3 := by exact_mod_cast (show n + 1 ≤ 3 by omega)
  apply (norm_iteratedFDeriv_vectorField_sub_le H H₀ hD hDH hDH₀
    (hH.of_le hn') (hH₀.of_le hn') (hKD hz)).trans
  exact norm_symbol_jet_sub_le_cNorm_three H H₀ hD hH hH₀ hK hKD (by omega) hz

/-- Uniform value stability of the actual Hamilton field from scalar `C³`
closeness (`app:lem:common-hamilton-phase`). -/
theorem norm_vectorField_sub_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) {z : E × E} (hz : z ∈ K) :
    ‖H.vectorField z - H₀.vectorField z‖ ≤ cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_vectorField_jet_sub_le_cNorm_three H H₀ hD hDH hDH₀ hH hH₀ hK hKD
      (n := 0) (by omega) hz

/-- Uniform first-derivative stability of the Hamilton field from scalar
`C³` closeness (`app:lem:common-hamilton-phase`). -/
theorem norm_fderiv_vectorField_sub_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) {z : E × E} (hz : z ∈ K) :
    ‖fderiv ℝ H.vectorField z - fderiv ℝ H₀.vectorField z‖ ≤
      cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  have hd : DifferentiableAt ℝ H.vectorField z :=
    ((H.contDiffOn_vectorField_of_subset hD hDH (n := 2) (by convert hH using 1; norm_num)).contDiffAt
      (hD.mem_nhds (hKD hz))).differentiableAt (by norm_num)
  have hd₀ : DifferentiableAt ℝ H₀.vectorField z :=
    ((H₀.contDiffOn_vectorField_of_subset hD hDH₀ (n := 2) (by convert hH₀ using 1; norm_num)).contDiffAt
      (hD.mem_nhds (hKD hz))).differentiableAt (by norm_num)
  have hb := norm_vectorField_jet_sub_le_cNorm_three H H₀ hD hDH hDH₀ hH hH₀ hK hKD
    (n := 1) (by omega) hz
  simpa only [norm_iteratedFDeriv_one, fderiv_fun_sub hd hd₀] using hb

/-- The `C²` Hamilton-field perturbation seminorm is at most three times the
scalar `C³` perturbation seminorm (`app:lem:common-hamilton-phase`). -/
theorem cNorm_two_vectorField_sub_le_three_mul
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    cNorm K 2 (fun w ↦ H.vectorField w - H₀.vectorField w) ≤
      3 * cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  apply (CompositionBounds.cNorm_le_sum
    (B := fun _ ↦ cNorm K 3 (fun w ↦ H.h w - H₀.h w))
    (fun _ _ ↦ CompositionBounds.cNorm_nonneg _ _ _)
    (fun _ hn _ hz ↦ norm_vectorField_jet_sub_le_cNorm_three
      H H₀ hD hDH hDH₀ hH hH₀ hK hKD hn hz)).trans_eq
  simp

/-- The normal Hamilton velocity changes by at most the scalar `C³` distance
times the normal's length (`app:lem:common-hamilton-phase`). -/
theorem abs_normal_velocity_sub_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) (ν : E) {z : E × E} (hz : z ∈ K) :
    |⟪H.hp z, ν⟫_ℝ - ⟪H₀.hp z, ν⟫_ℝ| ≤
      cNorm K 3 (fun w ↦ H.h w - H₀.h w) * ‖ν‖ := by
  rw [← inner_sub_left]
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg ν)
  exact (norm_fst_le (H.vectorField z - H₀.vectorField z)).trans
    (norm_vectorField_sub_le_cNorm_three H H₀ hD hDH hDH₀ hH hH₀ hK hKD hz)

/-- A reference normal velocity gap persists on the entire compact patch
under a fixed scalar `C³` perturbation (`app:lem:common-hamilton-phase`). -/
theorem normal_velocity_half_gap_of_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hDH₀ : D ⊆ H₀.domain)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D) (ν : E) (hν : ‖ν‖ = 1)
    {c : ℝ} (hgap : ∀ z ∈ K, c ≤ |⟪H₀.hp z, ν⟫_ℝ|)
    (hclose : cNorm K 3 (fun w ↦ H.h w - H₀.h w) ≤ c / 2) :
    ∀ z ∈ K, c / 2 ≤ |⟪H.hp z, ν⟫_ℝ| := by
  intro z hz
  have hb := abs_normal_velocity_sub_le_cNorm_three H H₀ hD hDH hDH₀ hH hH₀ hK hKD ν hz
  rw [hν, mul_one] at hb
  have ht := abs_sub_abs_le_abs_sub ⟪H₀.hp z, ν⟫_ℝ ⟪H.hp z, ν⟫_ℝ
  rw [abs_sub_comm] at ht
  linarith [hgap z hz]

/-- Common phase-space flows from scalar `C³` closeness on a fixed buffered
ball (`app:lem:common-hamilton-phase`). The initial radius, two-sided time,
comparison constant and perturbation threshold are chosen before the perturbed
symbol. The ODE, range containment and variational equation are retained in
`ODE.IsSmoothFlowOn`. Initial energy roots are inserted in a subsequent step. -/
theorem exists_common_symbol_flows [FiniteDimensional ℝ E]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} {z₀ : E × E} {R : ℝ}
    (hD : IsOpen D) (hDH₀ : D ⊆ H₀.domain) (hR : 0 < R)
    (hRD : closedBall z₀ R ⊆ D) (hH₀ : ContDiffOn ℝ ∞ H₀.h D) :
    ∃ r > (0 : ℝ), ∃ T > (0 : ℝ), ∃ C > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∃ Ψ₀ : (E × E) × ℝ → E × E,
        ODE.IsSmoothFlowOn H₀.vectorField z₀ R r T Ψ₀ ∧
        ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
          cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
          ∃ Ψ : (E × E) × ℝ → E × E,
            ODE.IsSmoothFlowOn H.vectorField z₀ R r T Ψ ∧
            ∀ q ∈ closedBall z₀ (r / 2) ×ˢ Icc (-T / 2) (T / 2),
              ‖Ψ q - Ψ₀ q‖ ≤ C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
              ‖fderiv ℝ Ψ q - fderiv ℝ Ψ₀ q‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) := by
  have hV₀ : ContDiffOn ℝ ∞ H₀.vectorField D :=
    H₀.contDiffOn_vectorField_of_subset hD hDH₀ (by simpa using hH₀)
  obtain ⟨r, hr, T, hT, C, hC, δ, hδ, Ψ₀, hΨ₀, hex⟩ :=
    ODE.exists_common_smoothFlowOn_with_cNorm_stability hD hR hRD hV₀
  refine ⟨r, hr, T, hT, C * 3, mul_pos hC (by norm_num), δ / 3,
    div_pos hδ (by norm_num), Ψ₀, hΨ₀, ?_⟩
  intro H hDH hH hsmall
  have hb := cNorm_two_vectorField_sub_le_three_mul H H₀ hD hDH hDH₀
    (hH.of_le (by simp)) (hH₀.of_le (by simp)) (isCompact_closedBall _ _) hRD
  have hV : ContDiffOn ℝ ∞ H.vectorField D :=
    H.contDiffOn_vectorField_of_subset hD hDH (by simpa using hH)
  obtain ⟨Ψ, hΨ, hclose⟩ := hex H.vectorField hV (by
    change cNorm (closedBall z₀ R) 2 (fun z ↦ H.vectorField z - H₀.vectorField z) ≤ δ
    linarith)
  refine ⟨Ψ, hΨ, fun q hq ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left hb hC.le
  simpa only [mul_assoc] using
    And.intro ((hclose q hq).1.trans h) ((hclose q hq).2.trans h)

section SectionEnergy

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

omit [CompleteSpace E] in
/-- At the reference root the perturbed energy has a small residual at the
same canonical energy. No equality of the perturbed and reference roots is
asserted (`app:lem:common-hamilton-phase`). -/
theorem sectionEnergy_defect_le_cNorm_three
    (H H₀ : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hH : ContDiffOn ℝ 3 H.h D) (hH₀ : ContDiffOn ℝ 3 H₀.h D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s : InitialData U} {τ : ℝ}
    (hz : transverseSectionState j ν (s, τ) ∈ K)
    (he : H₀.h (transverseSectionState j ν (s, τ)) = s.2.1) :
    |sectionEnergyEquation H j ν (s, τ)| ≤ cNorm K 3 (fun w ↦ H.h w - H₀.h w) := by
  have hb := norm_symbol_jet_sub_le_cNorm_three H H₀ hD hH hH₀ hK hKD
    (n := 0) (by omega) hz
  simpa only [norm_iteratedFDeriv_zero, he, Real.norm_eq_abs, sectionEnergyEquation] using hb

omit [CompleteSpace E] in
/-- Pulling the scalar-symbol perturbation back to the transverse section
controls the `C²` energy-equation perturbation by a fixed multiple of the scalar
`C³` seminorm. The canonical energy cancels exactly. This is the input of
`exists_uniform_C1_stable_sectionRoot` (`app:lem:common-hamilton-phase`). -/
theorem exists_sectionEnergy_cNorm_bound
    (j : U →ₗᵢ[ℝ] E) (ν : E) {K : Set (InitialData U × ℝ)} (hK : IsCompact K) :
    ∃ B > (0 : ℝ), ∀ (H H₀ : HomogeneousSymbol E) (D L : Set (E × E)),
      IsOpen D → ContDiffOn ℝ 3 H.h D → ContDiffOn ℝ 3 H₀.h D →
      IsCompact L → L ⊆ D → MapsTo (transverseSectionState j ν) K L →
      cNorm K 2 (sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν) ≤
        B * cNorm L 3 (fun z ↦ H.h z - H₀.h z) := by
  let B := compositionMultiplicity 2 * (1 + cNorm K 2 (transverseSectionState j ν)) ^ 2
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro H H₀ D L hD hH hH₀ hL hLD hmap
  have he : sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν =
      (fun z ↦ H.h z - H₀.h z) ∘ transverseSectionState j ν := by
    funext w
    simp only [Pi.sub_apply, sectionEnergyEquation, Function.comp_apply]
    ring
  rw [he]
  have hs : ContDiff ℝ 2 (transverseSectionState j ν) :=
    (contDiff_transverseSectionState j ν).of_le (by simp)
  have hb := cNorm_comp_le_polynomial (s := K) (r := 2)
    (fun _ _ ↦ hs.contDiffAt)
    (fun w hw ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hLD (hmap hw)))).of_le
      (by norm_num))
    (fun _ hn ↦ CompositionBounds.bddAbove_derivative_image hK hs hn)
    (CompositionBounds.cNorm_nonneg L 3 (fun z ↦ H.h z - H₀.h z))
    (fun n hn w hw ↦ norm_symbol_jet_sub_le_cNorm_three H H₀ hD hH hH₀ hL hLD
      (by omega) (hmap hw))
  calc
    _ ≤ B * cNorm L 3 (fun z ↦ H.h z - H₀.h z) := by
      convert hb using 1
      dsimp [B]
      ring
    _ ≤ (1 + |B|) * cNorm L 3 (fun z ↦ H.h z - H₀.h z) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self B])
        (CompositionBounds.cNorm_nonneg _ _ _)

omit [CompleteSpace E] in
/-- Construct the actual perturbed normal momentum at the unchanged canonical
energy from scalar `C³` closeness (`app:lem:common-hamilton-phase`). All radii,
compact sets, the transverse gap and stability constants precede the perturbed
symbol. In particular the perturbed symbol need not take the prescribed energy
at the reference normal momentum. The image of the fixed cylinder is the compact
normalized state patch on which the scalar seminorm is measured. -/
theorem exists_uniform_C1_stable_sectionRoot [FiniteDimensional ℝ U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ (r a c C δ : ℝ) (g₀ : InitialData U → ℝ),
      0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧ 0 < δ ∧
      let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
      let L := transverseSectionState j ν '' K
      IsCompact K ∧ IsCompact L ∧ L ⊆ D ∧ g₀ s₀ = τ₀ ∧
      ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)) ∧
      (∀ s ∈ ball s₀ (2 * r), g₀ s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
        H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ g : InitialData U → ℝ, ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            transverseSectionState j ν (s, g s) ∈ L ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          (∀ s ∈ ball s₀ (2 * r), ∀ τ ∈ Icc (τ₀ - a) (τ₀ + a),
            H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ) ∧
          (∀ s ∈ closedBall s₀ r,
            |g s - g₀ s| ≤ C * cNorm L 3 (fun z ↦ H.h z - H₀.h z) ∧
            ‖fderiv ℝ g s - fderiv ℝ g₀ s‖ ≤
              C * cNorm L 3 (fun z ↦ H.h z - H₀.h z)) := by
  let S := transverseSectionState j ν ⁻¹' D
  have hS : IsOpen S := hD.preimage (contDiff_transverseSectionState j ν).continuous
  have hf₀ : ContDiffOn ℝ ∞ (sectionEnergyEquation H₀ j ν) S :=
    (hH₀.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hw ↦ hw)).sub contDiff_fst.snd.fst.contDiffOn
  have hd : CharacteristicRoot.scalarDerivative (sectionEnergyEquation H₀ j ν) (s₀, τ₀) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation H₀ j ν (hDH₀ hbase)]
    exact htrans
  obtain ⟨r, a, c, C, δ, g₀, hr, ha, hc, hC, hδ, hK, hKS, hg₀base, hg₀, hroot₀, hpert⟩ :=
    CharacteristicRoot.exists_uniform_C1_stable_root hS hf₀ hbase
      (show sectionEnergyEquation H₀ j ν (s₀, τ₀) = 0 from sub_eq_zero.mpr henergy) hd
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let L := transverseSectionState j ν '' K
  have hL : IsCompact L := hK.image (contDiff_transverseSectionState j ν).continuous
  have hLD : L ⊆ D := by rintro _ ⟨w, hw, rfl⟩; exact hKS hw
  obtain ⟨B, hB, hbound⟩ := exists_sectionEnergy_cNorm_bound j ν hK
  refine ⟨r, a, c, C * B, δ / B, g₀, hr, ha, hc, mul_pos hC hB,
    div_pos hδ hB, hK, hL, hLD, hg₀base, hg₀, ?_, ?_⟩
  · intro s hs
    exact ⟨(hroot₀ s hs).1, sub_eq_zero.mp (hroot₀ s hs).2⟩
  intro H hDH hH hsmall
  have hf : ContDiffOn ℝ ∞ (sectionEnergyEquation H j ν) S :=
    (hH.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hw ↦ hw)).sub contDiff_fst.snd.fst.contDiffOn
  have hb := hbound H H₀ D L hD (hH.of_le (by simp)) (hH₀.of_le (by simp))
    hL hLD (fun _ hw ↦ mem_image_of_mem _ hw)
  have hsmall' : cNorm K 2 (sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν) ≤ δ := by
    apply hb.trans
    calc
      B * cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ B * (δ / B) :=
        mul_le_mul_of_nonneg_left hsmall hB.le
      _ = δ := mul_div_cancel₀ δ hB.ne'
  obtain ⟨g, hg, hroot, huniq, hclose⟩ := hpert (sectionEnergyEquation H j ν) hf hsmall'
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨ht, hmem, he, hgap⟩ := hroot s hs
    refine ⟨ht, mem_image_of_mem _ hmem, sub_eq_zero.mp he, ?_⟩
    rwa [scalarDerivative_sectionEnergyEquation H j ν (hDH (hKS hmem))] at hgap
  · intro s hs τ hτ
    simpa only [sectionEnergyEquation, sub_eq_zero] using huniq s hs τ hτ
  · intro s hs
    have h := mul_le_mul_of_nonneg_left hb hC.le
    simpa only [mul_assoc] using
      And.intro ((hclose s hs).1.trans h) ((hclose s hs).2.trans h)

/-- The actual section flow obtained by inserting the symbol's own normal
energy root (`app:lem:common-hamilton-phase`). -/
def sectionFlowState (j : U →ₗᵢ[ℝ] E) (ν : E) (g : InitialData U → ℝ)
    (Ψ : (E × E) × ℝ → E × E) (q : ℝ × InitialData U) : E × E :=
  Ψ (transverseSectionState j ν (q.2, g q.2), q.1)

/-- The augmented position projection of the constructed section flow. Its
canonical covector coordinate is unchanged (`app:lem:common-hamilton-phase`). -/
def sectionAugmentedProjection (j : U →ₗᵢ[ℝ] E) (ν : E) (g : InitialData U → ℝ)
    (Ψ : (E × E) × ℝ → E × E) (q : ℝ × InitialData U) : E × (ℝ × U) :=
  ((sectionFlowState j ν g Ψ q).1, q.2.2)

omit [CompleteSpace E] in
/-- Only the normal momentum changes when two initial roots are inserted at
the same canonical datum (`app:lem:common-hamilton-phase`). -/
theorem norm_transverseSectionState_root_sub (j : U →ₗᵢ[ℝ] E) (ν : E)
    (g g₀ : InitialData U → ℝ) (s : InitialData U) :
    ‖transverseSectionState j ν (s, g s) - transverseSectionState j ν (s, g₀ s)‖ =
      |g s - g₀ s| * ‖ν‖ := by
  have he : transverseSectionState j ν (s, g s) - transverseSectionState j ν (s, g₀ s) =
      (0, (g s - g₀ s) • ν) := by
    apply Prod.ext <;> simp [transverseSectionState, sub_smul]
  rw [he]
  simp [Prod.norm_def, norm_smul, Real.norm_eq_abs]
  positivity

omit [CompleteSpace E] in
/-- Smoothness and the actual ODE after inserting an initial root. This helper
is used by `exists_common_rooted_symbol_flows`, where all its root and flow
hypotheses are constructed from scalar-symbol closeness
(`app:lem:common-hamilton-phase`). -/
theorem sectionFlowState_properties
    (H : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    {g : InitialData U → ℝ} {Ψ : (E × E) × ℝ → E × E}
    {z₀ : E × E} {R ρ T : ℝ} {P : Set (InitialData U)}
    (hΨ : ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ)
    (hg : ContDiffOn ℝ ∞ g P)
    (hinit : ∀ s ∈ P, transverseSectionState j ν (s, g s) ∈ ball z₀ ρ) :
    ContDiffOn ℝ ∞ (sectionFlowState j ν g Ψ) (Ioo (-T) T ×ˢ P) ∧
    (∀ s ∈ P, sectionFlowState j ν g Ψ (0, s) = transverseSectionState j ν (s, g s)) ∧
    (∀ s ∈ P, ∀ t ∈ Icc (-T) T, sectionFlowState j ν g Ψ (t, s) ∈ closedBall z₀ R) ∧
    (∀ s ∈ P, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ sectionFlowState j ν g Ψ (u, s))
        (H.vectorField (sectionFlowState j ν g Ψ (t, s))) t) := by
  have hi : ContDiffOn ℝ ∞ (fun s ↦ transverseSectionState j ν (s, g s)) P :=
    (contDiff_transverseSectionState j ν).comp_contDiffOn (contDiffOn_id.prodMk hg)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hΨ.smooth.comp
      ((hi.comp contDiffOn_snd (fun _ hq ↦ hq.2)).prodMk contDiffOn_fst)
      (fun q hq ↦ ⟨hinit q.2 hq.2, hq.1⟩)
  · exact fun s hs ↦ hΨ.initial _ (ball_subset_closedBall (hinit s hs))
  · exact fun s hs t ht ↦ hΨ.range _ (ball_subset_closedBall (hinit s hs)) t ht
  · exact fun s hs _ ht ↦ hΨ.hasDerivAt (ball_subset_closedBall (hinit s hs)) ht

/-- Construct roots and flows simultaneously using a single scalar `C³`
seminorm on a fixed state-space ball (`app:lem:common-hamilton-phase`). The root
cylinder is chosen inside the common flow's initial ball; hence every perturbed
root produces a trajectory on the same two-sided interval, with state-space
containment and the actual ODE. The augmented projections are quantitatively
`C⁰` close, including the change of initial root. The separate `C¹` root and flow
bounds are retained for the subsequent derivative comparison. -/
theorem exists_common_rooted_symbol_flows [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ R : ℝ}
    (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ r > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ), ∃ C > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∃ (g₀ : InitialData U → ℝ) (Ψ₀ : (E × E) × ℝ → E × E),
        ODE.IsSmoothFlowOn H₀.vectorField z₀ R ρ T Ψ₀ ∧
        g₀ s₀ = τ₀ ∧ ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)) ∧
        (∀ s ∈ ball s₀ (2 * r),
          transverseSectionState j ν (s, g₀ s) ∈ ball z₀ (ρ / 2) ∧
          H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1) ∧
        ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
          cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
          ∃ (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E),
            ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ ∧
            ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
            (∀ s ∈ ball s₀ (2 * r),
              transverseSectionState j ν (s, g s) ∈ ball z₀ (ρ / 2) ∧
              H.h (transverseSectionState j ν (s, g s)) = s.2.1) ∧
            (∀ s ∈ closedBall s₀ r,
              |g s - g₀ s| ≤ C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
              ‖fderiv ℝ g s - fderiv ℝ g₀ s‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)) ∧
            (∀ q ∈ closedBall z₀ (ρ / 2) ×ˢ Icc (-T / 2) (T / 2),
              ‖Ψ q - Ψ₀ q‖ ≤ C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
              ‖fderiv ℝ Ψ q - fderiv ℝ Ψ₀ q‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)) ∧
            (∀ q ∈ Icc (-T / 2) (T / 2) ×ˢ closedBall s₀ r,
              ‖sectionAugmentedProjection j ν g Ψ q - sectionAugmentedProjection j ν g₀ Ψ₀ q‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)) ∧
            ContDiffOn ℝ ∞ (sectionFlowState j ν g Ψ)
              (Ioo (-T) T ×ˢ ball s₀ (2 * r)) ∧
            (∀ s ∈ ball s₀ (2 * r),
              sectionFlowState j ν g Ψ (0, s) = transverseSectionState j ν (s, g s)) ∧
            (∀ s ∈ ball s₀ (2 * r), ∀ t ∈ Icc (-T) T,
              sectionFlowState j ν g Ψ (t, s) ∈ closedBall z₀ R) ∧
            (∀ s ∈ ball s₀ (2 * r), ∀ t ∈ Ioo (-T) T,
              HasDerivAt (fun u ↦ sectionFlowState j ν g Ψ (u, s))
                (H.vectorField (sectionFlowState j ν g Ψ (t, s))) t) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨ρ, hρ, T, hT, Cf, hCf, δf, hδf, Ψ₀, hΨ₀, hflows⟩ :=
    exists_common_symbol_flows H₀ hD hDH₀ hR hRD hH₀
  let D' := D ∩ ball z₀ (min R (ρ / 2))
  have hD' : IsOpen D' := hD.inter isOpen_ball
  have hbase : z₀ ∈ D' :=
    ⟨hRD (mem_closedBall_self hR.le), mem_ball_self (lt_min hR (half_pos hρ))⟩
  obtain ⟨r, a, c, Cr, δr, g₀, hr, _, _, hCr, hδr,
      hK, _, hLD', hg₀base, hg₀, hroot₀, hroots⟩ :=
    exists_uniform_C1_stable_sectionRoot H₀ hD' (inter_subset_left.trans hDH₀)
      (hH₀.mono inter_subset_left) j ν hbase henergy htrans
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let L := transverseSectionState j ν '' K
  have hLball : L ⊆ ball z₀ (ρ / 2) :=
    fun _ hz ↦ (ball_subset_ball (min_le_right _ _)) (hLD' hz).2
  have hLR : L ⊆ closedBall z₀ R :=
    fun _ hz ↦ ball_subset_closedBall ((ball_subset_ball (min_le_left _ _)) (hLD' hz).2)
  have hroot₀' : ∀ s ∈ ball s₀ (2 * r),
      transverseSectionState j ν (s, g₀ s) ∈ ball z₀ (ρ / 2) ∧
      H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1 := by
    intro s hs
    exact ⟨hLball (mem_image_of_mem _
      ⟨ball_subset_closedBall hs, Ioo_subset_Icc_self (hroot₀ s hs).1⟩), (hroot₀ s hs).2⟩
  let Q := closedBall z₀ (ρ / 2) ×ˢ Icc (-T / 2) (T / 2)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hQsub : Q ⊆ ball z₀ ρ ×ˢ Ioo (-T) T := by
    intro q hq
    exact ⟨closedBall_subset_ball (by linarith) hq.1,
      ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  obtain ⟨Lf, hLf⟩ := (hΨ₀.smooth.mono hQsub).exists_lipschitzOnWith
    (by simp) ((convex_closedBall _ _).prod (convex_Icc _ _)) hQ
  let C := Cf + Cr + (Lf : ℝ) * Cr * ‖ν‖
  have hterm : 0 ≤ (Lf : ℝ) * Cr * ‖ν‖ := by positivity
  have hCCf : Cf ≤ C := by dsimp [C]; linarith
  have hCCr : Cr ≤ C := by dsimp [C]; linarith
  have hC : 0 < C := hCf.trans_le hCCf
  refine ⟨r, hr, ρ, hρ, T, hT, C, hC,
    min δf δr, lt_min hδf hδr, g₀, Ψ₀, hΨ₀, hg₀base, hg₀, hroot₀', ?_⟩
  intro H hDH hH hsmall
  have hnorm : cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤
      cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) :=
    cNorm_mono_set_of_contDiffAt hLR (isCompact_closedBall _ _)
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp))
  obtain ⟨g, hg, hroot, _, hcloseg⟩ := hroots H (inter_subset_left.trans hDH)
    (hH.mono inter_subset_left) (hnorm.trans (hsmall.trans (min_le_right _ _)))
  obtain ⟨Ψ, hΨ, hcloseΨ⟩ := hflows H hDH hH (hsmall.trans (min_le_left _ _))
  have hroot' : ∀ s ∈ ball s₀ (2 * r),
      transverseSectionState j ν (s, g s) ∈ ball z₀ (ρ / 2) ∧
      H.h (transverseSectionState j ν (s, g s)) = s.2.1 :=
    fun s hs ↦ ⟨hLball (hroot s hs).2.1, (hroot s hs).2.2.1⟩
  have hinit : ∀ s ∈ ball s₀ (2 * r), transverseSectionState j ν (s, g s) ∈ ball z₀ ρ :=
    fun s hs ↦ ball_subset_ball (by linarith) (hroot' s hs).1
  refine ⟨g, Ψ, hΨ, hg, hroot', ?_, ?_, ?_, sectionFlowState_properties H j ν hΨ hg hinit⟩
  · intro s hs
    have hb : Cr * cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤
        C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) :=
      mul_le_mul hCCr hnorm (CompositionBounds.cNorm_nonneg _ _ _) hC.le
    exact ⟨((hcloseg s hs).1).trans hb, ((hcloseg s hs).2).trans hb⟩
  · intro q hq
    have hb := mul_le_mul_of_nonneg_right hCCf
      (CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z))
    exact ⟨((hcloseΨ q hq).1).trans hb, ((hcloseΨ q hq).2).trans hb⟩

  · intro q hq
    have hs : q.2 ∈ ball s₀ (2 * r) := closedBall_subset_ball (by linarith) hq.2
    let x := (transverseSectionState j ν (q.2, g q.2), q.1)
    let y := (transverseSectionState j ν (q.2, g₀ q.2), q.1)
    have hx : x ∈ Q := ⟨ball_subset_closedBall (hroot' q.2 hs).1, hq.1⟩
    have hy : y ∈ Q := ⟨ball_subset_closedBall (hroot₀' q.2 hs).1, hq.1⟩
    have hxy : ‖x - y‖ = |g q.2 - g₀ q.2| * ‖ν‖ := by
      calc
        _ = ‖transverseSectionState j ν (q.2, g q.2) -
            transverseSectionState j ν (q.2, g₀ q.2)‖ := by
          change max ‖transverseSectionState j ν (q.2, g q.2) -
            transverseSectionState j ν (q.2, g₀ q.2)‖ ‖q.1 - q.1‖ = _
          rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
        _ = _ := norm_transverseSectionState_root_sub j ν g g₀ q.2
    have hlip : ‖Ψ₀ x - Ψ₀ y‖ ≤ (Lf : ℝ) * (|g q.2 - g₀ q.2| * ‖ν‖) := by
      simpa only [dist_eq_norm, hxy] using hLf.dist_le_mul x hx y hy
    have hbroot := (hcloseg q.2 hq.2).1.trans (mul_le_mul_of_nonneg_left hnorm hCr.le)
    have hbflow := (hcloseΨ x hx).1
    have hstate : ‖Ψ x - Ψ₀ y‖ ≤
        C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) := by
      calc
        _ ≤ ‖Ψ x - Ψ₀ x‖ + ‖Ψ₀ x - Ψ₀ y‖ := by
          simpa only [sub_add_sub_cancel] using norm_add_le (Ψ x - Ψ₀ x) (Ψ₀ x - Ψ₀ y)
        _ ≤ Cf * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) +
            (Lf : ℝ) * ((Cr * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)) * ‖ν‖) :=
          add_le_add hbflow (hlip.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hbroot (norm_nonneg ν)) Lf.coe_nonneg))
        _ ≤ _ := by
          dsimp [C]
          nlinarith [mul_nonneg hCr.le (CompositionBounds.cNorm_nonneg
            (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z))]
    have hproj := (norm_fst_le (Ψ x - Ψ₀ y)).trans hstate
    change max ‖(Ψ x).1 - (Ψ₀ y).1‖ ‖q.2.2 - q.2.2‖ ≤ _
    rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
    exact hproj

omit [CompleteSpace E] in
/-- Package the constructed section trajectories with their actual derivatives and
variational equation, for the buffered projection consumer
(`app:lem:common-hamilton-phase`). -/
theorem exists_hamiltonFlow_of_sectionFlow
    (H : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {g : InitialData U → ℝ} {Ψ : (E × E) × ℝ → E × E}
    {z₀ : E × E} {R ρ T t : ℝ} {P : Set (InitialData U)}
    (hP : IsOpen P) (ht : 0 < t) (htT : t ≤ T)
    (hΨ : ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ)
    (hfield : ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H.vectorField z)
    (hmem : closedBall z₀ R ⊆ H.domain)
    (hg : ContDiffOn ℝ ∞ g P)
    (hinit : ∀ s ∈ P, transverseSectionState j ν (s, g s) ∈ ball z₀ ρ)
    (henergy : ∀ s ∈ P, H.h (transverseSectionState j ν (s, g s)) = s.2.1) :
    ∃ Φ : HamiltonFlow H U,
      Φ.time = Ioo (-t) t ∧ Φ.parameters = P ∧
      Φ.sectionMap = j.toContinuousLinearMap ∧
      Φ.position = (fun q ↦ (sectionFlowState j ν g Ψ q).1) ∧
      Φ.momentum = (fun q ↦ (sectionFlowState j ν g Ψ q).2) ∧
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) := by
  let ι := fun s ↦ transverseSectionState j ν (s, g s)
  have hιcd : ContDiffOn ℝ ∞ ι P :=
    (contDiff_transverseSectionState j ν).comp_contDiffOn (contDiffOn_id.prodMk hg)
  have hι (s : InitialData U) (hs : s ∈ P) : DifferentiableAt ℝ ι s :=
    (hιcd.contDiffAt (hP.mem_nhds hs)).differentiableAt (by simp)
  have htime : Ioo (-t) t ⊆ Ioo (-T) T := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  let Z := sectionFlowState j ν g Ψ
  let V := fun q : ℝ × InitialData U ↦
    (ODE.flowInitialDerivative Ψ (ι q.2) q.1).comp (fderiv ℝ ι q.2)
  have hZrange (u : ℝ) (hu : u ∈ Ioo (-t) t) (s : InitialData U) (hs : s ∈ P) :
      Z (u, s) ∈ closedBall z₀ R :=
    hΨ.range _ (ball_subset_closedBall (hinit s hs)) u (Ioo_subset_Icc_self (htime hu))
  have hZmem (u : ℝ) (hu : u ∈ Ioo (-t) t) (s : InitialData U) (hs : s ∈ P) :
      Z (u, s) ∈ H.domain := hmem (hZrange u hu s hs)
  have hZ (u : ℝ) (hu : u ∈ Ioo (-t) t) (s : InitialData U) (hs : s ∈ P) :
      HasFDerivAt Z (flowDifferential (H.vectorField (Z (u, s))) (V (u, s))) (u, s) :=
    hasFDerivAt_sectionFlow (ι := ι)
      ((hΨ.smooth.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        ⟨hinit s hs, htime hu⟩)).differentiableAt (by simp))
      (hΨ.hasDerivAt (ball_subset_closedBall (hinit s hs)) (htime hu)) (hι s hs).hasFDerivAt
  have hstart (s : InitialData U) (hs : s ∈ P) : Z (0, s) = ι s :=
    hΨ.initial _ (ball_subset_closedBall (hinit s hs))
  let Φ : HamiltonFlow H U := {
    time := Ioo (-t) t
    isOpen_time := isOpen_Ioo
    isPreconnected_time := isPreconnected_Ioo
    zero_mem_time := ⟨by linarith, ht⟩
    parameters := P
    isOpen_parameters := hP
    sectionMap := j.toContinuousLinearMap
    position := fun q ↦ (Z q).1
    momentum := fun q ↦ (Z q).2
    positionVariation := fun q ↦ (ContinuousLinearMap.fst ℝ E E).comp (V q)
    momentumVariation := fun q ↦ (ContinuousLinearMap.snd ℝ E E).comp (V q)
    state_mem := hZmem
    position_derivative := by
      intro u hu s hs
      convert! (hZ u hu s hs).fst using 1
    momentum_derivative := by
      intro u hu s hs
      convert! (hZ u hu s hs).snd using 1
    variation_equation := by
      intro u hu s hs v
      have hvar := (hΨ.variation _ (hinit s hs) u (htime hu)).clm_apply
        (hasDerivAt_const u (fderiv ℝ ι s v))
      have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt u hvar
      have he := H.vectorField_fderiv_fst (hZmem u hu s hs)
        (hfield _ (hZrange u hu s hs)) (V (u, s) v)
      have hfst' : HasDerivAt (fun a ↦ (V (a, s) v).1)
          ((fderiv ℝ H.vectorField (Z (u, s)) (V (u, s) v)).1) u := by
        simpa [V, Z, ι, sectionFlowState, Function.comp_def] using hfst
      rw [he] at hfst'
      exact hfst'
    initial_position := by
      intro s hs
      exact congrArg Prod.fst (hstart s hs)
    initial_energy := by
      intro s hs
      change H.h (Z (0, s)) = _
      rw [hstart s hs]
      exact henergy s hs
    initial_momentum := by
      intro s hs v
      rw [hstart s hs]
      exact sectionRootMomentum_pairing j ν horth g s v }
  have hc := (sectionFlowState_properties H j ν hΨ hg hinit).1.mono
    (Set.prod_mono htime Subset.rfl)
  exact ⟨Φ, rfl, rfl, rfl, rfl, rfl, hc.fst, hc.snd⟩

section RootedComparison

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- Insert the symbol’s energy root into the initial state and retain time, for
`app:lem:common-hamilton-phase`. -/
def sectionFlowInput (j : U →ₗᵢ[ℝ] E) (ν : E) (g : InitialData U → ℝ)
    (q : ℝ × InitialData U) : (E × E) × ℝ :=
  (transverseSectionState j ν (q.2, g q.2), q.1)

omit [CompleteSpace E] in
private theorem hasFDerivAt_sectionFlowInput
    (j : U →ₗᵢ[ℝ] E) (ν : E) {g : InitialData U → ℝ} {q : ℝ × InitialData U}
    (hg : DifferentiableAt ℝ g q.2) :
    HasFDerivAt (sectionFlowInput j ν g)
      (((j.toContinuousLinearMap.comp ((ContinuousLinearMap.fst ℝ U (ℝ × U)).comp
        (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))).prod
        (((fderiv ℝ g q.2).comp (ContinuousLinearMap.snd ℝ ℝ (InitialData U))).smulRight ν +
          j.toContinuousLinearMap.comp ((ContinuousLinearMap.snd ℝ ℝ U).comp
            ((ContinuousLinearMap.snd ℝ U (ℝ × U)).comp
              (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))))).prod
                (ContinuousLinearMap.fst ℝ ℝ (InitialData U))) q := by
  exact ((j.toContinuousLinearMap.hasFDerivAt.comp q
    ((hasFDerivAt_snd (p := q)).fst)).prodMk
    (((hg.hasFDerivAt.comp q (hasFDerivAt_snd (p := q))).smul_const ν).add
      (j.toContinuousLinearMap.hasFDerivAt.comp q (hasFDerivAt_snd (p := q)).snd.snd))).prodMk
        (hasFDerivAt_fst (p := q))

omit [CompleteSpace E] in
/-- The root derivative controls the derivative of initial-state insertion
(`app:lem:common-hamilton-phase`). -/
theorem norm_fderiv_sectionFlowInput_sub_le
    (j : U →ₗᵢ[ℝ] E) (ν : E) {g g₀ : InitialData U → ℝ} {q : ℝ × InitialData U}
    (hg : DifferentiableAt ℝ g q.2) (hg₀ : DifferentiableAt ℝ g₀ q.2) :
    ‖fderiv ℝ (sectionFlowInput j ν g) q - fderiv ℝ (sectionFlowInput j ν g₀) q‖ ≤
      ‖fderiv ℝ g q.2 - fderiv ℝ g₀ q.2‖ * ‖ν‖ := by
  refine (fderiv ℝ (sectionFlowInput j ν g) q -
    fderiv ℝ (sectionFlowInput j ν g₀) q).opNorm_le_bound (by positivity) ?_
  intro v
  rw [(hasFDerivAt_sectionFlowInput j ν hg).fderiv,
    (hasFDerivAt_sectionFlowInput j ν hg₀).fderiv]
  have he : ((j (v.2.1), (fderiv ℝ g q.2 v.2) • ν + j v.2.2.2), v.1) -
      ((j (v.2.1), (fderiv ℝ g₀ q.2 v.2) • ν + j v.2.2.2), v.1) =
      ((0, ((fderiv ℝ g q.2 - fderiv ℝ g₀ q.2) v.2) • ν), 0) := by
    ext <;> simp [sub_smul]
  change ‖((j (v.2.1), (fderiv ℝ g q.2 v.2) • ν + j v.2.2.2), v.1) -
      ((j (v.2.1), (fderiv ℝ g₀ q.2 v.2) • ν + j v.2.2.2), v.1)‖ ≤ _
  rw [he]
  have hn : 0 ≤ ‖(fderiv ℝ g q.2 - fderiv ℝ g₀ q.2) v.2‖ * ‖ν‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  conv_lhs => simp only [Prod.norm_def, norm_zero, norm_smul]
  rw [max_eq_right hn, max_eq_left hn]
  calc
    _ ≤ (‖fderiv ℝ g q.2 - fderiv ℝ g₀ q.2‖ * ‖v.2‖) * ‖ν‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg ν)
    _ ≤ (‖fderiv ℝ g q.2 - fderiv ℝ g₀ q.2‖ * ‖ν‖) * ‖v‖ := by
      calc
        _ = (‖fderiv ℝ g q.2 - fderiv ℝ g₀ q.2‖ * ‖ν‖) * ‖v.2‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_snd_le v)
          (mul_nonneg (norm_nonneg (fderiv ℝ g q.2 - fderiv ℝ g₀ q.2)) (norm_nonneg ν))

omit [CompleteSpace E] in
private theorem norm_comp_sub_comp_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A A₀ : Y →L[ℝ] Z) (B B₀ : X →L[ℝ] Y) :
    ‖A.comp B - A₀.comp B₀‖ ≤ ‖A - A₀‖ * ‖B‖ + ‖A₀‖ * ‖B - B₀‖ := by
  have he : A.comp B - A₀.comp B₀ = (A - A₀).comp B + A₀.comp (B - B₀) := by
    ext v
    simp
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

omit [CompleteSpace E] in
private theorem norm_fderiv_sectionAugmentedProjection_sub_le
    (j : U →ₗᵢ[ℝ] E) (ν : E) {g g₀ : InitialData U → ℝ}
    {Ψ Ψ₀ : (E × E) × ℝ → E × E} {q : ℝ × InitialData U}
    (h : DifferentiableAt ℝ (sectionFlowState j ν g Ψ) q)
    (h₀ : DifferentiableAt ℝ (sectionFlowState j ν g₀ Ψ₀) q) :
    ‖fderiv ℝ (sectionAugmentedProjection j ν g Ψ) q -
      fderiv ℝ (sectionAugmentedProjection j ν g₀ Ψ₀) q‖ ≤
    ‖fderiv ℝ (sectionFlowState j ν g Ψ) q -
      fderiv ℝ (sectionFlowState j ν g₀ Ψ₀) q‖ := by
  refine (fderiv ℝ (sectionAugmentedProjection j ν g Ψ) q -
    fderiv ℝ (sectionAugmentedProjection j ν g₀ Ψ₀) q).opNorm_le_bound
      (norm_nonneg (fderiv ℝ (sectionFlowState j ν g Ψ) q -
        fderiv ℝ (sectionFlowState j ν g₀ Ψ₀) q)) ?_
  intro v
  unfold sectionAugmentedProjection
  rw [(h.hasFDerivAt.fst.prodMk (hasFDerivAt_snd (p := q)).snd).fderiv,
    (h₀.hasFDerivAt.fst.prodMk (hasFDerivAt_snd (p := q)).snd).fderiv]
  change max ‖(fderiv ℝ (sectionFlowState j ν g Ψ) q v).1 -
      (fderiv ℝ (sectionFlowState j ν g₀ Ψ₀) q v).1‖ ‖v.2.2 - v.2.2‖ ≤ _
  rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
  exact (norm_fst_le ((fderiv ℝ (sectionFlowState j ν g Ψ) q -
      fderiv ℝ (sectionFlowState j ν g₀ Ψ₀) q) v)).trans
    (ContinuousLinearMap.le_opNorm _ _)

omit [CompleteSpace E] in
/-- The derivative comparison after inserting the perturbed energy root:
the reference flow's second derivative controls the shifted evaluation point.
Used by the common symbol projection construction in `app:lem:common-hamilton-phase`. -/
theorem exists_sectionAugmentedProjection_C1_bound
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (j : U →ₗᵢ[ℝ] E) (ν : E)
    {s₀ : InitialData U} {z₀ : E × E} {r ρ T C : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hT : 0 < T) (hC : 0 < C)
    {g₀ : InitialData U → ℝ} {Ψ₀ : (E × E) × ℝ → E × E}
    (hg₀ : ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)))
    (hΨ₀ : ContDiffOn ℝ ∞ Ψ₀ (ball z₀ ρ ×ˢ Ioo (-T) T))
    (hinit₀ : ∀ s ∈ ball s₀ (2 * r),
      transverseSectionState j ν (s, g₀ s) ∈ ball z₀ (ρ / 2)) :
    ∃ B > (0 : ℝ), ∀ (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E)
      (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      ContDiffOn ℝ ∞ Ψ (ball z₀ ρ ×ˢ Ioo (-T) T) →
      (∀ s ∈ ball s₀ (2 * r), transverseSectionState j ν (s, g s) ∈ ball z₀ (ρ / 2)) →
      (∀ s ∈ closedBall s₀ r, |g s - g₀ s| ≤ C * ε ∧
        ‖fderiv ℝ g s - fderiv ℝ g₀ s‖ ≤ C * ε) →
      (∀ q ∈ closedBall z₀ (ρ / 2) ×ˢ Icc (-T / 2) (T / 2),
        ‖fderiv ℝ Ψ q - fderiv ℝ Ψ₀ q‖ ≤ C * ε) →
      ∀ q ∈ Icc (-T / 2) (T / 2) ×ˢ closedBall s₀ r,
        ‖fderiv ℝ (sectionAugmentedProjection j ν g Ψ) q -
          fderiv ℝ (sectionAugmentedProjection j ν g₀ Ψ₀) q‖ ≤ B * ε := by
  let Q := closedBall z₀ (ρ / 2) ×ˢ Icc (-T / 2) (T / 2)
  let P := Icc (-T / 2) (T / 2) ×ˢ closedBall s₀ r
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hP : IsCompact P := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hQsub : Q ⊆ ball z₀ ρ ×ˢ Ioo (-T) T := by
    intro q hq
    exact ⟨closedBall_subset_ball (by linarith) hq.1,
      ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  have hPsub : P ⊆ Ioo (-T) T ×ˢ ball s₀ (2 * r) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      closedBall_subset_ball (by linarith) hq.2⟩
  have hDΨ := hΨ₀.fderiv_of_isOpen (isOpen_ball.prod isOpen_Ioo) (m := ∞) (by simp)
  obtain ⟨L, hL⟩ := (hDΨ.mono hQsub).exists_lipschitzOnWith (by simp)
    ((convex_closedBall _ _).prod (convex_Icc _ _)) hQ
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn (hDΨ.continuousOn.mono hQsub)
  have hI₀ : ContDiffOn ℝ ∞ (sectionFlowInput j ν g₀)
      (Ioo (-T) T ×ˢ ball s₀ (2 * r)) :=
    ((contDiff_transverseSectionState j ν).comp_contDiffOn
      (contDiffOn_snd.prodMk (hg₀.comp contDiffOn_snd (fun _ hq ↦ hq.2)))).prodMk
        contDiffOn_fst
  obtain ⟨N, hN⟩ := hP.exists_bound_of_continuousOn
    ((hI₀.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_ball) (m := ∞) (by simp)).continuousOn.mono hPsub)
  let B := (C + (L : ℝ) * C * ‖ν‖) * (|N| + C * ‖ν‖) + |M| * C * ‖ν‖ + 1
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro g Ψ ε hε hε1 hg hΨ hinit hroot hflow q hq
  have hs := (hPsub hq).2
  let x := sectionFlowInput j ν g q
  let y := sectionFlowInput j ν g₀ q
  have hx : x ∈ Q := ⟨ball_subset_closedBall (hinit q.2 hs), hq.1⟩
  have hy : y ∈ Q := ⟨ball_subset_closedBall (hinit₀ q.2 hs), hq.1⟩
  have hdg := (hg.contDiffAt (isOpen_ball.mem_nhds hs)).differentiableAt (by simp)
  have hdg₀ := (hg₀.contDiffAt (isOpen_ball.mem_nhds hs)).differentiableAt (by simp)
  have hIx := hasFDerivAt_sectionFlowInput j ν hdg
  have hIy := hasFDerivAt_sectionFlowInput j ν hdg₀
  have hdx := (hΨ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds (hQsub hx))).differentiableAt (by simp)
  have hdy := (hΨ₀.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds (hQsub hy))).differentiableAt (by simp)
  have hstate := hdx.hasFDerivAt.comp q hIx
  have hstate₀ := hdy.hasFDerivAt.comp q hIy
  have hxy : ‖x - y‖ ≤ C * ε * ‖ν‖ := by
    have he : ‖x - y‖ = |g q.2 - g₀ q.2| * ‖ν‖ := by
      change max ‖transverseSectionState j ν (q.2, g q.2) -
        transverseSectionState j ν (q.2, g₀ q.2)‖ ‖q.1 - q.1‖ = _
      rw [sub_self, norm_zero, max_eq_left (norm_nonneg _), norm_transverseSectionState_root_sub]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hroot q.2 hq.2).1 (norm_nonneg ν)
  have hDI : ‖fderiv ℝ (sectionFlowInput j ν g) q -
      fderiv ℝ (sectionFlowInput j ν g₀) q‖ ≤ C * ε * ‖ν‖ :=
    (norm_fderiv_sectionFlowInput_sub_le j ν hdg hdg₀).trans
      (mul_le_mul_of_nonneg_right (hroot q.2 hq.2).2 (norm_nonneg ν))
  have hDI₀ : ‖fderiv ℝ (sectionFlowInput j ν g₀) q‖ ≤ |N| :=
    (hN q hq).trans (le_abs_self N)
  have hDIb : ‖fderiv ℝ (sectionFlowInput j ν g) q‖ ≤ |N| + C * ‖ν‖ := by
    have hh := norm_add_le (fderiv ℝ (sectionFlowInput j ν g) q -
      fderiv ℝ (sectionFlowInput j ν g₀) q) (fderiv ℝ (sectionFlowInput j ν g₀) q)
    rw [sub_add_cancel] at hh
    nlinarith [mul_nonneg hC.le (norm_nonneg ν)]
  have hDA : ‖fderiv ℝ Ψ x - fderiv ℝ Ψ₀ y‖ ≤ (C + (L : ℝ) * C * ‖ν‖) * ε := by
    have hl₀ : ‖fderiv ℝ Ψ₀ x - fderiv ℝ Ψ₀ y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul x hx y hy
    have hl := hl₀.trans (mul_le_mul_of_nonneg_left hxy L.coe_nonneg)
    have ht := norm_add_le (fderiv ℝ Ψ x - fderiv ℝ Ψ₀ x)
      (fderiv ℝ Ψ₀ x - fderiv ℝ Ψ₀ y)
    rw [sub_add_sub_cancel] at ht
    nlinarith [hflow x hx]
  have hDA₀ : ‖fderiv ℝ Ψ₀ y‖ ≤ |M| := (hM y hy).trans (le_abs_self M)
  apply (norm_fderiv_sectionAugmentedProjection_sub_le j ν
    hstate.differentiableAt hstate₀.differentiableAt).trans
  change ‖fderiv ℝ (Ψ ∘ sectionFlowInput j ν g) q -
    fderiv ℝ (Ψ₀ ∘ sectionFlowInput j ν g₀) q‖ ≤ _
  rw [hstate.fderiv, hstate₀.fderiv, ← hIx.fderiv, ← hIy.fderiv]
  apply (norm_comp_sub_comp_le _ _ _ _).trans
  calc
    _ ≤ ((C + (L : ℝ) * C * ‖ν‖) * ε) * (|N| + C * ‖ν‖) +
        |M| * (C * ε * ‖ν‖) := add_le_add
      (mul_le_mul hDA hDIb (norm_nonneg (fderiv ℝ (sectionFlowInput j ν g) q)) (by positivity))
      (mul_le_mul hDA₀ hDI (norm_nonneg (fderiv ℝ (sectionFlowInput j ν g) q -
        fderiv ℝ (sectionFlowInput j ν g₀) q)) (abs_nonneg _))
    _ ≤ B * ε := by dsimp [B]; nlinarith

end RootedComparison

/-- Common Hamilton flows and full augmented-projection `C¹` stability from a
scalar `C³` neighborhood. The roots solve the unchanged canonical energy equation;
the flows and variational equations are constructed, not assumed. This supplies
both perturbation inputs of `HamiltonFlow.exists_bufferedProjection_domains`
(`app:lem:common-hamilton-phase`). -/
theorem exists_common_C1_hamiltonFlows [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ r > (0 : ℝ), ∃ T > (0 : ℝ), ∃ C > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∃ Φ₀ : HamiltonFlow H₀ U,
        Φ₀.time = Ioo (-T) T ∧ Φ₀.parameters = ball s₀ r ∧
        Φ₀.sectionMap = j.toContinuousLinearMap ∧
        Φ₀.momentum (0, s₀) = z₀.2 ∧
        ContDiffOn ℝ ∞ Φ₀.position (Φ₀.time ×ˢ Φ₀.parameters) ∧
        ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters) ∧
        (∀ q ∈ Φ₀.time ×ˢ Φ₀.parameters,
          (Φ₀.position q, Φ₀.momentum q) ∈ closedBall z₀ R) ∧
        ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
          cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
          ∃ Φ : HamiltonFlow H U,
            Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
            Φ.sectionMap = j.toContinuousLinearMap ∧
            ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
            ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
            (∀ q ∈ Φ.time ×ˢ Φ.parameters,
              (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
            ∀ q ∈ Φ₀.time ×ˢ Φ₀.parameters,
              ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
              ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤
                C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r, hr, ρ, hρ, T, hT, C, hC, δ, hδ, g₀, Ψ₀,
      hΨ₀, hg₀base, hg₀, hroot₀, hpert⟩ :=
    exists_common_rooted_symbol_flows H₀ hD hDH₀ hH₀ j ν hR hRD henergy htrans
  obtain ⟨B, hB, hbound⟩ := exists_sectionAugmentedProjection_C1_bound j ν hr hρ hT hC
    hg₀ hΨ₀.smooth (fun s hs ↦ (hroot₀ s hs).1)
  have hrr : ball s₀ r ⊆ ball s₀ (2 * r) := ball_subset_ball (by linarith)
  have hρρ : ball z₀ (ρ / 2) ⊆ ball z₀ ρ := ball_subset_ball (by linarith)
  have hfield₀ : ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H₀.vectorField z :=
    fun z hz ↦ ((H₀.contDiffOn_vectorField_of_subset hD hDH₀
      (n := ∞) (by simpa using hH₀)).contDiffAt
        (hD.mem_nhds (hRD hz))).differentiableAt (by simp)
  obtain ⟨Φ₀, ht₀, hp₀, hj₀, hx₀, hm₀, hc₀, hmc₀⟩ :=
    exists_hamiltonFlow_of_sectionFlow H₀ j ν horth isOpen_ball (half_pos hT)
      (by linarith : T / 2 ≤ T) hΨ₀ hfield₀ (hRD.trans hDH₀) (hg₀.mono hrr)
      (fun s hs ↦ hρρ (hroot₀ s (hrr hs)).1) (fun s hs ↦ (hroot₀ s (hrr hs)).2)
  have hdom : Φ₀.time ×ˢ Φ₀.parameters ⊆ Icc (-T / 2) (T / 2) ×ˢ closedBall s₀ r := by
    rw [ht₀, hp₀]
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], hq.1.2.le⟩, ball_subset_closedBall hq.2⟩
  have he₀ : Φ₀.augmentedProjection = sectionAugmentedProjection j ν g₀ Ψ₀ := by
    funext q
    simp only [HamiltonFlow.augmentedProjection, hx₀, sectionAugmentedProjection]
  have hrange₀ : ∀ q ∈ Φ₀.time ×ˢ Φ₀.parameters,
      (Φ₀.position q, Φ₀.momentum q) ∈ closedBall z₀ R := by
    intro q hq
    rw [hx₀, hm₀]
    apply hΨ₀.range _ (ball_subset_closedBall (hρρ (hroot₀ q.2 (hrr (hp₀ ▸ hq.2))).1))
    have htq := (hdom hq).1
    exact ⟨by linarith [htq.1], by linarith [htq.2]⟩
  refine ⟨r, hr, T / 2, half_pos hT, C + B, add_pos hC hB,
    min δ 1, lt_min hδ zero_lt_one, Φ₀, ht₀, hp₀, hj₀, ?_, hc₀, hmc₀, hrange₀, ?_⟩
  · rw [hm₀]
    change (Ψ₀ (transverseSectionState j ν (s₀, g₀ s₀), 0)).2 = _
    rw [hΨ₀.initial _ (ball_subset_closedBall (hρρ (hroot₀ s₀ (mem_ball_self (by positivity))).1)),
      hg₀base]
  intro H hDH hH hsmall
  obtain ⟨g, Ψ, hΨ, hg, hroot, hcloseg, hcloseΨ, hcloseproj, _⟩ :=
    hpert H hDH hH (hsmall.trans (min_le_left _ _))
  have hfield : ∀ z ∈ closedBall z₀ R, DifferentiableAt ℝ H.vectorField z :=
    fun z hz ↦ ((H.contDiffOn_vectorField_of_subset hD hDH
      (n := ∞) (by simpa using hH)).contDiffAt
        (hD.mem_nhds (hRD hz))).differentiableAt (by simp)
  obtain ⟨Φ, ht, hp, hj, hx, hm, hc, hmc⟩ :=
    exists_hamiltonFlow_of_sectionFlow H j ν horth isOpen_ball (half_pos hT)
      (by linarith : T / 2 ≤ T) hΨ hfield (hRD.trans hDH) (hg.mono hrr)
      (fun s hs ↦ hρρ (hroot s (hrr hs)).1) (fun s hs ↦ (hroot s (hrr hs)).2)
  have hte := ht.trans ht₀.symm
  have hpe := hp.trans hp₀.symm
  have he : Φ.augmentedProjection = sectionAugmentedProjection j ν g Ψ := by
    funext q
    simp only [HamiltonFlow.augmentedProjection, hx, sectionAugmentedProjection]
  refine ⟨Φ, hte, hpe, hj, hc, hmc, ?_, ?_⟩
  · intro q hq
    rw [hx, hm]
    apply hΨ.range _ (ball_subset_closedBall (hρρ (hroot q.2 (hrr (hp ▸ hq.2))).1))
    have htq := (hdom (by simpa only [← hte, ← hpe] using hq)).1
    exact ⟨by linarith [htq.1], by linarith [htq.2]⟩
  · intro q hq
    rw [he, he₀]
    have hn := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z)
    have hb := hbound g Ψ _ hn (hsmall.trans (min_le_right _ _)) hg hΨ.smooth
      (fun s hs ↦ (hroot s hs).1) hcloseg (fun q hq ↦ (hcloseΨ q hq).2) q (hdom hq)
    exact ⟨(hcloseproj q (hdom hq)).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + B) hn),
      hb.trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ C + B) hn)⟩

/-- Common buffered inverse projection charts for a scalar `C³` neighborhood
of a transverse Hamilton symbol (`app:lem:common-hamilton-phase`). The initial
energy root, Hamilton flow, projection closeness and normalized half gap are
all derived. The target, source radii and buffer are fixed before the perturbed
symbol; the entire preimage in the outer source lies in the middle source. -/
theorem exists_common_buffered_symbol_charts
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] [CompleteSpace U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
      (r b δ C : ℝ) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < δ ∧ 0 < C ∧
      IsOpen V ∧ IsCompact (closure V) ∧ (j s₀.1, s₀.2) ∈ V ∧
      closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ₀.time ×ˢ Φ₀.parameters ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (χ : ProjectionChart Φ),
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          χ.target = V ∧
          χ.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          χ.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ContDiffOn ℝ ∞ χ.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
                ≤ 1 / 2) ∧
          ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤
              C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ∧
            ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤
              C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r₀, hr₀, T, hT, C, hC, δ₀, hδ₀, Φ₀, ht₀, hp₀, hj₀,
      hm₀, hc₀, _, _, hpert⟩ :=
    exists_common_C1_hamiltonFlows H₀ hD hDH₀ hH₀ j ν horth hR hRD henergy htrans
  have hs₀ : s₀ ∈ Φ₀.parameters := hp₀.symm ▸ mem_ball_self hr₀
  have hv : ⟪ν, H₀.hp (j s₀.1, Φ₀.momentum (0, s₀))⟫_ℝ ≠ 0 := by
    rw [hm₀, real_inner_comm]
    exact htrans
  have hcbase : ContDiffAt ℝ 1 Φ₀.position ((0 : ℝ), s₀) :=
    (hc₀.contDiffAt ((Φ₀.isOpen_time.prod Φ₀.isOpen_parameters).mem_nhds
      ⟨Φ₀.zero_mem_time, hs₀⟩)).of_le (by simp)
  obtain ⟨A, _, r, hr, _, _, _, hinnerouter, _, hadm, hconv, hgap,
      ε, hε, b, hb, V, hV, hVc, hzV, hstable⟩ :=
    Φ₀.exists_bufferedProjection_domains j hj₀ ν horth hspan hs₀ hv hcbase
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hN : 0 ≤ N := norm_nonneg _
  let η := min ε (1 / (4 * (N + 1)))
  have hη : 0 < η := lt_min hε (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have hNη : N * η ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (N + 1) by positivity)).mp
      (show η ≤ 1 / (4 * (N + 1)) from min_le_right _ _)
    nlinarith [hη.le]
  have hDadm : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ₀.time ×ˢ Φ₀.parameters :=
    subset_closure.trans hadm
  refine ⟨Φ₀, A, r, b, min δ₀ (η / C), C, V, hr, hb,
    lt_min hδ₀ (div_pos hη hC), hC, hV, hVc, hzV, hadm, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨Φ, ht, hp, hj, hc, hmc, hrange, hclose⟩ :=
    hpert H hDH hH (hsmall.trans (min_le_left _ _))
  have hbound : C * cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ η := by
    have hh := (le_div_iff₀ hC).mp (hsmall.trans (min_le_right _ _))
    linarith
  have hadm' : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ.time ×ˢ Φ.parameters := by
    simpa only [ht, hp] using hDadm
  have hd : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r), DifferentiableAt ℝ Φ.augmentedProjection q :=
    fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hadm' hq)).differentiableAt
  have hderiv : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤ ε :=
    fun q hq ↦ ((hclose q (hDadm hq)).2.trans hbound).trans hηε
  have hvalue : ∀ q ∈ closure (ball ((0 : ℝ), s₀) r),
      ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤ ε := by
    intro q hq
    have hq' := hinnerouter hq
    exact ((hclose q (hDadm (ball_subset_ball (by linarith) hq'))).1.trans hbound).trans hηε
  obtain ⟨_, _, _, hinner, htarget, hpre, _⟩ := hstable Φ.augmentedProjection hd hderiv hvalue
  have hhalf : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
          ≤ 1 / 2 := by
    intro q hq
    apply normalized_derivative_gap_of_perturbation A (A := fderiv ℝ Φ₀.augmentedProjection q)
    · have he : (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ₀.augmentedProjection q - (A : _ →L[ℝ] _)) =
          (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ₀.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U) := by
        apply ContinuousLinearMap.ext
        intro v
        simp
      exact he ▸ hgap q hq
    · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      exact (mul_le_mul_of_nonneg_left ((hclose q (hDadm hq)).2.trans hbound) hN).trans hNη
  have himage : V ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (3 * r) := by
    intro z hz
    exact image_mono (ball_subset_ball (by linarith))
      (htarget (self_subset_cthickening _ (subset_closure hz)))
  obtain ⟨χ, hχt, hχs, hχ⟩ :=
    Φ.exists_smoothBufferedProjectionChart isOpen_ball hconv hV hadm' himage hc A hhalf
  refine ⟨Φ, χ, ht, hp, hj, hc, hmc, hrange, hχt, hχs, ?_, hχ,
    hinner, htarget, hpre, hhalf, fun q hq ↦ hclose q (hDadm hq)⟩
  intro q hq
  rw [hχs] at hq
  exact hpre ⟨self_subset_cthickening _ (subset_closure hq.2), hq.1⟩

end SectionEnergy

end JanetCartan.HamiltonPhase
