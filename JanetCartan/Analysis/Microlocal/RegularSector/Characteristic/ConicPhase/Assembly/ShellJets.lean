module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.CompactJets

/-!
# Actual normalized shell bounds on a spacetime cone

A fixed temporal aperture prevents a full normalized frequency from approaching
zero spatial frequency. Thus every normalized shell of the unbounded cone lies
in the explicit compact jet set. The original local phase jets supply the literal
whole-image reserve, with zero derivative loss. Consumer:
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral KernelIdentification WholeImageGeometry
variable {d : ℕ}

/-- The fixed convex spacetime cone with a temporal aperture. It lies in the
angular cone where the elapsed geometry was already proved
(`app:ch_regular_base:lem:retarded-kernel`). -/
def fullAngularCone (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε T : ℝ) :
    Set (Euclidean (d + 1)) :=
  {ξ | spatialPart ξ ∈ angularCone ℓ η₀ ε ∧ |ξ 0| < T * ℓ (spatialPart ξ)}

/-- The actual spacetime frequency cone is open
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isOpen_fullAngularCone (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε T : ℝ) : IsOpen (fullAngularCone ℓ η₀ ε T) :=
  ((isOpen_angularCone ℓ η₀ ε).preimage spatialPartCLM.continuous).inter
    (isOpen_lt ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.abs)
      (continuous_const.mul (ℓ.continuous.comp spatialPartCLM.continuous)))

/-- Convexity retains whole-cone averaged-gradient injectivity after the
fixed temporal restriction (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem convex_fullAngularCone (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε T : ℝ) : Convex ℝ (fullAngularCone ℓ η₀ ε T) := by
  let A : Euclidean (d + 1) →L[ℝ] ℝ := T • ℓ.comp spatialPartCLM
  let τ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))
  have he : fullAngularCone ℓ η₀ ε T =
      (spatialPart ⁻¹' angularCone ℓ η₀ ε) ∩
        ((A + τ) ⁻¹' Ioi 0 ∩ (A - τ) ⁻¹' Ioi 0) := by
    ext ξ
    change (spatialPart ξ ∈ angularCone ℓ η₀ ε ∧ |ξ 0| < T * ℓ (spatialPart ξ)) ↔
      (spatialPart ξ ∈ angularCone ℓ η₀ ε ∧
        (0 < T * ℓ (spatialPart ξ) + ξ 0 ∧ 0 < T * ℓ (spatialPart ξ) - ξ 0))
    rw [abs_lt]
    constructor <;> rintro ⟨hη, h₁, h₂⟩ <;> exact ⟨hη, by linarith, by linarith⟩
  rw [he]
  exact ((convex_angularCone ℓ η₀ ε).linear_preimage spatialPartCLM.toLinearMap).inter
    (((convex_Ioi (0 : ℝ)).linear_preimage (A + τ).toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (A - τ).toLinearMap))

/-- The outer spacetime cone excludes zero spatial frequency, hence zero
full frequency (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem ne_zero_of_mem_fullAngularCone {ℓ : Euclidean d →L[ℝ] ℝ}
    {η₀ : Euclidean d} {ε T : ℝ} {ξ : Euclidean (d + 1)}
    (hξ : ξ ∈ fullAngularCone ℓ η₀ ε T) : ξ ≠ 0 := by
  intro he
  have hz : spatialPart ξ = 0 := by rw [he]; rfl
  exact ne_zero_of_mem_angularCone hξ.1 hz

/-- Fixed inner angular and temporal margins, with a positive spatial collar,
have their full closure in the outer spacetime cone. This is the actual
frequency support margin used by the whole-image realization
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem closure_fullAngularCone_collar_subset (ℓ : Euclidean d →L[ℝ] ℝ)
    {η₀ : Euclidean d} {ε T c : ℝ} (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c) :
    closure (fullAngularCone ℓ η₀ (ε / 2) (T / 2) ∩
      {ξ | c < ‖spatialPart ξ‖}) ⊆ fullAngularCone ℓ η₀ ε T := by
  intro ξ hξ
  have hangular : spatialPart ξ ∈ angularCone ℓ η₀ ε := by
    have hsub : fullAngularCone ℓ η₀ (ε / 2) (T / 2) ∩
        {ξ | c < ‖spatialPart ξ‖} ⊆
        spatialPart ⁻¹' (angularCone ℓ η₀ (ε / 2) ∩ {η | c < ‖η‖}) :=
      fun _ hp ↦ ⟨hp.1.1, hp.2⟩
    exact closure_lifted_angularCone_collar_subset ℓ hε hc (closure_mono hsub hξ)
  have ht : |ξ 0| ≤ (T / 2) * ℓ (spatialPart ξ) := by
    apply closure_minimal (fun _ hp ↦ hp.1.2.le) _ hξ
    exact isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.abs)
      (continuous_const.mul (ℓ.continuous.comp spatialPartCLM.continuous))
  exact ⟨hangular, ht.trans_lt (mul_lt_mul_of_pos_right (by linarith) hangular.1)⟩

/-- Positive scaling preserves the same spacetime cone
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem smul_mem_fullAngularCone {ℓ : Euclidean d →L[ℝ] ℝ}
    {η₀ : Euclidean d} {ε T R : ℝ} (hR : 0 < R)
    {ξ : Euclidean (d + 1)} (hξ : ξ ∈ fullAngularCone ℓ η₀ ε T) :
    R • ξ ∈ fullAngularCone ℓ η₀ ε T := by
  refine ⟨by simpa using smul_mem_angularCone hξ.1 hR, ?_⟩
  simpa only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hR,
    SymbolBudgets.spatialPart_smul, map_smul, smul_eq_mul, mul_left_comm T R] using
      mul_lt_mul_of_pos_left hξ.2 hR

/-- Each normalized shell lies in the explicit compact spatial radial band.
The lower endpoint uses the temporal aperture and the upper endpoint uses
only the norm of the fixed section (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem normalizedSourceBand_mem_radialSectionBand (ℓ : Euclidean d →L[ℝ] ℝ)
    {η₀ : Euclidean d} {ε T a b R : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (ha : 0 < a) (hR : 0 < R) {ξ : Euclidean (d + 1)}
    (hξ : ξ ∈ normalizedSourceBand (fullAngularCone ℓ η₀ ε T) R a b) :
    spatialPart ξ ∈ radialSectionBand ℓ η₀ ε
      (a / (1 + T + ‖η₀‖ + ε)) ((1 + ‖ℓ‖) * b) := by
  have hc : ξ ∈ fullAngularCone ℓ η₀ ε T := by
    have hh := smul_mem_fullAngularCone (inv_pos.mpr hR) hξ.1
    simpa only [inv_smul_smul₀ hR.ne'] using hh
  let rad := ℓ (spatialPart ξ)
  have hrad : 0 < rad := hc.1.1
  have hden : 0 < 1 + T + ‖η₀‖ + ε := by positivity
  have hn : ‖rad⁻¹ • spatialPart ξ‖ ≤ ‖η₀‖ + ε := by
    have htri := dist_triangle (rad⁻¹ • spatialPart ξ) η₀ 0
    rw [dist_zero_right, dist_zero_right] at htri
    linarith [show dist (rad⁻¹ • spatialPart ξ) η₀ < ε from hc.1.2]
  have hnη : ‖spatialPart ξ‖ ≤ rad * (‖η₀‖ + ε) := by
    calc
      _ = rad * ‖rad⁻¹ • spatialPart ξ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrad,
          ← mul_assoc, mul_inv_cancel₀ hrad.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hn hrad.le
  have hlo : a / (1 + T + ‖η₀‖ + ε) ≤ rad := by
    apply (div_le_iff₀ hden).mpr
    have ht : |ξ 0| < T * rad := hc.2
    have := SymbolBudgets.norm_le_time_add_spatial ξ
    nlinarith [hξ.2.1]
  have hb : 0 < b := lt_trans ha (hξ.2.1.trans hξ.2.2)
  have hhi : rad ≤ (1 + ‖ℓ‖) * b := by
    have hl : rad ≤ ‖ℓ‖ * ‖spatialPart ξ‖ := (le_abs_self rad).trans (ℓ.le_opNorm _)
    have hs := (SymbolBudgets.norm_spatialPart_le ξ).trans hξ.2.2.le
    nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg ℓ)]
  refine ⟨(rad, rad⁻¹ • spatialPart ξ), ⟨⟨hlo, hhi⟩, ?_, ?_⟩,
    smul_inv_smul₀ hrad.ne' _⟩
  · exact ball_subset_closedBall hc.1.2
  · change ℓ (rad⁻¹ • spatialPart ξ) = 1
    simp only [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hrad.ne'

/-- The actual normalized shells, including their dummy source position,
lie in the constructed compact elapsed jet set. This closes the geometric
shell input of the whole-image reserve
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem normalizedSourceBand_mem_elapsedJetSet (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε T a b R : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (ha : 0 < a) (hR : 0 < R)
    {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ elapsedPhysicalBox z ε ×ˢ
      normalizedSourceBand (fullAngularCone ℓ z.2.2 ε T) R a b) :
    SymbolBudgets.phasePairInclusion p ∈ elapsedJetSet ℓ z ε
      (a / (1 + T + ‖z.2.2‖ + ε)) ((1 + ‖ℓ‖) * b) b := by
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · exact ⟨(p.1 0, spatialPart p.1),
      ⟨ball_subset_closedBall hp.1.1, ball_subset_closedBall hp.1.2⟩,
      timeSpaceMeasurableEquiv.symm_apply_apply p.1⟩
  · refine ⟨(p.2 0, spatialPart p.2), ⟨?_,
      normalizedSourceBand_mem_radialSectionBand ℓ hε hT ha hR hp.2⟩,
      timeSpaceMeasurableEquiv.symm_apply_apply p.2⟩
    have ht : |p.2 0| ≤ b := (PiLp.norm_apply_le p.2 0).trans hp.2.2.2.le
    exact abs_le.mp ht

/-- Every normalized shell of the actual unbounded cone has its literal
elapsed phase jets controlled by original buffered jets at the same order.
All constants depend only on the fixed geometry and derivative order, and
precede `F`, the positive radial scale and elapsed time. In particular set
`n = wholeImagePhaseReserve (d+1)` for the existing whole-image constructor.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_normalizedShell_jet_bound (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε T a b : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (ha : 0 < a) {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ U) (n : ℕ) :
    ∃ A > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∀ F : TwoTimePoint (Euclidean d) → ℝ, ContDiffOn ℝ ∞ F U →
      ∀ R > (0 : ℝ), ∀ r ∈ Icc 0 ε,
      ∀ p ∈ elapsedPhysicalBox z ε ×ˢ
          normalizedSourceBand (fullAngularCone ℓ z.2.2 ε T) R a b,
      ∀ k ≤ n,
        ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedPhase R
          (elapsedPhase (curriedExtend ℓ F) r))) p‖ ≤
            B + A * cNorm (closedBall (z.1, z) (2 * ε)) n F := by
  let a' := a / (1 + T + ‖z.2.2‖ + ε)
  let b' := (1 + ‖ℓ‖) * b
  have ha' : 0 < a' := div_pos ha (by positivity)
  refine ⟨jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε a' b') n,
    jetBoundConstant_pos _ _ _, SymbolBudgets.phaseTimeConstant (elapsedJetSet ℓ z ε a' b' b) n ε,
    SymbolBudgets.phaseTimeConstant_nonneg _ _ hε, ?_⟩
  intro F hF R hR r hr p hp k hk
  exact norm_iteratedFDeriv_buffered_elapsed_le ℓ hε ha' hU hbuffer hF hR hr hk
    (normalizedSourceBand_mem_elapsedJetSet ℓ hε hT ha hR hp)

end JanetCartan.RegularSector.Characteristic.ConicPhase
