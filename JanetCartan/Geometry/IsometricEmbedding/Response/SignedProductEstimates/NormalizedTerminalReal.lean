module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalCutSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedQuadratures

/-!
# The actual real normalized source on the terminal localizer

The complete normalized source and its literal adjoint commute with real
quadratures. This identifies their composition with the real compression of
the original right localizer, before output restriction. The existing complex
terminal estimate then applies to the literal zero extension of the original
nested-cutoff datum, with the original local real L² norm.

Consumers: the real terminal observation in `finiteChain_observation_rapidDecayAt`
and the angular contribution to `app:ch_pairs:prop:pairs-lag-sum`. The same
physical masks, one identity subtraction and low collar remain. No equality
between independently chosen masks, intermediate restriction removal or
complete residual-chain estimate is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 100000
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver RegularSector.Realization
open ArbitraryAccuracy.ResidualLocalization LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
open FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x₀ : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)
local notation "RH" => Lp RV 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩


/-- Real compression retains the literal Hilbert adjoint of the same operator
(`measured-adjoint`, terminal observation). -/
private theorem terminal_realCompression_adjoint (T : H →L[ℂ] H) :
    (realCompression T).adjoint = realCompression T.adjoint := by
  have hi : (l2ComplexInclusion (ι := Fin (d+1)) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (congrArg (fun A : RH →L[ℝ] H ↦ A.adjoint)
        (l2RealPart_adjoint (ι := Fin (d+1)) (volume : Measure E))).symm
  simp only [realCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictScalars_complex,
    l2RealPart_adjoint (ι := Fin (d+1)) (volume : Measure E), hi,
    ContinuousLinearMap.comp_assoc]


/-- The actual normalized pair preserves real part by its proved inclusion
identity and literal adjoint (`real-sector-normalization`). -/
private theorem normalizedPair_realPart (T : H →L[ℂ] H) (u : H) :
    realCompression (normalizedPair T) (l2RealPart volume u) =
      l2RealPart volume (normalizedPair T u) := by
  have he : (l2ComplexInclusion volume).comp (realCompression (normalizedPair T.adjoint)) =
      ((normalizedPair T.adjoint).restrictScalars ℝ).comp (l2ComplexInclusion volume) := by
    ext1 v
    exact inclusion_realCompression_normalizedPair T.adjoint v
  have ha := congrArg ContinuousLinearMap.adjoint he
  simp only [ContinuousLinearMap.adjoint_comp, terminal_realCompression_adjoint,
    adjoint_restrictScalars_complex, normalizedPair_adjoint,
    ContinuousLinearMap.adjoint_adjoint] at ha
  have hi : (l2ComplexInclusion (ι := Fin (d+1)) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (congrArg (fun A : RH →L[ℝ] H ↦ A.adjoint)
        (l2RealPart_adjoint (ι := Fin (d+1)) (volume : Measure E))).symm
  rw [hi] at ha
  exact DFunLike.congr_fun ha u


set_option backward.isDefEq.respectTransparency false

/-- Both literal orientations of the corrected real source commute with each
real quadrature, retaining the single identity subtraction
(`app:ch_regular:eq:resolved-angular-tail`, `measured-adjoint`). -/
theorem normalizedSource_real_direction_quadrature_defect
    (f : ActualMaskFamily Ω x₀ RQ A₀ K C₀) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (backward : Bool) (u : H) (c : ℂ) :
    let S := pairedSource f hK L₀ output ho hob
    let P := if backward then S.adjoint else S
    let R := realSource f hK L₀ output ho hob
    let Pr := if backward then R.adjoint else R
    (Pr - 1) (l2RealPart volume (c • u)) =
      l2RealPart volume (c • ((P - 1) u)) := by
  intro S P R Pr
  let T := (sourceCutMultiplier output ho hob).comp
    (RegularSector.FiniteAssembly.selectedFiniteSourcePDO f L₀ +
      RegularSector.EllipticComplement.ellipticSourcePDO f hK L₀)
  have hP : P = normalizedPair (if backward then T.adjoint else T) := by
    cases backward
    · rfl
    · exact normalizedPair_adjoint T
  have hPr : Pr = realCompression (normalizedPair (if backward then T.adjoint else T)) := by
    cases backward
    · rfl
    · exact (terminal_realCompression_adjoint (normalizedPair T)).trans
        (congrArg realCompression (normalizedPair_adjoint T))
  have he (v : H) : Pr (l2RealPart volume v) = l2RealPart volume (P v) := by
    rw [hPr, hP]
    exact normalizedPair_realPart _ v
  rw [← (P - 1).map_smul c u]
  simp only [sub_apply, one_apply_eq_self, map_sub]
  exact congrArg (fun z ↦ z - l2RealPart volume (c • u)) (he (c • u))

/-- The actual real source after the compressed right localizer is exactly
the local compression of the complex composition. Original restriction and
zero extension retain their positions; no parity or extra plateau is assumed
(`app:ch_regular:lem:finite-chain`, terminal observation). -/
theorem normalizedSource_real_terminal_composition
    (f : ActualMaskFamily Ω x₀ RQ A₀ K C₀) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (backward : Bool) (M : H →L[ℂ] H) {D : Set E} (hD : MeasurableSet D)
    (W : Set E) (u : LocalL2 D RV) :
    let S := pairedSource f hK L₀ output ho hob
    let P := if backward then S.adjoint else S
    let R := realSource f hK L₀ output ho hob
    let Pr := if backward then R.adjoint else R
    localRealCompression hD W ((P - 1).comp M) u =ᵐ[volume.restrict W]
      (Pr - 1) (realCompression M (SmallSupport.zeroExtend hD u)) := by
  intro S P R Pr
  have he := normalizedSource_real_direction_quadrature_defect f hK L₀ output ho hob
    backward (M (l2ComplexInclusion volume (SmallSupport.zeroExtend hD u))) 1
  simp only [one_smul] at he
  have he' : (Pr - 1) (realCompression M (SmallSupport.zeroExtend hD u)) =
      realCompression ((P - 1).comp M) (SmallSupport.zeroExtend hD u) := he
  rw [he']
  exact localRealCompression_coeFn hD W ((P - 1).comp M) u

/-- Real inclusion commutes with the original local source cutoff, with the
same restricted measure (`app:ch_regular:thm:exact-correction`). -/
private theorem terminal_inclusion_bump {D : Set E} (χ : ContDiffBump x₀)
    (u : LocalL2 D RV) :
    l2ComplexInclusion (volume.restrict D) (SmallSupport.bumpL2 (p := 2) le_rfl χ u) =
      SmallSupport.bumpL2 (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict D) u) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL
    (SmallSupport.bumpL2 (p := 2) le_rfl χ u),
    SmallSupport.bumpL2_coeFn (p := 2) le_rfl χ u,
    SmallSupport.bumpL2_coeFn (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict D) u),
    euclideanComplexInclusion.coeFn_compLpL u] with y hi hr hc hu
  change (l2ComplexInclusion (volume.restrict D) (SmallSupport.bumpL2 (p := 2) le_rfl χ u)) y = _ at hi
  change (l2ComplexInclusion (volume.restrict D) u) y = _ at hu
  rw [hi, hr, hc, hu]
  exact euclideanComplexInclusion.map_smul (χ y) (u y)

set_option maxHeartbeats 800000

/-- Apply the proved corrected terminal estimate to the actual real source
and its literal adjoint, after the compressed right localizer. The local
compression is identified with this same composition on the original zero
extension of `χ₂u`. All constants precede domains, inner cutoffs and data;
the source masks, low collar and fixed exponent are retained
(`app:ch_regular:eq:resolved-angular-tail`, terminal `hBnear`). -/
theorem exists_normalizedRealSource_recut_terminal_bounds
    (f : ActualMaskFamily Ω x₀ RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (χ₃ : ContDiffBump x₀) (U : Set E) (hU : IsOpen U)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (hcore : U ⊆ ball x₀ f.physicalRadius) (houtput : ∀ y ∈ U, output y = 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
        (∀ u : H, M u =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ χ₂ : ContDiffBump x₀, (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) →
      ∀ q (D : Set E) (hD : MeasurableSet D) (W : Set E) (hW : MeasurableSet W)
        (u : LocalL2 D RV) (backward : Bool),
        let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
        let S := pairedSource f hK L₀ output ho.continuous hob
        let P := if backward then S.adjoint else S
        let R := realSource f hK L₀ output ho.continuous hob
        let Pr := if backward then R.adjoint else R
        let w := SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u
        let v := localRealCompression hD W ((P - 1).comp M) w
        (v =ᵐ[volume.restrict W]
          (Pr - 1) (realCompression M (SmallSupport.zeroExtend hD w))) ∧
        v ∈ (restrictionSobolevScale W RV hW).level s ∧
          (restrictionSobolevScale W RV hW).gradeNorm s v ≤
            C q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖ := by
  let data := exists_normalizedSource_recut_terminal_bounds
    f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput
    mi hi hic hlo hann hterminal s
  let Cr := data.choose_spec.choose
  have hCr := data.choose_spec.choose_spec.2.1
  have hbound := data.choose_spec.choose_spec.2.2
  refine ⟨Cr, hCr, ?_⟩
  intro ρ L hL hLρ M hM χ₂ hnest q D hD W hW u backward hob S P R Pr w v
  refine ⟨(normalizedSource_real_terminal_composition f hK L₀ output ho.continuous hob
    backward M hD W w), ?_⟩
  have hb := (hbound ρ L hL hLρ M hM χ₂ hnest q D hD W hW
    (l2ComplexInclusion (volume.restrict D) u) backward).2 1 (by simp)
  simp only [one_smul] at hb
  have he : v = l2RealPart (volume.restrict W)
      (restrictL2 W ((P - 1) (M (SmallSupport.zeroExtend hD
        (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ (l2ComplexInclusion (volume.restrict D) u)))))) := by
    change l2RealPart (volume.restrict W) (restrictL2 W
      ((P - 1) (M (SmallSupport.zeroExtend hD (l2ComplexInclusion (volume.restrict D) w))))) = _
    rw [terminal_inclusion_bump]
  rw [he]
  have hn : ‖l2ComplexInclusion (volume.restrict D) u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (l2ComplexInclusion (volume.restrict D)).le_of_opNorm_le
      (l2ComplexInclusion_norm_le _) u
  refine ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hn ?_)⟩
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hCq := hCr q
  positivity

end JanetCartan.SignedProductEstimates
