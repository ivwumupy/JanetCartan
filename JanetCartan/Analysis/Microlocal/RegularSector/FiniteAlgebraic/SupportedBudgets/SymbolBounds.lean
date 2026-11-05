module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets.ProductBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SupportedBudgets

/-!
# Supported algebraic symbols on the selected family's retained interval

Apply source multiplication, the full physical action and both physical masks
to the exact inverse returned by `exists_finite_physical_evolution_and_algebraic_inverse`.
Consumers: `directPDOSymbols` indices zero and three, and the natural-order
forward and literal-adjoint estimates in `SupportedBudgets.IntegerBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- On the SAME selected family, both literal algebraic symbols are globally
smooth, have a common paired-position support box, and satisfy weighted
position budgets with reserve ONE. The original low order is
`2 * (d + 2) + 2`. Constants precede `L,Q,B`.

`hc`, `hsource`, complement containment and the local inverse estimates are
precisely retained outputs of `exists_finite_physical_evolution_and_algebraic_inverse`;
the parent instantiates them on its selected witnesses with `L ≥ f.radialThreshold`.
No new interval, compact-buffer witness or assembled-symbol budget is assumed.
Source: `app:ch_regular_base:eq:complement-symbol` and `energy-complete-residual`. -/
theorem exists_selected_algebraicSymbols_supported_budgets
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : RootBuffer (f.chart p).index (f.chart p).row (f.chart p).col A₀ p.val.val
      (f.chart p).root (f.chart p).coefficientRadius (f.chart p).rootRadius
      (f.chart p).minorGap (f.chart p).transportGap)
    (hsource : MapsTo (rootPhysicalPosition (coordinateSplit (f.chart p).index))
      (tsupport (f.chart p).sourceMask) (closedBall x RQ))
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : tsupport ρ ⊆ {η | 0 < (f.chart p).radialSection η})
    (hρrange : ∀ η, ρ η ∈ Icc (0 : ℝ) 1)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (hcarrier : tsupport χout ⊆ closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ)
    (Mlow : ℝ) (hMlow : 0 ≤ Mlow) (D : ℕ → ℝ) (hD : ∀ m, 0 < D m) :
    let c := f.chart p
    let x' := (physicalCoordinates c.index).symm x
    ∃ Rbox > 0, ∃ C : ℕ → ℝ, ∃ Mbound > 0, (∀ m, 0 < C m) ∧
      ∀ (L : ℝ) (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2 * (d + 2) + 2) Q ≤ Mlow →
        cNorm (closedBall x RQ) (2 * (d + 2) + 2) B ≤ Mlow →
        let h := fieldRoot (coordinateSplit c.index) Q c.root
        let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
        ((physicalCoordinates c.index ⁻¹' Ω) ×ˢ
          (normalizeCovector c.radialSection '' tsupport β) ⊆
          complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) →
        (∀ ζ ∈ tsupport β,
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) y) ∧
          ∀ m, (1 + ‖ζ‖) * cNorm (closedBall x' RQ) m
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
              D m * (1 + cNorm (closedBall x RQ) m Q)) →
        let b := directAlgebraicSymbol
          (conicBminus c.radialSection c.index Q h c.row c.col)
          (conicSourceSymbol c.radialSection ρ c.sourceMask) β
        let p := physicalSymbolApply
          (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b
        ∀ s ∈ ({b, p} : Set (E → E → CMat)),
          ContDiff ℝ ∞ (Function.uncurry s) ∧
          GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource s) Rbox Mbound ∧
          (∀ ξ is, is.length ≤ 2 * (d + 2) + 1 → ∀ z,
            (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
              (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤ Mbound) ∧
          ∀ m ξ is, is.length ≤ m → ∀ z,
            (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
              (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤
                C m * (1 + cNorm (closedBall x RQ) (m + 1) Q +
                  cNorm (closedBall x RQ) (m + 1) B) := by
  intro c x'
  let i := c.index
  let ℓ := c.radialSection
  let σ := c.sourceMask
  have hdist (y : E) : dist (physicalCoordinates i y) x = dist y x' := by
    calc
      dist (physicalCoordinates i y) x =
          dist (physicalCoordinates i y) (physicalCoordinates i x') := by
        congr 1
        exact ((physicalCoordinates i).apply_symm_apply x).symm
      _ = dist y x' := by
        rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  have hphysical : MapsTo (physicalCoordinates i) (closedBall x' RQ) (closedBall x RQ) := by
    intro y hy
    simpa only [mem_closedBall, hdist] using hy
  have hsσ : ∀ w ∈ tsupport σ,
      KernelIdentification.timeSpacePoint w.1 w.2.1 ∈ closedBall x' RQ := by
    intro w hw
    have hw' := hsource hw
    change dist ((coordinateSplit i).symm (w.1, w.2.1)) x ≤ RQ at hw'
    rw [← physicalCoordinates_timeSpacePoint, hdist] at hw'
    exact hw'
  obtain ⟨Db, hDb, hb⟩ := exists_selected_sourceInverse_weighted_cNorm_bounds
    f p hRQ hKΩ ρ hρrange D hD
  obtain ⟨Dp, hDp, hp⟩ := exists_physicalSymbolApply_weighted_cNorm_transfer
    i x' hRQ x RQ hphysical Mlow Db hDb
  choose T hT htransfer using fun m ↦
    exists_maskedPhysicalPDOCycleSymbol_derivative_constant (q := d + 1)
      x' RQ χout χsource ho hs hco hcs hcarrier m
  obtain ⟨Rbox, hRbox, hbox⟩ := exists_common_maskedPhysicalPDOCycleSymbol_support
    (q := d + 1) hco hcs
  let C : ℕ → ℝ := fun m ↦ T m * (Db m + Dp m)
  have hC m : 0 < C m := mul_pos (hT m) (add_pos (hDb m) (hDp m))
  let k := 2 * (d + 2) + 1
  let L := C k * (1 + 2 * Mlow)
  have hL : 0 < L := mul_pos (hC k) (by positivity)
  refine ⟨Rbox, hRbox, C, L, hL, hC, ?_⟩
  intro radial Q B hQ hB hQrange hQlow hBlow h β hdom hinverse b p'
  have hroot := fieldRoot_smooth_and_characteristic_on_normalizedRootDomain c hΩ hc Q hQ
    (f.mapsTo_local_coefficient_ball p hQrange)
  have hbSmooth : ContDiff ℝ ∞ (Function.uncurry b) :=
    contDiff_conicAlgebraicSymbol ℓ i hQ (isOpen_normalizedRootDomain c hΩ) hroot.1
      (fun _ hw ↦ hw.1) c.row c.col hdom ρ hρ hsρ σ c.sourceMask_smooth
      (fun w hw ↦ by
        change physicalCoordinates i (KernelIdentification.timeSpacePoint w.1 w.2.1) ∈ Ω
        rw [physicalCoordinates_timeSpacePoint]
        exact hKΩ (hsource hw))
      β (Complex.ofRealCLM.contDiff.comp
        ((contDiff_dilatedConicMask (f.angularMask_smooth p) radial).comp
          (physicalCoordinates i).contDiff))
      (fun ζ hζ ↦ mem_image_of_mem _ hζ)
  let U := physicalCoordinates i ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (physicalCoordinates i).continuous
  have hKU : closedBall x' RQ ⊆ U := fun y hy ↦ hKΩ (hphysical hy)
  have hA : ContDiffOn ℝ ∞
      (fun y a ↦ (coefficient i Q y a).map Complex.ofReal) U := by
    apply contDiffOn_pi.mpr
    intro a
    exact contDiff_matrix_map_ofReal.comp_contDiffOn
      (contDiff_pencil.comp_contDiffOn
        ((hQ.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hy ↦ hy)).prodMk
          contDiffOn_const))
  have hBc : ContDiffOn ℝ ∞ (fun y ↦ (zeroth i B y).map Complex.ofReal) U :=
    contDiff_matrix_map_ofReal.comp_contDiffOn
      (hB.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hy ↦ hy))
  have hbSupport : ∀ y, y ∉ closedBall x' RQ → ∀ η, b y η = 0 := by
    intro y hy η
    have hσzero : σ (rootState y ((ℓ (spatialPart η))⁻¹ • spatialPart η)) = 0 := by
      by_contra hn
      have hw := hsσ _ (subset_tsupport σ hn)
      have he : EvolutionIntegral.KernelIdentification.timeSpacePoint (y 0) (spatialPart y) = y :=
        EvolutionIntegral.KernelIdentification.timeSpaceMeasurableEquiv.symm_apply_apply y
      exact hy (by simpa only [rootState, he] using hw)
    dsimp only [σ, ℓ] at hσzero
    simp [b, directAlgebraicSymbol, conicSourceSymbol, ResidualCoordinates.sourceSymbol, hσzero]
  have hpSmooth : ContDiff ℝ ∞ (Function.uncurry p') :=
    contDiff_physicalSymbolApply_on_carrier isClosed_closedBall hU hKU hA hBc hbSmooth hbSupport
  have hbBound := (hb radial Q hdom hinverse).2
  have hpBound := hp Ω hΩ hKΩ Q B b hQ hB hbSmooth hpSmooth
    ((cNorm_mono_order (by omega : 1 ≤ 2 * (d + 2) + 2)).trans hQlow)
    ((cNorm_mono_order (by omega : 0 ≤ 2 * (d + 2) + 2)).trans hBlow) hbBound
  have hsmooth (s : E → E → CMat) (hs' : s ∈ ({b, p'} : Set (E → E → CMat))) :
      ContDiff ℝ ∞ (Function.uncurry s) := by
    simp only [mem_insert_iff, mem_singleton_iff] at hs'
    rcases hs' with rfl | rfl
    · exact hbSmooth
    · exact hpSmooth
  have hbudget (s : E → E → CMat) (hs' : s ∈ ({b, p'} : Set (E → E → CMat)))
      (m : ℕ) (η : E) :
      (1 + ‖η‖) * cNorm (closedBall x' RQ) m (fun y ↦ s y η) ≤
        (Db m + Dp m) * (1 + cNorm (closedBall x RQ) (m + 1) Q +
          cNorm (closedBall x RQ) (m + 1) B) := by
    have hhigh : 0 ≤ 1 + cNorm (closedBall x RQ) (m + 1) Q +
        cNorm (closedBall x RQ) (m + 1) B := by
      linarith [cNorm_nonneg (closedBall x RQ) (m + 1) Q,
        cNorm_nonneg (closedBall x RQ) (m + 1) B]
    simp only [mem_insert_iff, mem_singleton_iff] at hs'
    rcases hs' with rfl | rfl
    · apply (hbBound η m).trans
      apply mul_le_mul
      · exact le_add_of_nonneg_right (hDp m).le
      · have hq := cNorm_mono_order (s := closedBall x RQ) (f := Q) (Nat.le_succ m)
        linarith [cNorm_nonneg (closedBall x RQ) (m + 1) B]
      · linarith [cNorm_nonneg (closedBall x RQ) m Q]
      · exact (add_pos (hDb m) (hDp m)).le
    · exact (hpBound η m).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hDb m).le) hhigh)
  intro s hs'
  have hsSmooth := hsmooth s hs'
  have hderiv m ξ is (his : is.length ≤ m) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤
        C m * (1 + cNorm (closedBall x RQ) (m + 1) Q +
          cNorm (closedBall x RQ) (m + 1) B) := by
    have hnonneg : 0 ≤ (Db m + Dp m) *
        (1 + cNorm (closedBall x RQ) (m + 1) Q + cNorm (closedBall x RQ) (m + 1) B) :=
      mul_nonneg (add_pos (hDb m) (hDp m)).le (by
        linarith [cNorm_nonneg (closedBall x RQ) (m + 1) Q,
          cNorm_nonneg (closedBall x RQ) (m + 1) B])
    exact (htransfer m s hsSmooth _ hnonneg (hbudget s hs' m) ξ is his z).trans_eq (by
      dsimp [C]; ring)
  have hlow ξ is (his : is.length ≤ k) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤ L := by
    apply (hderiv k ξ is his z).trans
    apply mul_le_mul_of_nonneg_left _ (hC k).le
    have hq := (cNorm_mono_order (s := closedBall x RQ) (f := Q)
      (show k + 1 ≤ 2 * (d + 2) + 2 by dsimp [k]; omega)).trans hQlow
    have hbb := (cNorm_mono_order (s := closedBall x RQ) (f := B)
      (show k + 1 ≤ 2 * (d + 2) + 2 by dsimp [k]; omega)).trans hBlow
    linarith
  refine ⟨hsSmooth, ⟨contDiff_maskedPhysicalPDOCycleSymbol ho hs hsSmooth, hbox s, ?_⟩,
    hlow, hderiv⟩
  intro ξ is his z
  have hweighted := hlow ξ is (by dsimp [k]; omega) z
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ])).trans hweighted

end JanetCartan.RegularSector.FiniteAlgebraic
