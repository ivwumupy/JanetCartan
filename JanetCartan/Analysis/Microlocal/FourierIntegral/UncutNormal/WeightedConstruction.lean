module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.Construction
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds

/-!
# The actual weighted uncut cross-normal

The original mask and invertible matrix determine both amplitudes in
`app:ch_regular_base:eq:actual-matrix-inverse`. Their continuity, support,
growth and finite jets are derived before constructing both bounded graphs.
Their pure cross-normal is the existing matrix PDO, with supported diagonal
exactly the square of the complete mask times the identity. Gaps occur only
on the buffered chart; source multipliers and the diagonal reduction remainder
belong to the consuming coordinate-inverse construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison LowBounds LowBounds.FrequencyCutoff WholeImageGeometry
  Pseudodifferential AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The diagonal of the actual cycle PDO symbol, using only the original phase
and matrix gaps on the supported chart. All derivatives needed by the diagonal
cancellation are derived from local phase smoothness. Source:
`app:ch_regular_base:eq:actual-normal-amplitude` and
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeighted_cycleSymbol_diagonal_of_primitive_phase
    {X D : Set E} {S : E → E → ℝ} (c : E → E → ℝ) (U : E → E → Mat)
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hs : tsupport (Function.uncurry c) ⊆ X ×ˢ D)
    {δ δU : ℝ} (hδ : 0 < δ) (hδU : 0 < δU)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    (hdet : ∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) (x ξ : E) :
    cycleCrossNormalSymbol D S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
      (wholeImageInverse S D) (averagedJacobian S) ξ (pairedPosition x x) =
      {v : E | x ∈ X ∧ (2 * Real.pi) • v ∈ averagedGradient S x x '' D}.indicator
        (fun v ↦ (c x (wholeImageInverse S D x x ((2 * Real.pi) • v)) : ℂ)^2 •
          (1 : Mat)) ξ := by
  have hz (x u : E) (hx : x ∉ X) : c x u = 0 := by
    by_contra hne
    exact hx (hs (subset_tsupport (Function.uncurry c)
      (show (x, u) ∈ Function.support (Function.uncurry c) from hne))).1
  have hp := maskedAmplitudes_physical_support S c U X hz
  rw [cycleCrossNormalSymbol_eq_pairedBuffered X D S _ _ _ _ hp.1 hp.2,
    pairedNormalAmplitude_pairedPosition]
  apply maskedWeighted_extended_diagonal X D S c U hδ
  · intro z hz u hu _
    have hg := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
      (x := (z, z, u)) ((hX.prod (hX.prod hD)).mem_nhds ⟨hz, hz, hu⟩)
    have hd := (hg.comp u (contDiffAt_const.prodMk
      (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
    have he : averagedGradient S z z = fun v ↦ gradient (fun w ↦ S w v) z := by
      funext v
      simp [averagedGradient, averagedPhaseDifferential, gradient]
    change DifferentiableAt ℝ (averagedGradient S z z) u at hd
    rwa [he] at hd
  · intro z hz u hu _
    exact hgap z hz z hz u hu
  · intro z hz u hu _
    exact isUnit_iff_ne_zero.mpr (norm_pos_iff.mp (hδU.trans_le (hdet z hz u hu)))

/-- Construct the transport graph and the weighted forward graph, and identify
their uncut cross-normal with the literal matrix PDO. Only original local phase,
mask and matrix jets and their supported gaps are inputs. Inverse-matrix jets,
Jacobian-density jets, both graph operators and the normal identity are outputs.

For `c x u = χt x * χg u`, `maskedWeightedAmplitude_product_mask` gives exactly
`χt χg j_S U⁻*`; the diagonal below retains `(χt χg)^2`. The parent retains the
source multiplier and order-minus-one diagonal remainder. Source:
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_weighted_uncut_crossNormal_of_wholeImage_phase
    (hn : 0 < n) (R M₀ M B₀ Bφ : ℝ)
    {δ δU ε : ℝ} (hδ : 0 < δ) (hδU : 0 < δU) (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∃ C > 0, ∃ Mnormal > 0,
      ∀ (X D : Set E) (O : Set (E × E)) (S : E → E → ℝ)
        (c : E → E → ℝ) (U : E → E → Mat) (Kout : Set E),
      IsOpen X → IsOpen D → Convex ℝ X → IsOpen O → closure (X ×ˢ D) ⊆ O →
      IsCompact Kout → ContDiffOn ℝ ∞ (Function.uncurry S) O →
      (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
        S x (t • u) = t * S x u) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
      (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      (∀ u ∈ D, ε < ‖u‖) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ Bφ) →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D) →
      tsupport (Function.uncurry c) ⊆ X ×ˢ D →
      (∀ x u, x ∉ Kout → c x u = 0) →
      (∀ x ∈ X, ∀ u ∈ D, ‖c x u‖ ≤ M₀) →
      (∀ x ∈ X, ∀ u ∈ D, ‖U x u‖ ≤ M₀) →
      (∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (fun q : E × E ↦ c q.1 (((2 : ℝ)^j) • q.2)) z‖ ≤ M) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 U)) z‖ ≤ M) →
      ∃ T V : H →L[ℂ] H,
        ‖T‖ ≤ C ∧ ‖T.adjoint‖ ≤ C ∧ ‖V‖ ≤ C ∧ ‖V.adjoint‖ ≤ C ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2
            (graphOperator S (fun z _ v ↦ maskedTransportAmplitude c U z v) u x)) ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), V (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2
            (graphOperator S (fun z _ v ↦ maskedWeightedAmplitude S c U z v) u x)) ∧
        ∃ hb : GraphNormalAmplitudeBounds
          (cycleCrossNormalSymbol D S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
            (wholeImageInverse S D) (averagedJacobian S)) R Mnormal,
          T.comp V.adjoint = vectorTwoPositionL2Operator hn R
            (cycleCrossNormalSymbol D S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
              (wholeImageInverse S D) (averagedJacobian S))
            hb.smooth hb.support Mnormal hb.entry_bound ∧
          ∀ x ξ : E,
            cycleCrossNormalSymbol D S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
              (wholeImageInverse S D) (averagedJacobian S) ξ (pairedPosition x x) =
              {v : E | x ∈ X ∧ (2 * Real.pi) • v ∈ averagedGradient S x x '' D}.indicator
                (fun v ↦ (c x (wholeImageInverse S D x x ((2 * Real.pi) • v)) : ℂ)^2 •
                  (1 : Mat)) ξ := by
  obtain ⟨a, ha, b, hab, C, hC, Cnormal, hCnormal, hcross⟩ :=
    exists_uncut_crossNormal_of_wholeImage_phase (r := r) hn R B₀ Bφ hδ hε
  obtain ⟨β, hβ, PB, _, hweighted⟩ :=
    exists_maskedWeightedAmplitude_wholeImage_inputs (n := n) (r := r) M₀ M B₀ Bφ hδ hδU
  obtain ⟨PA, hPA, hglobal⟩ :=
    exists_maskedAmplitudes_global_bound (n := n) (r := r) M₀ B₀ hδ hδU
  let α := (2 : ℝ)^(primitiveNormalReserve n) * max 1 M ^ 2
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨a, ha, b, hab, C * max α β, mul_pos hC (hα.trans_le (le_max_left _ _)),
    Cnormal * α * β, mul_pos (mul_pos hCnormal hα) hβ, ?_⟩
  intro X D O S c U Kout hX hD hcX hO hbuffer hKout hS hhom hmix hinj hgap hcollar
    hφjet hR hc hU hsupp hphysical hc₀ hU₀ hdet hcjet hUjet
  have hSlocal := hS.mono (subset_trans subset_closure hbuffer)
  have hJ (x) (hx : x ∈ X) (u) (hu : u ∈ D) : δ ≤ phaseJacobian S x u := by
    rw [phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hSlocal hx hu]
    exact hgap x hx x hx u hu
  obtain ⟨hBs, hB, ⟨KB, hKB, hsB⟩, hsuppB, hpolyB, hjB⟩ :=
    hweighted X D Kout S c U a b hX hD hcX hKout hSlocal hc hU hsupp hphysical
      hc₀ hU₀ hmix hJ hdet hφjet hcjet hUjet
  have hAs := (maskedAmplitudes_contDiff hX hD hcX hSlocal hc hU
    (fun x hx u hu ↦ ne_of_gt (hδ.trans_le (hJ x hx u hu)))
    (fun x hx u hu ↦ norm_pos_iff.mp (hδU.trans_le (hdet x hx u hu))) hsupp).1
  have hsA := (maskedAmplitudes_physical_support S c U Kout hphysical).1
  have hsuppA := (maskedAmplitudes_tsupport_subset S c U).1.trans hsupp
  have hjA (j : ℕ) (z) (hz : z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b)
      (k : ℕ) (hk : k ≤ primitiveNormalReserve n) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0
        (maskedTransportAmplitude c U))) z‖ ≤ α :=
    maskedTransportAmplitude_normalized_jets_le (primitiveNormalReserve n) M hX hD hc hU
      _ a b (hcjet j) (hUjet j) hz hk
  have hpolyA (x u : E) :
      ‖maskedTransportAmplitude c U x u‖ ≤ PA * (1 + ‖u‖ ^ (0 : ℕ)) := by
    have hp := (hglobal X D S c U hX hD hcX hSlocal hsupp hc₀ hU₀ hmix hJ hdet x u).1
    simpa using hp.trans (show PA ≤ PA * (1 + (1 : ℝ)) by linarith)
  obtain ⟨T, V, hT, hTa, hV, hVa, hTtest, hVtest, hb, hidentity, _⟩ :=
    hcross X D O S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
      α β hα.le hβ.le hX hD hcX hO hbuffer hS hhom hmix hinj hgap hcollar hφjet hR
      hAs.contDiffOn hBs hjA hjB hAs.continuous hB Kout KB hKout hKB hsA hsB hsuppA hsuppB
      PA PB 0 0 hpolyA hpolyB
  refine ⟨T, V, hT.trans ?_, hTa.trans ?_, hV.trans ?_, hVa.trans ?_,
    hTtest, hVtest, hb, hidentity, ?_⟩
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le
  · exact maskedWeighted_cycleSymbol_diagonal_of_primitive_phase c U hX hD hcX hSlocal
      hsupp hδ hδU hgap hdet

end JanetCartan.FourierIntegral.UncutNormal
