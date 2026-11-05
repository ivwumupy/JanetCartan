module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.KernelConcentration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization

/-!
# A single realization for the constructed finite-band kernels

The finite-ceiling event in `app:ch_waves:eq:sampling-all-prefixes` is obtained
from the proved Bernstein inequality, intersected with admissible shifts, and
used without resampling for the background quadrature. Its scalar failure
budget is explicit. Actual geometric kernel data, the sharp band estimate,
and the largest continuum-normal bound remain with the source construction;
the asymptotic choice of the scalar parameters remains an assembly obligation.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators ContDiff

namespace JanetCartan.Sampling
open SeparatedSampling Realization RawInputPartition SamplingKernelBounds LatticeQuadrature
open BackgroundQuadrature

variable {n J p : ℕ} {A : Type*} [Fintype A]

/-- The union bound on the one fixed ceiling includes every grouped prefix,
without independence between prefixes (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem refinedKernelPrefix_allPrefixes_failure_le
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    {B W h C_op R C t : ℝ} {P : A → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * W ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    familyShiftLaw A p B h (allPrefixesGood (Finset.range (J + 1))
      (fun L ↦ familyDeviation p B ψ w h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))) t)ᶜ ≤
      (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
        (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
          (countConstant p B * (P a * W ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t := by
  let Δ L := familyDeviation p B ψ w h (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))
  have he : (allPrefixesGood (Finset.range (J + 1)) Δ t)ᶜ =
      ⋃ L ∈ Finset.range (J + 1), {ξ | t < ‖Δ L ξ‖} := by
    ext ξ
    simp [allPrefixesGood]
  change familyShiftLaw A p B h (allPrefixesGood _ Δ t)ᶜ ≤ _
  rw [he]
  apply (measure_biUnion_finset_le (Finset.range (J + 1)) _).trans
  calc
    _ ≤ ∑ _L ∈ Finset.range (J + 1), OperatorCompression.bernsteinTail R (R * C)
        (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
          (countConstant p B * (P a * W ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t :=
      Finset.sum_le_sum fun L _ ↦ operatorBernstein_refinedKernelPrefix D hn L hw hψ hψc hwc
        hh hh₁ hC_op hband hblock hR hC hmean ht hthreshold
    _ = _ := by simp [nsmul_eq_mul]

/-- One admissible sample set satisfies all original grouped prefixes and the
deterministic background estimate (`app:ch_waves:thm:sampling`). A strict scalar
Bernstein budget, not a successful-event hypothesis, gives existence. The
background family and its derivative bounds are quantified after the shifts,
so later background choices use these same nodes and weights. -/
theorem exists_refinedKernelPrefix_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) {ψ : A → Point → ℝ} {B h C_op R C t : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hh : 0 < h) (hh₁ : h ≤ 1) (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * 1 ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2)
    (hfailure : (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
      (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t < 1) :
    ∃ ξ : A → ShiftSpace p B h,
      (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧ extendedShift (ξ a) q i < h) ∧
      (∀ L ≤ J, ‖familyDeviation p B ψ (convolvedBoxWindow κ p) h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t) ∧
      (∀ a, SampleGeometry p B (P a) 1 (ψ a) (convolvedBoxWindow κ p) h
        (extendedShift (ξ a))) ∧
      (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Q : A → ℝ),
        (∀ a c, ContDiff ℝ p (fun z ↦ ψ a z • G a c z)) →
        (∀ a, 0 ≤ Q a) →
        (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a c z) z‖ ≤ Q a) →
        ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) h
          (fun a ↦ extendedShift (ξ a)) G‖ ≤
            BackgroundQuadrature.backgroundQuadratureConstant p B * (∑ a, Q a) * h ^ p) := by
  let := isProbabilityMeasure_familyShiftLaw (J := A) p B hh
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  let Δ L := familyDeviation p B ψ (convolvedBoxWindow κ p) h
    (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))
  let good := allPrefixesGood (Finset.range (J + 1)) Δ t
  have hmeas : MeasurableSet good := measurableSet_familyGood B h hψc hwc _ _
    (fun L a c ↦ (continuous_refinedKernelPrefix (D a) L).comp
      (continuous_const.prodMk continuous_id)) t
  have hbad : familyShiftLaw A p B h goodᶜ < 1 :=
    (refinedKernelPrefix_allPrefixes_failure_le D hn hw hψ hψc hwc hh hh₁
      hC_op hband hblock hR hC hmean ht hthreshold).trans_lt hfailure
  have hgood : 0 < familyShiftLaw A p B h good := by
    by_contra hz
    have hz' : familyShiftLaw A p B h good = 0 := le_antisymm (not_lt.mp hz) bot_le
    rw [prob_compl_eq_one_sub hmeas, hz', tsub_zero] at hbad
    exact lt_irrefl _ hbad
  have hreal : 0 < (familyShiftLaw A p B h).real good :=
    ENNReal.toReal_pos hgood.ne' (measure_ne_top _ _)
  obtain ⟨ξ, hξgood, hξ⟩ := exists_mem_of_positive_of_ae _ hreal
    (ae_admissible_familyShift (J := A) (p := p) (B := B) hh)
  refine ⟨ξ, hξ, ?_, ?_, ?_⟩
  · intro L hL
    exact hξgood L (Finset.mem_range.mpr (Nat.lt_succ_of_le hL))
  · intro a
    exact sampleGeometry_of_admissible hw (hψ a) hh hh₁ _ (hξ a)
  · intro G Q hG hQ hderiv
    exact norm_familyBackgroundError_le hc hs hm hkpos hk hp hψ G hG Q hQ hderiv
      hh hh₁ _ hξ

end JanetCartan.Sampling
