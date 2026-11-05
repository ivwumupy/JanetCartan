module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.KernelRealization

/-!
# One original sample for the measured and scalar auxiliary rows

The amplitude test in paper-v2 `new:eq:amplitude-test` needs a scalar auxiliary
row on the SAME sampled nodes as the measured canonical row.  A measured-row
bound alone does not imply the scalar bound.  This file intersects the two
proved Bernstein events on the one original shift law before the source
Picard count is chosen.  Both rows retain every original grouped prefix.

The kernels, sharp single-band estimates and continuum mean bounds must be
instantiated from the same current phase and fixed cutoffs. Those original
analytic inputs are not replaced by a successful-sample hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace BigOperators ContDiff

namespace JanetCartan.PhysicalMean

open Sampling SeparatedSampling Sampling.Realization RawInputPartition SamplingKernelBounds
  LatticeQuadrature Sampling.BackgroundQuadrature

variable {n J p : ℕ} {A : Type*} [Fintype A]

/-- One admissible realization handles BOTH the original measured kernels
and the scalar auxiliary kernels, every fixed-ceiling prefix, and subsequent
deterministic background quadrature. The scalar failure budgets are added,
not the sample weights; no duplicated sample or enlarged count is introduced
(`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`). -/
theorem exists_common_measured_scalar_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    (D Dscalar : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) {ψ : A → Point → ℝ} {B h C_op R C t : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hh : 0 < h) (hh₁ : h ≤ 1) (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hbandScalar : ∀ a (i : RefinedIndex J) c z,
      ‖(Dscalar a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * 1 ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (hmeanScalar : ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) h
      (fun c z ↦ refinedKernelPrefix (Dscalar a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2)
    (hfailure : (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
      (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t +
      (J + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
      (R * ((∑ a, ((Dscalar a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
        (countConstant p B * (P a * 1 ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t < 1) :
    ∃ ξ : A → ShiftSpace p B h,
      (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧ extendedShift (ξ a) q i < h) ∧
      (∀ L ≤ J, ‖familyDeviation p B ψ (convolvedBoxWindow κ p) h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t) ∧
      (∀ L ≤ J, ‖familyDeviation p B ψ (convolvedBoxWindow κ p) h
        (fun a c z ↦ refinedKernelPrefix (Dscalar a) L (c, z)) ξ‖ ≤ t) ∧
      (∀ a, SampleGeometry p B (P a) 1 (ψ a) (convolvedBoxWindow κ p) h
        (extendedShift (ξ a))) ∧
      (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Q : A → ℝ),
        (∀ a c, ContDiff ℝ p (fun z ↦ ψ a z • G a c z)) →
        (∀ a, 0 ≤ Q a) →
        (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a c z) z‖ ≤ Q a) →
        ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) h
          (fun a ↦ extendedShift (ξ a)) G‖ ≤
            backgroundQuadratureConstant p B * (∑ a, Q a) * h ^ p) := by
  let := isProbabilityMeasure_familyShiftLaw (J := A) p B hh
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  let Δ L := familyDeviation p B ψ (convolvedBoxWindow κ p) h
    (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))
  let Δscalar L := familyDeviation p B ψ (convolvedBoxWindow κ p) h
    (fun a c z ↦ refinedKernelPrefix (Dscalar a) L (c, z))
  let good := allPrefixesGood (Finset.range (J + 1)) Δ t
  let goodScalar := allPrefixesGood (Finset.range (J + 1)) Δscalar t
  have hmeas : MeasurableSet good := measurableSet_familyGood B h hψc hwc _ _
    (fun L a c ↦ (continuous_refinedKernelPrefix (D a) L).comp
      (continuous_const.prodMk continuous_id)) t
  have hmeasScalar : MeasurableSet goodScalar := measurableSet_familyGood B h hψc hwc _ _
    (fun L a c ↦ (continuous_refinedKernelPrefix (Dscalar a) L).comp
      (continuous_const.prodMk continuous_id)) t
  have hbad : familyShiftLaw A p B h (good ∩ goodScalar)ᶜ < 1 := by
    rw [compl_inter]
    exact ((measure_union_le _ _).trans
      (add_le_add
        (refinedKernelPrefix_allPrefixes_failure_le D hn hw hψ hψc hwc hh hh₁
          hC_op hband hblock hR hC hmean ht hthreshold)
        (refinedKernelPrefix_allPrefixes_failure_le Dscalar hn hw hψ hψc hwc hh hh₁
          hC_op hbandScalar hblock hR hC hmeanScalar ht hthreshold))).trans_lt hfailure
  have hgood : 0 < familyShiftLaw A p B h (good ∩ goodScalar) := by
    by_contra hz
    have hz' : familyShiftLaw A p B h (good ∩ goodScalar) = 0 :=
      le_antisymm (not_lt.mp hz) bot_le
    rw [prob_compl_eq_one_sub (hmeas.inter hmeasScalar), hz', tsub_zero] at hbad
    exact lt_irrefl _ hbad
  have hreal : 0 < (familyShiftLaw A p B h).real (good ∩ goodScalar) :=
    ENNReal.toReal_pos hgood.ne' (measure_ne_top _ _)
  obtain ⟨ξ, hξgood, hξ⟩ := exists_mem_of_positive_of_ae _ hreal
    (ae_admissible_familyShift (J := A) (p := p) (B := B) hh)
  refine ⟨ξ, hξ, ?_, ?_, ?_, ?_⟩
  · intro L hL
    exact hξgood.1 L (Finset.mem_range.mpr (Nat.lt_succ_of_le hL))
  · intro L hL
    exact hξgood.2 L (Finset.mem_range.mpr (Nat.lt_succ_of_le hL))
  · intro a
    exact sampleGeometry_of_admissible hw (hψ a) hh hh₁ _ (hξ a)
  · intro G Q hG hQ hderiv
    exact norm_familyBackgroundError_le hc hs hm hkpos hk hp hψ G hG Q hQ hderiv
      hh hh₁ _ hξ

end JanetCartan.PhysicalMean
