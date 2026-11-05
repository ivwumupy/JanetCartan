module

public import JanetCartan.Iteration.PhysicalSampling.OriginalEvent

/-!
# Common original-scale event from actual coefficient bounds

The corrected kernel's auxiliary amplitude bound is an arbitrary compactness
witness. A proved coefficient estimate need not bound that witness. Replace
ONLY support/bound evidence in both data records, preserving the literal
kernels, operators, original weights, refined shells and native scalar row.
The shared event then follows from the original revised numerical budget.
Consumer: the actual corrected/scalar join in `app:ch_waves:thm:sampling` and
`new:eq:amplitude-test`; sharp and mean estimates come from their analytic
producers, not from a successful realization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.PhysicalSampling

open Sampling Sampling.Realization SeparatedSampling SamplingKernelBounds
open RawInputPartition RawInputRealization LatticeQuadrature Sampling.BackgroundQuadrature
open CanonicalRowComparison PhysicalSamplingShells

/-- Proved coefficient bounds, rather than a comparison with an arbitrary
chosen amplitude-bound witness, feed the SAME measured/scalar common event.
Only proof/bound fields are replaced; every operator in the conclusion is the
original one, including its native scalar synthesis and carrier weights. -/
theorem exists_threshold_original_common_scalar_native_of_amplitude
    {A : Type*} [Fintype A] {n p : ℕ} (hn : 1 ≤ n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    {ψ : A → Point → ℝ} {B C_op Cmean : ℝ} {P M Mscalar Md Mdscalar : A → ℝ}
    (hB : 0 ≤ B) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hC_op : 0 ≤ C_op)
    (S Sscalar : A → Set (Euclidean n))
    (hS : ∀ a, IsCompact (S a)) (hSscalar : ∀ a, IsCompact (Sscalar a))
    (hM : ∀ a, 0 ≤ M a) (hMscalar : ∀ a, 0 ≤ Mscalar a)
    (hMd : ∀ a, 0 ≤ Md a) (hMdscalar : ∀ a, 0 ≤ Mdscalar a) :
    ∃ C > (0 : ℝ), ∃ T₀ ≥ (1 : ℝ), ∀ T ≥ T₀,
      let J := cutoffCount (T ^ fineExponent)
      let h := T ^ (-separationExponent)
      let t := T ^ (-((3 : ℝ) / 512))
      let w := convolvedBoxWindow κ p
      ∀ D Dscalar : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n,
        (∀ a q η x, x ∉ S a → (D a).amplitude ((q, η), x) = 0) →
        (∀ a q η x, x ∉ Sscalar a → (Dscalar a).amplitude ((q, η), x) = 0) →
        (∀ a q η x, ‖(D a).amplitude ((q, η), x)‖ ≤ M a) →
        (∀ a q η x, ‖(Dscalar a).amplitude ((q, η), x)‖ ≤ Mscalar a) →
        (∀ a η, ‖(D a).mask η‖ ≤ Md a) →
        (∀ a η, ‖(Dscalar a).mask η‖ ≤ Mdscalar a) →
        (∀ a (i : RefinedIndex J) color z, ψ a z ≠ 0 →
          ‖(D a).operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ C_op * refinedRadius i) →
        (∀ a (i : RefinedIndex J) color z, ψ a z ≠ 0 →
          ‖(Dscalar a).operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ C_op * refinedRadius i) →
        ‖∑ a, patchMeanNormal p B (ψ a) w h
          (fun color z ↦ refinedKernelPrefix (D a) J (color, z))‖ ≤ Cmean →
        ‖∑ a, patchMeanNormal p B (ψ a) w h
          (fun color z ↦ refinedKernelPrefix (Dscalar a) J (color, z))‖ ≤ Cmean →
      ∃ ξ : A → ShiftSpace p B h,
        (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧ extendedShift (ξ a) q i < h) ∧
        (∀ L ≤ J, ‖familyDeviation p B ψ w h
          (fun a color z ↦ refinedKernelPrefix (D a) L (color, z)) ξ‖ ≤ t) ∧
        (∀ L ≤ J, ‖familyDeviation p B ψ w h
          (fun a color z ↦ refinedKernelPrefix (Dscalar a) L (color, z)) ξ‖ ≤ t) ∧
        (∀ a, SampleGeometry p B (P a) 1 (ψ a) w h (extendedShift (ξ a))) ∧
        (∀ L ≤ J, ‖nativeScalarOperator hn B ψ w h (fun a ↦ extendedShift (ξ a)) Dscalar L‖ ≤
          Real.sqrt (C + 1)) ∧
        (Fintype.card (SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a))) : ℝ) ≤
          ((Fintype.card A : ℝ) * countConstant p B) * T ^ (1 + samplingSlack) ∧
        (∑ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
          sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i) ≤ countConstant p B * (∑ a, P a) ∧
        (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Qbg : A → ℝ),
          (∀ a color, ContDiff ℝ p (fun z ↦ ψ a z • G a color z)) →
          (∀ a, 0 ≤ Qbg a) →
          (∀ a color z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a color z) z‖ ≤ Qbg a) →
          ‖familyBackgroundError p B ψ w h (fun a ↦ extendedShift (ξ a)) G‖ ≤
            backgroundQuadratureConstant p B * (∑ a, Qbg a) * h ^ p) := by
  let Q := fun a ↦ volume.real (S a) * Md a ^ 2 * M a ^ 2 * unitBallVolume n
  let Qscalar := fun a ↦ volume.real (Sscalar a) * Mdscalar a ^ 2 * Mscalar a ^ 2 * unitBallVolume n
  have hQ (a) : 0 ≤ Q a := by dsimp [Q, unitBallVolume]; positivity
  have hQscalar (a) : 0 ≤ Qscalar a := by dsimp [Qscalar, unitBallVolume]; positivity
  obtain ⟨C, hC, T₀, hT₀, hsample⟩ :=
    exists_threshold_original_common_scalar_native (Cmean := Cmean) (V := V)
      hn hc hs hm hkpos hk hp hB hψ hψc (fun a ↦ add_nonneg (hQ a) (hQscalar a)) hC_op
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T hT J h t w D Dscalar hsupport hsupportScalar hamp hampScalar hmask hmaskScalar
    hband hbandScalar hmean hmeanScalar
  let E a : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n :=
    { D a with
      physicalSupport := S a
      physicalSupport_compact := hS a
      amplitude_eq_zero := hsupport a
      amplitudeBound := M a
      amplitudeBound_nonneg := hM a
      amplitude_le := hamp a
      maskBound := Md a
      maskBound_nonneg := hMd a
      mask_le := hmask a }
  let Escalar a : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n :=
    { Dscalar a with
      physicalSupport := Sscalar a
      physicalSupport_compact := hSscalar a
      amplitude_eq_zero := hsupportScalar a
      amplitudeBound := Mscalar a
      amplitudeBound_nonneg := hMscalar a
      amplitude_le := hampScalar a
      maskBound := Mdscalar a
      maskBound_nonneg := hMdscalar a
      mask_le := hmaskScalar a }
  exact hsample T hT E Escalar
    (fun a ↦ le_add_of_nonneg_right (hQscalar a))
    (fun a ↦ le_add_of_nonneg_left (hQ a)) hband hbandScalar hmean hmeanScalar

end JanetCartan.PhysicalSampling
