module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactSupport

/-!
# Joint integrability after conic substitution

The second Fubini step in `app:ch_background:eq:bg-full-complex-amplitude`,
used for modified adjoints in `app:ch_background:prop:bg-adjoint`. Compact
source support inside the conic chart, continuous forward and inverse maps,
and a nonzero continuous Jacobian imply absolute joint integrability. No
normal identity or operator bound is an input.
-/

@[expose] public noncomputable section
open MeasureTheory Set

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ContinuumRow.TransportKernel NormalComparison
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Compact-image proof of joint transformed integrability. The support set
`C` is a compact subset of the genuine source chart; its image retains the
spectator coordinate (`app:ch_background:eq:bg-full-complex-amplitude`).
Consumer: `modifiedNormalKernel_eq_fullAmplitude_of_compactChart`. -/
theorem integrable_joint_modifiedInverseDensity
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
    (hm : Continuous m)
    (e : Euclidean n ≃ᵐ SliceVariable n) (hec : Continuous e)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (C : Set (Euclidean 2 × Euclidean n)) (hC : IsCompact C)
    (hCD : ∀ p ∈ C, p.2 ∈ D p.1)
    (hΨc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ p.1 p.2)) C)
    (hUc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ U p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ p.1 p.2)) '' C))
    (hJc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ J p.1 p.2) C)
    (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ p : Euclidean 2 × Euclidean n, p ∉ C →
      modifiedNormalDensity a m x y (chartCarrierVariable e p.1 p.2) = 0) :
    Integrable (fun p : Euclidean 2 × Euclidean n ↦
      modifiedInverseDensity a m x y e D Ψ U J p.1 p.2) (volume.prod volume) := by
  let T : Euclidean 2 × Euclidean n → Euclidean 2 × Euclidean n :=
    fun p ↦ (p.1, Ψ p.1 p.2)
  let S := T '' C
  let V : Euclidean 2 × Euclidean n → Euclidean 2 × Euclidean n :=
    fun p ↦ (p.1, U p.1 p.2)
  let F : Euclidean 2 × Euclidean n → ℂ := fun p ↦
    |(J p.1 (U p.1 p.2)).det|⁻¹ •
      modifiedNormalDensity a m x y (chartCarrierVariable e p.1 (U p.1 p.2))
  have hS : IsCompact S := hC.image_of_continuousOn hΨc
  have hV : ContinuousOn V S := continuous_fst.continuousOn.prodMk hUc
  have hVC : MapsTo V S C := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [V, T, hU p.1 p.2 (hCD p hp)] using hp
  have hdet : ContinuousOn (fun p ↦ (J p.1 (U p.1 p.2)).det) S :=
    ContinuousLinearMap.continuous_det.continuousOn.comp (hJc.comp hV hVC) (mapsTo_univ _ _)
  have hdet0 : ∀ p ∈ S, (J p.1 (U p.1 p.2)).det ≠ 0 := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [T, hU p.1 p.2 (hCD p hp)] using hJ p.1 p.2 (hCD p hp)
  have hc : Continuous (fun p : Euclidean 2 × Euclidean n ↦
      chartCarrierVariable e p.1 p.2) :=
    ((hec.comp continuous_snd).fst.prodMk continuous_fst).prodMk
      (hec.comp continuous_snd).snd
  have hd : Continuous (fun p : Euclidean 2 × Euclidean n ↦
      modifiedNormalDensity a m x y (chartCarrierVariable e p.1 p.2)) := by
    exact ((Complex.continuous_ofReal.comp (hm.comp hc)).pow 2).mul
      ((ha.comp (continuous_const.prodMk hc)).star.mul
        (ha.comp (continuous_const.prodMk hc)))
  have hF : ContinuousOn F S :=
    (hdet.abs.inv₀ (fun p hp ↦ abs_ne_zero.mpr (hdet0 p hp))).smul
      (hd.continuousOn.comp hV (mapsTo_univ _ _))
  have hi := (hF.integrableOn_compact (μ := volume.prod volume) hS).integrable_indicator hS.measurableSet
  apply hi.congr
  filter_upwards [] with p
  by_cases hp : p ∈ S
  · obtain ⟨q, hq, hqp⟩ := hp
    have hmem : p.2 ∈ Ψ p.1 '' D p.1 := by
      rw [← hqp]
      exact mem_image_of_mem _ (hCD q hq)
    simp only [indicator_of_mem (show p ∈ S from ⟨q, hq, hqp⟩),
      modifiedInverseDensity, indicator_of_mem hmem]
    rfl
  · rw [indicator_of_notMem hp]
    symm
    by_cases hk : p.2 ∈ Ψ p.1 '' D p.1
    · obtain ⟨t, ht, htp⟩ := hk
      have hout : (p.1, t) ∉ C := by
        intro hct
        apply hp
        exact ⟨(p.1, t), hct, Prod.ext rfl htp⟩
      rw [← htp]
      simp [modifiedInverseDensity, hU p.1 t ht, hsupp (p.1, t) hout,
        mem_image_of_mem (Ψ p.1) ht]
    · simp [modifiedInverseDensity, hk]

/-- The exact conic normal identity with both Fubini premises discharged
from primitive compact support and chart geometry. The coordinate equivalence
preserves the literal slice measure; no graph or torus replaces the carrier
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem modifiedNormalKernel_eq_fullAmplitude_of_compactChart
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (e : Euclidean n ≃ᵐ SliceVariable n) (hec : Continuous e)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (C : Set (Euclidean 2 × Euclidean n)) (hC : IsCompact C)
    (hCD : ∀ p ∈ C, p.2 ∈ D p.1)
    (hΨc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ p.1 p.2)) C)
    (hUc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ U p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ p.1 p.2)) '' C))
    (hJc : ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ J p.1 p.2) C)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v))
    (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ p : Euclidean 2 × Euclidean n, p ∉ C →
      modifiedNormalDensity a m x y (chartCarrierVariable e p.1 p.2) = 0)
    (hphase : ∀ v t, t ∈ D v →
      Φ (chartCarrierVariable e v t).1 x (chartCarrierVariable e v t).2 -
        Φ (chartCarrierVariable e v t).1 y (chartCarrierVariable e v t).2 =
          inner ℝ (x - y) (Ψ v t)) :
    modifiedNormalKernel Φ a m x y = ∫ k,
      oscillatoryFactor 1 (inner ℝ (x - y) k) *
        modifiedNormalAmplitude a m x y e D Ψ U J k := by
  apply modifiedNormalKernel_eq_fullAmplitude Φ a m x y e he D Ψ U J
    hD hΨ hinj hU hJ
  · intro v t ht
    apply hsupp (v, t)
    exact fun hp ↦ ht (hCD (v, t) hp)
  · exact hphase
  · exact integrable_modifiedNormalKernel_integrand Φ a m hΦ ha hm hms x y
  · have hi := integrable_joint_modifiedInverseDensity a m x y ha hm e hec
      D Ψ U J C hC hCD hΨc hUc hJc hU hJ hsupp
    apply hi.bdd_mul (c := 1)
    · exact (by fun_prop : Continuous (fun p : Euclidean 2 × Euclidean n ↦
        Complex.exp (Complex.I * (1 * inner ℝ (x - y) p.2 : ℝ)))).aestronglyMeasurable
    · filter_upwards [] with p
      simp [oscillatoryFactor, Complex.norm_exp]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
