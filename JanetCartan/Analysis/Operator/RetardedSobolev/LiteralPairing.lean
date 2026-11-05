module

public import JanetCartan.Analysis.Operator.RetardedSobolev.ClassicalOperator
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Duality

/-!
# Ambient smooth adjoint pairing

The rectangle Fubini identity extends to the full ambient pairing because the
exterior cutoffs vanish outside the fixed strip (`app:ch_osc:eq:retarded-literal-adjoint`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ComplexConjugate

namespace JanetCartan.RetardedSobolev

open Spaces

/-- The actual lower and upper test operators satisfy the ambient smooth L²
pairing, with no adjoint identity assumed
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem retardedTest_adjoint_pairing {d : ℕ} (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout)
    (hsin_time : tsupport χin ⊆ Icc a b ×ˢ univ)
    (hsout_time : tsupport χout ⊆ Icc a b ×ˢ univ) (f g : Test d) :
    smoothPairing g (lowerTest a χin χout hin hout hsout f) =
      smoothPairing (upperTest b χin χout hin hout hsin g) f := by
  have h := Retarded.adjoint_pairing_of_continuous_hasCompactSupport volume a b hab
    χin χout hin.continuous hout.continuous hsin hsout f g
    (by simpa only [jet_zeroIndex] using
      jet_memLp (volume.prod (volume.restrict (Icc a b))) (zeroIndex d 0) f)
    (by simpa only [jet_zeroIndex] using
      jet_memLp (volume.prod (volume.restrict (Icc a b))) (zeroIndex d 0) g)
  have hμ : (volume : Measure ((Fin d → ℝ) × ℝ)).restrict (univ ×ˢ Icc a b) =
      volume.prod (volume.restrict (Icc a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hμ] at h
  have hl : (∫ p : (Fin d → ℝ) × ℝ in univ ×ˢ Icc a b,
      Retarded.lower a χin χout f (p.2, p.1) * conj (g.val (p.2, p.1))) =
      ∫ p : (Fin d → ℝ) × ℝ,
        Retarded.lower a χin χout f (p.2, p.1) * conj (g.val (p.2, p.1)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have hz : Retarded.lower a χin χout f (p.2, p.1) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs ↦ hp ⟨mem_univ _,
        (hsout_time (tsupport_lower_subset a χin χout f hs)).1⟩)
    simp [hz]
  have hu : (∫ p : (Fin d → ℝ) × ℝ in univ ×ˢ Icc a b,
      f.val (p.2, p.1) * conj (Retarded.upper b χin χout g (p.2, p.1))) =
      ∫ p : (Fin d → ℝ) × ℝ,
        f.val (p.2, p.1) * conj (Retarded.upper b χin χout g (p.2, p.1)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have hz : Retarded.upper b χin χout g (p.2, p.1) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs ↦ hp ⟨mem_univ _,
        (hsin_time (tsupport_upper_subset b χin χout g hs)).1⟩)
    simp [hz]
  rw [hl, hu] at h
  simpa only [smoothPairing, lowerTest, upperTest, LinearMap.coe_mk, AddHom.coe_mk,
    mul_comm, starRingEnd_apply] using h

/-- Conjugate symmetry of the literal smooth pairing used to reverse the
adjoint identity (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem smoothPairing_conj_symm {d : ℕ} (g f : Test d) :
    conj (smoothPairing g f) = smoothPairing f g := by
  unfold smoothPairing
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p ↦ by simp only [map_mul, starRingEnd_apply, star_star, mul_comm])

/-- The reverse adjoint identity for the upper test operator
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem retardedTest_reverse_adjoint_pairing {d : ℕ} (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout)
    (hsin_time : tsupport χin ⊆ Icc a b ×ˢ univ)
    (hsout_time : tsupport χout ⊆ Icc a b ×ˢ univ) (f g : Test d) :
    smoothPairing g (upperTest b χin χout hin hout hsin f) =
      smoothPairing (lowerTest a χin χout hin hout hsout g) f := by
  have h := congrArg conj (retardedTest_adjoint_pairing a b hab χin χout hin hout
    hsin hsout hsin_time hsout_time g f)
  simpa only [smoothPairing_conj_symm] using h.symm

end JanetCartan.RetardedSobolev
