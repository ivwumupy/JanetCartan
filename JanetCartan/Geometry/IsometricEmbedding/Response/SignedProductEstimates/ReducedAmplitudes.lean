module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Amplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.StressBudgets

/-!
# The complete reduced signed amplitude jets

The actual current stress contraction in `app:ch_pairs:prop:pairs-lag-sum`
is bilinear in the original real row and the complete complex tensor.
Reuse its existing continuous bilinear map to prove the original `L^r`
profile, including both cutoffs and the doubled plus diagonal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open Sampling.BackgroundModulation
variable {n N : ℕ}

open RawPrimary.AmplitudeGrades.Polynomial

/-- Smoothness of the actual reduced plus/minus amplitudes, retaining the
same stress row and reduced cutoff (`app:ch_pairs:eq:pairs-lag-envelope`).
This supplies the compact source admission used by the fixed inverse. -/
theorem contDiffOn_reduced_signed_amplitudes
    {U : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    {η : Euclidean n → ℝ} {A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ}
    (hQ : ContDiffOn ℝ ∞ Q U) (hη : ContDiffOn ℝ ∞ η U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun x ↦ η x • ((1 / 2 : ℝ) • complexStressContraction (Q x)
      (symmetricBilinearTensor (A x) (B x)))) U ∧
    ContDiffOn ℝ ∞ (fun x ↦ η x • ((1 / 2 : ℝ) • complexStressContraction (Q x)
      (symmetricBilinearTensor (A x) ((B x).map conj)))) U := by
  obtain ⟨hp, hm⟩ := contDiffOn_signed_tensor_amplitudes hA hB
  let R := (1 / 2 : ℝ) • complexStressContractionLinear n
  have hcont (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
      (ha : ContDiffOn ℝ ∞ a U) :
      ContDiffOn ℝ ∞ (fun x ↦ η x • (R (Q x) (a x))) U :=
    hη.smul (R.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (g := fun p : (Fin n → MetricTensor n) × Matrix (Fin n) (Fin n) ℂ ↦ R p.1 p.2)
      (f := fun x ↦ (Q x, a x)) (hQ.prodMk ha))
  exact ⟨hcont _ hp, hcont _ hm⟩

/-- Leibniz estimates for the complete reduced signed amplitudes
(`app:ch_pairs:prop:pairs-lag-sum`, Step 1). The row, both original cutoffs and
the full tensor factors consume only their total derivative order. Constants
precede scales and all varying source data; no accuracy parameter enters.
The row profile is supplied by `exists_projectedStress_jet_budgets` for the
actual projected row, or by its retained extension producer on that same row.
Consumed by the reduced Sobolev-source estimates for the original inverse. -/
theorem exists_cutoff_reduced_signed_jet_constants
    (X Y CQ C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) :
    ∃ J : ℕ → ℝ, (∀ r, 0 ≤ J r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ (χ η : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      ∀ x ∈ U, ∀ r,
        ‖iteratedFDeriv ℝ r (fun y ↦ χ y • (η y • ((1 / 2 : ℝ) •
          complexStressContraction (Q y) (symmetricBilinearTensor (A y) (B y))))) x‖ ≤ J r * L ^ r ∧
        ‖iteratedFDeriv ℝ r (fun y ↦ χ y • (η y • ((1 / 2 : ℝ) •
          complexStressContraction (Q y) (symmetricBilinearTensor (A y) ((B y).map conj))))) x‖ ≤
          J r * L ^ r := by
  obtain ⟨J, hJ, hjet⟩ := exists_cutoff_signed_tensor_jet_constants (n := n) (N := N) X C hX hC
  let R := (1 / 2 : ℝ) • complexStressContractionLinear n
  let H := productProfile R CQ J
  have hH := productProfile_nonneg R hCQ hJ
  let M := (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
  refine ⟨productProfile M Y H, productProfile_nonneg M hY hH, ?_⟩
  intro U hU L hL χ η Q A B hχ hη hQ hA hB hχb hηb hQb hAb hBb x hx r
  obtain ⟨hp, hm⟩ := contDiffOn_signed_tensor_amplitudes hA hB
  have hj := hjet U hU L hL χ A B hχ hA hB hχb hAb hBb
  have hfull (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
      (ha : ContDiffOn ℝ ∞ a U)
      (haj : ∀ j, ‖iteratedFDeriv ℝ j (fun y ↦ χ y • a y) x‖ ≤ J j * L ^ j) :
      ‖iteratedFDeriv ℝ r (fun y ↦ χ y • (η y • ((1 / 2 : ℝ) •
        complexStressContraction (Q y) (a y)))) x‖ ≤ productProfile M Y H r * L ^ r := by
    have hs : ContDiffOn ℝ ∞ (fun y ↦ R (Q y) (χ y • a y)) U :=
      R.isBoundedBilinearMap.contDiff.comp_contDiffOn
        (g := fun p : (Fin n → MetricTensor n) × Matrix (Fin n) (Fin n) ℂ ↦ R p.1 p.2)
        (f := fun y ↦ (Q y, χ y • a y)) (hQ.prodMk (hχ.smul ha))
    have hb (j) : ‖iteratedFDeriv ℝ j (fun y ↦ R (Q y) (χ y • a y)) x‖ ≤ H j * L ^ j :=
      jet_bilinear_le R (g := fun y ↦ χ y • a y) hU hQ (hχ.smul ha) hx (b := 0) hL hCQ hJ
        (hQb x hx) haj j
    have ht := jet_bilinear_le M (f := η) (g := fun y ↦ R (Q y) (χ y • a y))
      hU hη hs hx (b := 0) hL hY hH (hηb x hx) hb r
    have he : (fun y ↦ M (η y) (R (Q y) (χ y • a y))) =
        fun y ↦ χ y • (η y • ((1 / 2 : ℝ) • complexStressContraction (Q y) (a y))) := by
      funext y
      change η y • ((1 / 2 : ℝ) • complexStressContraction (Q y) (χ y • a y)) = _
      rw [LinearMapClass.map_smul_of_tower]
      simp only [smul_smul, mul_comm, mul_left_comm]
    rw [he] at ht
    simpa only [Nat.sub_zero] using ht
  exact ⟨hfull _ hp (fun j ↦ (hj x hx j).1), hfull _ hm (fun j ↦ (hj x hx j).2)⟩

end JanetCartan.SignedProductEstimates
