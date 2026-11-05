module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.TestPairing
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests

/-!
# Finite physical sector equations and real compression

Source: `app:ch_regular_base:eq:energy-complete-residual`.
The input sector equations are the tested outputs of the uncut residual
construction. Density extends them to all L² sources for the same bounded
operators. Finite sums and the physical plus pairing then preserve those
equations. This is a downstream deduction, not a construction of its sector
inputs. The complete residual must be supplied with all three terms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector RegularSector.Realization FourierIntegral
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ
local notation "H" => EuclideanSpace ℂ (Fin q)
local notation "C2" => Lp H 2 (volume : Measure E)
local notation "R2" => Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E)

/-- A tested equation on compact smooth sources extends to all L² sources
by density and continuity of the physical test action. Consumer: finite
sector pairing, and ultimately the supported inputs of
`FixedDomainInverse.exact_physical_localSobolev_ae`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalTestAction_eq_of_graphTests
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (S G : C2 →L[ℂ] C2)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q)
    (htest : ∀ v : graphTestSpace n q,
      physicalTestAction A B (fun x ↦ (S (graphTestToLp v) x).ofLp) φ i =
        ∫ x, φ x • G (graphTestToLp v) x i) (f : C2) :
    physicalTestAction A B (fun x ↦ (S f x).ofLp) φ i = ∫ x, φ x • G f x i := by
  let L := physicalTestActionLp A B hA hB φ hφ hc i
  let M := testCoordinatePairing φ (hφ.continuous.memLp_of_hasCompactSupport hc) i
  have he : (fun f ↦ L (S f)) = fun f ↦ M (G f) :=
    denseRange_graphTestToLp.equalizer
      ((physicalTestActionLp_continuous A B hA hB φ hφ hc i).comp S.continuous)
      ((testCoordinatePairing_continuous φ _ i).comp G.continuous)
      (funext fun v ↦ by simpa [L, M, testCoordinatePairing, Function.comp_apply, physicalTestActionLp_apply] using htest v)
  simpa [L, M, testCoordinatePairing, Function.comp_apply, physicalTestActionLp_apply] using congrFun he f

/-- The physical plus pairing preserves addition of entire sector operators.
Thus the principal Op(α) and the complete residual remain separate; scalars
inside a conjugate factor are conjugated with that factor
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalPairedSectorSum_add {ι : Type*} (s : Finset ι)
    (G R : ι → C2 →L[ℂ] C2) :
    physicalPairedSectorSum s (fun j ↦ G j + R j) =
      physicalPairedSectorSum s G + physicalPairedSectorSum s R := by
  apply ContinuousLinearMap.ext
  intro f
  change ((∑ j ∈ s, (G j + R j)) f + star ((∑ j ∈ s, (G j + R j)) (star f))) = _
  change _ = ((∑ j ∈ s, G j) f + star ((∑ j ∈ s, G j) (star f))) +
    ((∑ j ∈ s, R j) f + star ((∑ j ∈ s, R j) (star f)))
  simp only [Finset.sum_add_distrib, add_apply, star_add]
  abel

/-- Finite sums and the physical pairing S + cSc preserve the actual tested
sector equations, first extended by density from compact smooth sources.
The same conclusion holds for every L² input. In its complete-residual use,
G is Op(α) plus all three actual residual terms; it is never replaced by I.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalPairedSectorSum_test {ι : Type*}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (s : Finset ι) (S G : ι → C2 →L[ℂ] C2)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q)
    (hsector : ∀ j ∈ s, ∀ v : graphTestSpace n q,
      physicalTestAction A B (fun x ↦ (S j (graphTestToLp v) x).ofLp) φ i =
        ∫ x, φ x • G j (graphTestToLp v) x i) (f : C2) :
    physicalTestAction A B (fun x ↦ (physicalPairedSectorSum s S f x).ofLp) φ i =
      ∫ x, φ x • physicalPairedSectorSum s G f x i := by
  let L := physicalTestActionLp A B hA hB φ hφ hc i
  let M := testCoordinatePairing φ (hφ.continuous.memLp_of_hasCompactSupport hc) i
  have hj (j : ι) (hj : j ∈ s) (v : C2) : L (S j v) = M (G j v) := by
    simpa [L, M, testCoordinatePairing, Function.comp_apply, physicalTestActionLp_apply] using
      physicalTestAction_eq_of_graphTests A B hA hB (S j) (G j) hφ hc i (hsector j hj) v
  have hsum (v : C2) : L ((∑ j ∈ s, S j) v) = M ((∑ j ∈ s, G j) v) := by
    simp only [sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun j hj' ↦ hj j hj' v)
  rw [← physicalTestActionLp_apply A B hA hB φ hφ hc i]
  change L ((∑ j ∈ s, S j) f + star ((∑ j ∈ s, S j) (star f))) =
    M ((∑ j ∈ s, G j) f + star ((∑ j ∈ s, G j) (star f)))
  rw [map_add, map_add, physicalTestActionLp_star, testCoordinatePairing_star,
    hsum f, hsum (star f)]

/-- The real-compressed physical solver satisfies the same tested equation
on embedded real inputs, with no additional factor of i or sign change.
The principal and complete residual are compressed using the same pairing
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem realCompression_physicalPairedSectorSum_test {ι : Type*}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (s : Finset ι) (S G : ι → C2 →L[ℂ] C2)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q)
    (hsector : ∀ j ∈ s, ∀ v : graphTestSpace n q,
      physicalTestAction A B (fun x ↦ (S j (graphTestToLp v) x).ofLp) φ i =
        ∫ x, φ x • G j (graphTestToLp v) x i) (f : R2) :
    physicalTestAction A B
      (fun x ↦ (l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s S) f) x).ofLp) φ i =
      ∫ x, φ x • l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s G) f) x i := by
  rw [inclusion_realCompression_physicalPairedSectorSum,
    inclusion_realCompression_physicalPairedSectorSum]
  exact physicalPairedSectorSum_test A B hA hB s S G hφ hc i hsector _

/-- Once the same paired output has its local H¹ weak derivative, its tested
equation is an a.e. equation on the open measurement plateau. This requires
no separate differentiation of an uncut kernel. The H¹ producer is the
sector parent's graph/PDO estimates
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalPairedSectorSum_ae {ι : Type*}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (s : Finset ι) (S G : ι → C2 →L[ℂ] C2) {U : Set E} (hU : IsOpen U)
    (hsector : ∀ j ∈ s, ∀ v : graphTestSpace n q,
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
        physicalTestAction A B (fun x ↦ (S j (graphTestToLp v) x).ofLp) φ i =
          ∫ x, φ x • G j (graphTestToLp v) x i)
    (f : C2) (du : E → E →L[ℝ] FV)
    (hdu : Mollification.HasWeakFDerivOn volume
      (fun x ↦ (physicalPairedSectorSum s S f x).ofLp) du U) :
    physicalWeakApply A B (fun x ↦ (physicalPairedSectorSum s S f x).ofLp) du
      =ᵐ[volume.restrict U] fun x ↦ (physicalPairedSectorSum s G f x).ofLp := by
  let L : H →L[ℝ] FV :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).toContinuousLinearMap.restrictScalars ℝ
  have hg : MemLp (fun x ↦ (physicalPairedSectorSum s G f x).ofLp) 2 volume :=
    L.comp_memLp' (Lp.memLp _)
  apply physicalWeakApply_ae_eq_of_test A B hA hB hU hdu
    ((hg.locallyIntegrable (by norm_num)).locallyIntegrableOn U)
  intro φ hφ hc hs i
  exact physicalPairedSectorSum_test A B hA hB s S G hφ hc i
    (fun j hj v ↦ hsector j hj v φ hφ hc hs i) f

/-- The finite physical equation keeps the principal operator separate from
all three residual terms. In particular, the scalar 1/i is inside the
conjugated residual factor, so the partner has its conjugate scalar.
No low-frequency part of Op(α) is identified with the identity.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem completeResidual_physicalPairedSectorSum_test {ι : Type*}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (s : Finset ι) (S principal endpoint retarded derivative : ι → C2 →L[ℂ] C2)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q)
    (hsector : ∀ j ∈ s, ∀ v : graphTestSpace n q,
      physicalTestAction A B (fun x ↦ (S j (graphTestToLp v) x).ofLp) φ i =
        ∫ x, φ x • ((principal j +
          (endpoint j + retarded j + (1 / Complex.I) • derivative j)) (graphTestToLp v)) x i)
    (f : C2) :
    physicalTestAction A B (fun x ↦ (physicalPairedSectorSum s S f x).ofLp) φ i =
      ∫ x, φ x • ((physicalPairedSectorSum s principal +
        physicalPairedSectorSum s (fun j ↦ endpoint j + retarded j +
          (1 / Complex.I) • derivative j)) f) x i := by
  have h := physicalPairedSectorSum_test A B hA hB s S
    (fun j ↦ principal j + (endpoint j + retarded j + (1 / Complex.I) • derivative j))
    hφ hc i hsector f
  rwa [physicalPairedSectorSum_add] at h

/-- The same a.e. physical equation holds for the existing real compression,
viewed through its exact complex inclusion. The weak derivative belongs to
that same included output. This retains Euclidean Lebesgue measure and
restricts only to the actual open measurement domain
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem realCompression_physicalPairedSectorSum_ae {ι : Type*}
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (s : Finset ι) (S G : ι → C2 →L[ℂ] C2) {U : Set E} (hU : IsOpen U)
    (hsector : ∀ j ∈ s, ∀ v : graphTestSpace n q,
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
        physicalTestAction A B (fun x ↦ (S j (graphTestToLp v) x).ofLp) φ i =
          ∫ x, φ x • G j (graphTestToLp v) x i)
    (f : R2) (du : E → E →L[ℝ] FV)
    (hdu : Mollification.HasWeakFDerivOn volume
      (fun x ↦ (l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s S) f) x).ofLp) du U) :
    physicalWeakApply A B
      (fun x ↦ (l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s S) f) x).ofLp) du
      =ᵐ[volume.restrict U] fun x ↦ (l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s G) f) x).ofLp := by
  rw [inclusion_realCompression_physicalPairedSectorSum] at hdu
  rw [inclusion_realCompression_physicalPairedSectorSum,
    inclusion_realCompression_physicalPairedSectorSum]
  exact physicalPairedSectorSum_ae A B hA hB s S G hU hsector _ du hdu

end JanetCartan.CharacteristicTransport.CompleteResidual
