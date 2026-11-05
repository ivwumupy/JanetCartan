module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestEnergy.Schwartz

/-!
# The source-tail pairing on compact tests

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, integration by parts
and the self-adjoint Bessel pairing turn the actual source-square tail into
the difference of the two adjoint energies. Consumer:
`fixedSourceTail_energy_eq_inner_of_test`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
open JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison.SourceTailTestEnergy
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => 𝓢(E, ℂ)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)

/-- The complex realization underlying the fixed real tail
(`app:ch_background:prop:bg-frame`). -/
def complexTail (hR : 0 < R) (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : C² →L[ℂ] C² :=
  coefficientSourceCommutatorTailOperator
    (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
    (FixedCutoffs.physical hR 0) (fixedSourceSquare hR)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
    (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR)

/-- The original, unsquared physical source mask on Schwartz inputs
(`app:ch_background:prop:bg-frame`). -/
def sourceMask (hR : 0 < R) : S →L[ℂ] S :=
  SchwartzMap.smulLeftCLM ℂ (fun x ↦ (FixedCutoffs.physical hR 2 x : ℂ))

private theorem realMask_pairing (c : E → ℝ) (hc : c.HasTemperateGrowth) (u v : S) :
    imageSchwartzPairing (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) u) v =
      imageSchwartzPairing u (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) v) := by
  have htc : (fun x ↦ (c x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [imageSchwartzPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply htc, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

private theorem sourceSquare_pairing (hR : 0 < R) (w : S) :
    imageSchwartzPairing
        (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (fixedSourceSquare hR x : ℂ)) w) w =
      imageSchwartzPairing (sourceMask hR w) (sourceMask hR w) := by
  have ht := (FixedCutoffs.physical (n := n) hR 2).hasCompactSupport.hasTemperateGrowth
    (FixedCutoffs.physical hR 2).contDiff
  have hc : (fun x : E ↦ (FixedCutoffs.physical hR 2 x : ℂ)).HasTemperateGrowth := by fun_prop
  have hb : (fun x : E ↦ (fixedSourceSquare hR x : ℂ)).HasTemperateGrowth := by
    dsimp only [fixedSourceSquare]
    fun_prop
  simp only [imageSchwartzPairing_eq_integral, sourceMask]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.smulLeftCLM_apply_apply hb, SchwartzMap.smulLeftCLM_apply_apply hc]
  simp only [smul_eq_mul, fixedSourceSquare, Complex.ofReal_pow,
    star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem scalarTail_pairing (hR : 0 < R) (q : S)
    (hq : SchwartzMap.smulLeftCLM ℂ
      (fun x ↦ ((FixedCutoffs.physical hR 0 x) ^ 2 : ℂ)) q = q) :
    imageSchwartzPairing
      (SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((FixedCutoffs.physical hR 0 x) ^ 2 : ℂ))
        (imageBesselSchwartzCLM (imageBesselSchwartzCLM q -
          SchwartzMap.smulLeftCLM ℂ (fun x ↦ (fixedSourceSquare hR x : ℂ))
            (imageBesselSchwartzCLM q)))) q =
      imageSchwartzPairing (imageBesselSchwartzCLM q) (imageBesselSchwartzCLM q) -
        imageSchwartzPairing (sourceMask hR (imageBesselSchwartzCLM q))
          (sourceMask hR (imageBesselSchwartzCLM q)) := by
  have ht := (FixedCutoffs.physical (n := n) hR 0).hasCompactSupport.hasTemperateGrowth
    (FixedCutoffs.physical hR 0).contDiff
  have hsq : (fun x : E ↦ (FixedCutoffs.physical hR 0 x) ^ 2).HasTemperateGrowth := by fun_prop
  simp only [← Complex.ofReal_pow] at hq ⊢
  rw [realMask_pairing _ hsq, hq, imageBesselSchwartzCLM_pairing]
  have hsub (a b c : S) : imageSchwartzPairing (a - b) c =
      imageSchwartzPairing a c - imageSchwartzPairing b c := by
    change inner ℂ ((SchwartzMap.toLpCLM ℂ ℂ 2) (a - b)) (c.toLp 2) = _
    rw [map_sub, inner_sub_left]
    rfl
  rw [hsub, sourceSquare_pairing]

private theorem complexTail_toLp (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S) :
    complexTail hR A (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (coefficientSourceCommutatorTailSchwartz
        (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
        (FixedCutoffs.physical hR 0) (fixedSourceSquare hR) v) := by
  apply Lp.ext
  exact (coefficientSourceCommutatorTailOperator_ae_schwartz
    (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
    (FixedCutoffs.physical hR 0) (fixedSourceSquare hR)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
    (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR)
    (FixedCutoffs.physical hR 0).hasCompactSupport
    (fun y hy ↦ fixedSourceSquare_plateau hR y hy y (by simpa using hR))
    v _ (imageSchwartzFamilyToLp_ae v)).trans (imageSchwartzFamilyToLp_ae _).symm

/-- Exact complex pairing of the actual bounded tail with a plateau-supported
test. Its real part is the required real energy defect
(`app:ch_background:prop:bg-frame`). -/
theorem complexTail_inner (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S)
    (hv : ∀ i, tsupport (v i : E → ℂ) ⊆
      interior {x | FixedCutoffs.physical hR 0 x = 1}) :
    inner ℂ (complexTail hR A (imageSchwartzFamilyToLp v)) (imageSchwartzFamilyToLp v) =
      inner ℂ (imageSchwartzFamilyToLp (fun j ↦ imageBesselSchwartzCLM (adjointFactor hR A v j)))
        (imageSchwartzFamilyToLp (fun j ↦ imageBesselSchwartzCLM (adjointFactor hR A v j))) -
      inner ℂ (imageSchwartzFamilyToLp (fun j ↦ sourceMask hR (imageBesselSchwartzCLM (adjointFactor hR A v j))))
        (imageSchwartzFamilyToLp (fun j ↦ sourceMask hR (imageBesselSchwartzCLM (adjointFactor hR A v j)))) := by
  rw [complexTail_toLp]
  simp only [imageSchwartzFamilyToLp_inner]
  change (∑ i, imageSchwartzPairing
    (maskedCoefficientSchwartzCLM (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
      (fun j ↦ SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((FixedCutoffs.physical hR 0 x) ^ 2 : ℂ))
        (imageBesselSchwartzCLM (imageBesselSchwartzCLM (adjointFactor hR A v j) -
          SchwartzMap.smulLeftCLM ℂ (fun x ↦ (fixedSourceSquare hR x : ℂ))
            (imageBesselSchwartzCLM (adjointFactor hR A v j))))) i) (v i)) = _
  rw [maskedCoefficientSchwartzCLM_pairing
    (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport]
  change (∑ j, imageSchwartzPairing _ (adjointFactor hR A v j)) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact scalarTail_pairing hR _ (adjointFactor_mask_sq hR A v hv j)

end JanetCartan.ContinuumNormal.FrozenImageComparison.SourceTailTestEnergy
