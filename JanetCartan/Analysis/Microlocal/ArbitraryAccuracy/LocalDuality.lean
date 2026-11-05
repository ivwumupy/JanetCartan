module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.PhysicalComponents
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Remainder
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.LocalL2

/-!
# Concrete local negative pairing and the remaining inverse

The imported pairing is unconditional on actual local L² and restriction
Sobolev classes, with genuine weak extensions and the infimum restriction norm.
The physical-frequency leaf retains the fixed `2π` convention and its Jacobian.

The inverse remainder below instantiates `app:ch_regular:eq:inverse-remainder`
on this actual scale. Its remaining inputs are the contraction of the complete
residual, one-gain regularity and estimates for it and its literal adjoint, the
coefficient profile, and a bound on the original source's negative Fourier norm.
The regular-sector, fixed-domain-inverse, and response-transfer constructions
must supply these inputs. No pairing estimate is assumed, and this conditional
inverse theorem does not establish the original unconditional existence theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy

open LocalSobolev

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]

/-- The remaining inverse bound `app:ch_regular:eq:inverse-remainder` on the
actual local restriction scale. The source assumption is only its zero-extended
negative Fourier norm. Local duality is proved from weak extensions, and the
adjoint is the literal Hilbert adjoint. The complete operator and all domains
stay fixed as `N` and `s` vary. The analytic inputs must be instantiated by the
regular-sector, fixed-domain-inverse, and response-transfer producers. -/
theorem inverse_remainder_restrictionSobolev
    (basis : OrthonormalBasis ι ℝ F) {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : MeasurableSet W) (K : LocalL2 W F →L[ℝ] LocalL2 W F)
    {C C' D a : ℕ → ℝ} {b : ℕ} {θ L ρ A CN : ℝ}
    (hK : ‖K‖ ≤ θ) (hθ : θ < 1) (hL : 1 ≤ L) (hρ : 0 < ρ)
    (hA : 0 ≤ A) (hCN : 0 ≤ CN)
    (hC : ∀ j, 0 ≤ C j) (hC' : ∀ j, 0 ≤ C' j) (hD : ∀ j, 0 ≤ D j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hprofile : ∀ j, 1 + a (j + b) ≤ D j * L ^ j)
    (hreg : ∀ j f, MemRestrictionSobolev W j f →
      MemRestrictionSobolev W (j + 1) (K f))
    (hgain : ∀ j f, MemRestrictionSobolev W j f →
      restrictionSobolevNorm W (j + 1) (K f) ≤
        C (j + 1) * (restrictionSobolevNorm W j f + (1 + a (j + 1 + b)) * ‖f‖))
    (hreg' : ∀ j f, MemRestrictionSobolev W j f →
      MemRestrictionSobolev W (j + 1) (K.adjoint f))
    (hgain' : ∀ j f, MemRestrictionSobolev W j f →
      restrictionSobolevNorm W (j + 1) (K.adjoint f) ≤
        C' (j + 1) * (restrictionSobolevNorm W j f + (1 + a (j + 1 + b)) * ‖f‖))
    (N s : ℕ) (h : LocalL2 W F)
    (hsource : componentFourierSobolevNorm basis (-(N : ℝ))
      (SmallSupport.zeroExtend hW h) ≤ CN * A / ρ ^ N) :
    MemRestrictionSobolev W s (neumannInverse K ((K ^ (N + s)) h)) ∧
    restrictionSobolevNorm W s (neumannInverse K ((K ^ (N + s)) h)) ≤
      (inverseTameConstant θ C s * (powerGainConstant C D s + D s) *
        ((localDualityConstant n N basis * CN) * powerGainConstant C' D N)) *
          A * L ^ s * (L / ρ) ^ N := by
  have hdual (v : LocalL2 W F) (hv : MemRestrictionSobolev W N v) :
      |inner ℝ h v| ≤ ((localDualityConstant n N basis * CN) * A / ρ ^ N) *
        (restrictionSobolevScale W F hW).gradeNorm N v := by
    rw [restrictionSobolevScale_gradeNorm hW hv]
    apply (abs_inner_le_negativeNorm_mul_restrictionSobolevNorm basis hW N h v hv).trans
    calc
      _ ≤ (localDualityConstant n N basis * (CN * A / ρ ^ N)) *
          restrictionSobolevNorm W N v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsource (localDualityConstant_pos n N basis).le)
          restrictionSobolevNorm_nonneg
      _ = _ := by ring
  obtain ⟨hmem, hbound⟩ := inverse_remainder_of_one_gain_and_duality
    (restrictionSobolevScale W F hW) (restrictionSobolevScale W F hW) K
    hK hθ hL hρ hA (mul_nonneg (localDualityConstant_pos n N basis).le hCN)
    hC hC' hD ha ham hprofile
    (FixedDomainInverse.restrictionSobolev_hasOneGain hW K C a b hreg hgain)
    (FixedDomainInverse.restrictionSobolev_hasOneGain hW K.adjoint C' a b hreg' hgain')
    N s h hdual
  exact ⟨hmem, by simpa only [restrictionSobolevScale_gradeNorm hW hmem] using hbound⟩

end JanetCartan.ArbitraryAccuracy
