module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ComplexInverse
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps

/-!
# The original real inverse remainders on the combined complex source

The initialized inverse estimates both real quadratures, with the same depth,
Sobolev order, and source/coefficient scales. This file recombines those exact
remainders on the same complex Neumann series. Only a fixed numerical factor
is spent; the original derivative reserve and the factors `τ³ L^s (Lτ)^N`
are preserved. This is the complex remainder input of
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev RegularSector RegularSector.Realization
open ArbitraryAccuracy.ResidualLocalization

variable {n r : ℕ} {U : Set (Euclidean n)}
local notation "RF" => EuclideanSpace ℝ (Fin r)
local notation "CF" => EuclideanSpace ℂ (Fin r)
local notation "RH" => LocalL2 U RF
local notation "CH" => LocalL2 U CF

private theorem restrictionSobolev_quadratures_bound
    (s : ℕ) {f g : RH} (hf : MemRestrictionSobolev U s f)
    (hg : MemRestrictionSobolev U s g) {A : ℝ}
    (hfb : restrictionSobolevNorm U s f ≤ A)
    (hgb : restrictionSobolevNorm U s g ≤ A) :
    MemRestrictionSobolev U s
        (l2ComplexInclusion (volume.restrict U) f +
          Complex.I • l2ComplexInclusion (volume.restrict U) g) ∧
      restrictionSobolevNorm U s
        (l2ComplexInclusion (volume.restrict U) f +
          Complex.I • l2ComplexInclusion (volume.restrict U) g) ≤ 6 * A := by
  let inc := euclideanComplexInclusion (ι := Fin r)
  let mulI := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] CF →L[ℝ] CF) Complex.I
  have hmulI : ‖mulI‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp only [mulI, ContinuousLinearMap.lsmul_apply, norm_smul, Complex.norm_I, one_mul]
    exact le_rfl
  have he (v : CH) : mulI.compLp v = Complex.I • v := by
    apply Lp.ext
    filter_upwards [mulI.coeFn_compLp v, Lp.coeFn_smul Complex.I v] with x hx hy
    rw [hx, hy]
    rfl
  obtain ⟨hfm, hfn⟩ := compLp_restrictionSobolev_bound inc hf
  obtain ⟨hgm, hgn⟩ := compLp_restrictionSobolev_bound inc hg
  have hinc : ‖inc‖ ≤ 1 := euclideanComplexInclusion_norm_le
  have hinc1 : ‖inc‖ + 1 ≤ 2 := by linarith
  have hmulI1 : ‖mulI‖ + 1 ≤ 2 := by linarith
  have hfbound : restrictionSobolevNorm U s (inc.compLp f) ≤ 2 * A := by
    apply hfn.trans
    exact mul_le_mul hinc1 hfb restrictionSobolevNorm_nonneg (by norm_num)
  have hgbound : restrictionSobolevNorm U s (inc.compLp g) ≤ 2 * A := by
    apply hgn.trans
    exact mul_le_mul hinc1 hgb restrictionSobolevNorm_nonneg (by norm_num)
  obtain ⟨higm, hign⟩ := compLp_restrictionSobolev_bound mulI hgm
  rw [he] at higm hign
  have hibound : restrictionSobolevNorm U s (Complex.I • inc.compLp g) ≤ 4 * A := by
    apply hign.trans
    calc
      _ ≤ 2 * (2 * A) := mul_le_mul hmulI1 hgbound
        restrictionSobolevNorm_nonneg (by norm_num)
      _ = _ := by ring
  refine ⟨hfm.add higm, (restrictionSobolevNorm_add_le hfm higm).trans ?_⟩
  exact (add_le_add hfbound hibound).trans_eq (by ring)

/-- Convert the same real Neumann-series remainder bounds to the full complex
source. The two physical source quadratures are combined before any primary
demodulation. For the normalized initializer take `depth = N+s` and
`A = C_N τ³ L^s (Lτ)^N`, exactly as returned by its original source remainder
producer; neither `s`, `N`, nor its derivative reserve is increased
(`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem complex_inverse_power_remainder_of_real_quadratures
    (K : CH →L[ℂ] CH)
    (hreal : conjugateOperator K.toLinearMap = K.toLinearMap) (hK : ‖K‖ < 1)
    (s depth : ℕ) (f g : RH)
    (hf : MemRestrictionSobolev U s
      (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) f)))
    (hg : MemRestrictionSobolev U s
      (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) g)))
    {A : ℝ}
    (hfb : restrictionSobolevNorm U s
      (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) f)) ≤ A)
    (hgb : restrictionSobolevNorm U s
      (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) g)) ≤ A) :
    let source := l2ComplexInclusion (volume.restrict U) f +
      Complex.I • l2ComplexInclusion (volume.restrict U) g
    let remainder := complexNeumannInverse K hK ((K^depth) source)
    MemRestrictionSobolev U s remainder ∧ restrictionSobolevNorm U s remainder ≤ 6 * A := by
  intro source remainder
  have hpow (j : ℕ) (u : RH) :
      (K ^ j) (l2ComplexInclusion (volume.restrict U) u) =
        l2ComplexInclusion (volume.restrict U) (((realOutputCompression K)^j) u) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ']
      change K ((K^j) (l2ComplexInclusion (volume.restrict U) u)) = _
      rw [ih, ← inclusion_realCompression K hreal]
      rfl
  have he : remainder =
      l2ComplexInclusion (volume.restrict U)
        (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) f)) +
      Complex.I • l2ComplexInclusion (volume.restrict U)
        (neumannInverse (realOutputCompression K) (((realOutputCompression K)^depth) g)) := by
    have hsourcePower : (K ^ depth) source =
        l2ComplexInclusion (volume.restrict U) (((realOutputCompression K)^depth) f) +
        Complex.I • l2ComplexInclusion (volume.restrict U)
          (((realOutputCompression K)^depth) g) := by
      change (K ^ depth)
        (l2ComplexInclusion (volume.restrict U) f +
          Complex.I • l2ComplexInclusion (volume.restrict U) g) = _
      exact ((K ^ depth).map_add _ _).trans
        (congrArg₂ (· + ·) (hpow depth f)
          (((K ^ depth).map_smul Complex.I _).trans
            (congrArg (Complex.I • ·) (hpow depth g))))
    change complexNeumannInverse K hK ((K ^ depth) source) = _
    exact (congrArg (complexNeumannInverse K hK) hsourcePower).trans
      (neumannInverse_quadratures K hreal hK _ _)
  rw [he]
  exact restrictionSobolev_quadratures_bound s hf hg hfb hgb

end JanetCartan.FixedDomainInverse
