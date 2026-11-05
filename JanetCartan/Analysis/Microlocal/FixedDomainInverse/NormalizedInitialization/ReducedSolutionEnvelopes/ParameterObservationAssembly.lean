module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ComplexParameterRemainder
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterRemainderDepth

/-!
# Uniform parameter remainders on the same observed inverse

The actual source-jet remainder from `inverse_remainder_product_parameter_jet`
is used at a single spatial order and a single inverse depth in every term
of the parameter Leibniz formula. The finite maximum of its constants and
the original frequency gap give the precise remainder input of
`parameter_inverse_reserved_envelope_of_finite_remainders`.

This is a deduction from the displayed source-jet remainder producer. It
does not replace the actual characteristic or full elliptic word estimates,
and it does not infer a fixed tame derivative loss from all-order profiles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Finset
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential SmallSupport
open RegularSector.Realization ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ObservedParameterRemainders

variable {n r : ℕ} {ι : Type*} {Par : Type}
  [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean n
local notation "CF" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Fixed residual powers and the same inverse preserve norm-smoothness of
the original source family under the actual demodulated observation. This
supplies both regularity inputs of the differentiated finite identity;
no smoothness of the observed solution is assumed
(`app:ch_regular:eq:finite-neumann-identity`). -/
theorem contDiffOn_demodulated_fixed_local_operator
    {U : Set E} (hU : MeasurableSet U) {x : E} (χ : ContDiffBump x)
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (S : H →L[ℂ] H) (T : LocalL2 U CF →L[ℝ] LocalL2 U CF)
    (source : Par → LocalL2 U CF) (hsource : ContDiffOn ℝ ∞ source V) :
    ContDiffOn ℝ ∞ (fun c ↦ carrierMultiplication (-ρ) (φ c) (hφc c)
      (S (zeroExtend hU (bumpL2 (p := 2) le_rfl χ (T (source c)))))) V := by
  let B : LocalL2 U CF →L[ℝ] H := (S.restrictScalars ℝ).comp
    ((zeroExtend (F := CF) (p := 2) hU).toContinuousLinearMap.comp
      ((bumpL2 (F := CF) (μ := volume.restrict U) (p := 2) le_rfl χ).comp T))
  exact (contDiffOn_demodulationOperators hV hX ρ φ hφc hφ hs).clm_apply
    (B.contDiff.comp_contDiffOn hsource)

/-- The displayed actual source-jet remainder supplies the uniform observed
remainder at the SAME depth `N+s`. Its producer is
`inverse_remainder_product_parameter_jet`, whose constant is explicit and
independent of histories, parameters, and unit directions. The observation
uses only these source jets at spatial order `s`; all parameter polynomial
costs are absorbed by the original frequency window
(`app:ch_regular:eq:finite-observation`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem observed_parameter_remainder_of_actual_source_jets
    (U : Set E) (hU : MeasurableSet U) {x : E} (χ₃ : ContDiffBump x)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (R : ι → LocalL2 U CF →L[ℂ] LocalL2 U CF) (hR : ∀ i, ‖R i‖ < 1)
    (S : ι → H →L[ℂ] H)
    (source : ι → Par → LocalL2 U CF)
    (V : Set Par) (hV : IsOpen V) (hsource : ∀ i, ContDiffOn ℝ ∞ (source i) V)
    (ρ L K A : ι → ℝ) {ν : ℝ}
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hν : 0 < ν) (hwindow : ∀ i, K i ≤ (ρ i)^(1-ν)) (hA : ∀ i, 0 ≤ A i)
    (φ : ι → Par → E → ℝ) (hφc : ∀ i c, Continuous (φ i c))
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ univ))
    {X : Set E} (hX : IsCompact X) (hsφ : ∀ i c, c ∈ V → tsupport (φ i c) ⊆ X)
    (P Csolver Ccoefficient : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hCsolver : ∀ s, 0 ≤ Csolver s)
    (hCcoefficient : ∀ s, 0 ≤ Ccoefficient s)
    (hphase : ∀ i c, c ∈ V → ∀ y ∈ X, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) (c,y)‖ ≤ P j * K i ^ j)
    (high : ι → ℕ → ℝ) (hhigh : ∀ i s, 0 ≤ high i s)
    (hcoefficient : ∀ i s, 1 + high i s ≤ Ccoefficient s * L i ^ s)
    (hsolver : ∀ i (s : ℕ) (z : H), MemVectorFourierSobolev (s : ℝ) z →
      MemVectorFourierSobolev (s : ℝ) (S i z) ∧
        vectorFourierSobolevNorm (s : ℝ) (S i z) ≤
          Csolver s * (vectorFourierSobolevNorm (s : ℝ) z + high i s * ‖z‖))
    (CP : ℕ → ℕ → ℕ → ℝ)
    (hpower : ∀ i N s k c, c ∈ V →
      ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
        let u := fun q ↦ complexNeumannInverse (R i) (hR i)
          (((R i)^(N+s)) (source i q))
        let jet := iteratedFDeriv ℝ k u c v
        MemRestrictionSobolev U s jet ∧ restrictionSobolevNorm U s jet ≤
          CP N s k * (A i * ρ i ^ k * K i ^ (k+n+1)) * L i ^ s * (L i / ρ i)^N) :
    ∀ s k, ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
        let u := fun q ↦ complexNeumannInverse (R i) (hR i)
          (((R i)^(N+s)) (source i q))
        let observed := fun q ↦ carrierMultiplication (-(ρ i)) (φ i q) (hφc i q)
          (S i (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃ (u q))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k observed c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k observed c v) ≤ D * A i := by
  intro s k
  obtain ⟨Dobs, hDobs, hobs⟩ :=
    exists_parameter_demodulated_bumped_solver_fourier_cost (r := r) (Par := Par) χ₃ P hP s k
  obtain ⟨N, _hN, hdepth⟩ := exists_observed_parameter_remainder_depth hν n s k
  let Csum := ∑ j ∈ range (k+1), |CP N s j|
  have hCsum : 0 ≤ Csum := sum_nonneg (fun _ _ ↦ abs_nonneg _)
  let D := Dobs * Csolver s * Ccoefficient s * Csum
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (mul_nonneg hDobs (hCsolver s)) (hCcoefficient s)) hCsum
  refine ⟨N, D, hD, ?_⟩
  intro i c hc v hv u observed
  have hKi : 1 ≤ K i := (hL i).trans (hLK i)
  have hL0 := zero_le_one.trans (hL i)
  have hK0 := zero_le_one.trans hKi
  have hρ0 := zero_le_one.trans (hρ i)
  have hAi := hA i
  let B := Csum * (A i * ρ i ^ k * K i ^ (k+n+1)) * L i ^ s * (L i / ρ i)^N
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let T : LocalL2 U CF →L[ℝ] LocalL2 U CF :=
    (((complexNeumannInverse (R i) (hR i)).comp ((R i)^(N+s))).restrictScalars ℝ)
  have hu : ContDiffOn ℝ ∞ u V := T.contDiff.comp_contDiffOn (hsource i)
  have hjets (vs : List Par) (hlen : vs.length ≤ k) (hvs : ∀ a ∈ vs, ‖a‖ ≤ 1) :
      MemRestrictionSobolev U s (parameterListJet u vs c) ∧
        restrictionSobolevNorm U s (parameterListJet u vs c) ≤ B := by
    obtain ⟨hm, hb⟩ := hpower i N s vs.length c hc vs.get
      (fun j ↦ hvs _ (List.get_mem ..))
    refine ⟨hm, hb.trans ?_⟩
    have hC : CP N s vs.length ≤ Csum := (le_abs_self _).trans
      (single_le_sum (fun j _ ↦ abs_nonneg (CP N s j))
        (mem_range.mpr (Nat.lt_succ_of_le hlen)))
    have hsize : A i * ρ i ^ vs.length * K i ^ (vs.length+n+1) ≤
        A i * ρ i ^ k * K i ^ (k+n+1) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hρ i) hlen) (hA i))
        (pow_le_pow_right₀ hKi (by omega)) (pow_nonneg hK0 _)
        (mul_nonneg (hA i) (pow_nonneg hρ0 _))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hC hsize (by positivity) hCsum) (pow_nonneg hL0 _))
      (pow_nonneg (div_nonneg hL0 hρ0) _)
  obtain ⟨hm, hb⟩ := hobs U hU hχ₃ hV hX (ρ i) (K i) (hρ i) hKi
    (φ i) (hφc i) (hφ i) (hsφ i) (S i) (Csolver s) (high i s)
    (hCsolver s) (hhigh i s) (hsolver i s) u hu c hc
    (fun y hy j hj _ ↦ hphase i c hc y hy j hj) v hv B hB hjets
  refine ⟨hm, hb.trans ?_⟩
  calc
    _ ≤ (Dobs * Csolver s * (Ccoefficient s * L i ^ s)) *
        ρ i ^ (k+2*s) * K i ^ (k+s) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcoefficient i s)
              (mul_nonneg hDobs (hCsolver s))) (pow_nonneg hρ0 _))
          (pow_nonneg hK0 _)) hB
    _ = D * ρ i ^ (k+2*s) * K i ^ (k+s) *
        (A i * ρ i ^ k * K i ^ (k+n+1) * L i ^ s * (L i / ρ i)^N) * L i ^ s := by
      dsimp only [D, B]
      ac_rfl
    _ ≤ D * A i := hdepth (hρ i) hL0 (hLK i) (hwindow i) (hA i) hD

end JanetCartan.FixedDomainInverse
