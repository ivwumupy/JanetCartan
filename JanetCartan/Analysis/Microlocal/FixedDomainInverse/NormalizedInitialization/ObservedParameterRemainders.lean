module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.Sobolev
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.Leibniz
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.Totalization
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Observation

/-!
# The actual parameter derivatives of the observed inverse remainder

Apply the finite Leibniz formula to the original demodulation, fixed complete
solver and fixed bumped zero extension. Every inverse-source parameter jet
is used at the single target spatial order `s`. Its depth is therefore the
same `N+s` for all terms. Primitive compact-phase derivatives supply the
multiplier costs; there is no derivative-observation estimate among the inputs.

The source-family input is produced by
`iteratedFDeriv_fixed_inverse_real_source_of_eq` and
`inverse_remainder_actual_parameter_source_quadrature`, or their actual complex
product-parameter variants. The consumer is the differentiated finite Neumann
assembly in `app:ch_regular:eq:finite-neumann-identity` and
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential SmallSupport
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open ArbitraryAccuracy.ResidualLocalization
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open ObservedParameterRemainders

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem list_vectorFourier_bound {κ : Type*} (s : ℕ) (l : List κ)
    (g : κ → H) {B : ℝ}
    (hg : ∀ i ∈ l, MemVectorFourierSobolev (s : ℝ) (g i) ∧
      vectorFourierSobolevNorm (s : ℝ) (g i) ≤ B) :
    MemVectorFourierSobolev (s : ℝ) ((l.map g).sum) ∧
      vectorFourierSobolevNorm (s : ℝ) ((l.map g).sum) ≤ (l.length : ℝ) * B := by
  induction l with
  | nil =>
    have he := norm_vectorWeightedFourier (s : ℝ)
      (0 : vectorFourierSobolevLevel (d := n) (I := Fin r) (s : ℝ))
    simp only [map_zero, norm_zero, ZeroMemClass.coe_zero] at he
    exact ⟨(vectorFourierSobolevLevel (d := n) (I := Fin r) (s : ℝ)).zero_mem,
      by simpa only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_mul]
        using le_of_eq he.symm⟩
  | cons i l ih =>
    obtain ⟨hm, hb⟩ := hg i (List.mem_cons_self ..)
    obtain ⟨hsm, hsb⟩ := ih (fun j hj ↦ hg j (List.mem_cons_of_mem i hj))
    obtain ⟨hadd, hbadd⟩ := TerminalBounds.add_bound hm hsm
    refine ⟨hadd, hbadd.trans ((add_le_add hb hsb).trans_eq ?_)⟩
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]

/-- The actual ordered parameter derivative of the same demodulated solver
observation has a polynomial cost using only source jets at spatial order `s`.
The constant precedes the domain, phase, frequency, solver and inverse-source
family. Taking `u(c)=Inv(R^(N+s)h_c)` preserves one common inverse depth for
every Leibniz term. The original complex source is retained throughout
(`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_parameter_demodulated_bumped_solver_fourier_cost
    {x : E} (χ : ContDiffBump x) (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U →
      ∀ {V : Set Par}, IsOpen V → ∀ {X : Set E}, IsCompact X →
      ∀ (ρ K : ℝ), 1 ≤ ρ → 1 ≤ K →
      ∀ (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c)),
        ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ) →
        (∀ c ∈ V, tsupport (φ c) ⊆ X) →
      ∀ (T : H →L[ℂ] H) (C high : ℝ), 0 ≤ C → 0 ≤ high →
        (∀ z : H, MemVectorFourierSobolev (s : ℝ) z →
          MemVectorFourierSobolev (s : ℝ) (T z) ∧
            vectorFourierSobolevNorm (s : ℝ) (T z) ≤
              C * (vectorFourierSobolevNorm (s : ℝ) z + high * ‖z‖)) →
      ∀ (u : Par → LocalL2 U F), ContDiffOn ℝ ∞ u V →
      ∀ c ∈ V,
        (∀ y ∈ X, ∀ j, 1 ≤ j → j ≤ s + k →
          ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c, y)‖ ≤ P j * K ^ j) →
      ∀ (v : Fin k → Par), (∀ i, ‖v i‖ ≤ 1) →
      ∀ (B : ℝ), 0 ≤ B →
        (∀ vs : List Par, vs.length ≤ k → (∀ a ∈ vs, ‖a‖ ≤ 1) →
          MemRestrictionSobolev U s (parameterListJet u vs c) ∧
            restrictionSobolevNorm U s (parameterListJet u vs c) ≤ B) →
        let observation := fun a ↦ carrierMultiplication (-ρ) (φ a) (hφc a)
          (T (zeroExtend hU (bumpL2 (p := 2) le_rfl χ (u a))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k observation c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k observation c v) ≤
            (D * C * (1 + high)) * ρ ^ (k + 2 * s) * K ^ (k + s) * B := by
  obtain ⟨Dphase, hDphase, hphaseCost⟩ :=
    exists_demodulation_parameterJet_fourier_cost (r := r) (Par := Par) P hP s k
  obtain ⟨Dbump, hDbump, hbump⟩ := exists_bump_zeroExtension_fourier_constant (r := r) χ s
  let D := (2 : ℝ) ^ k * Dphase * Dbump
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro U hU hχ V hV X hX ρ K hρ hK φ hφc hφ hs T C high hC hhigh hT
    u hu c hc hphase v hv B hB hsource observation
  let S : LocalL2 U F →L[ℝ] H :=
    (T.restrictScalars ℝ).comp
      ((zeroExtend hU).toContinuousLinearMap.comp
        (bumpL2 (μ := volume.restrict U) (p := 2) le_rfl χ))
  have hS (vs : List Par) (hlen : vs.length ≤ k) (hvs : ∀ a ∈ vs, ‖a‖ ≤ 1) :
      MemVectorFourierSobolev (s : ℝ) (S (parameterListJet u vs c)) ∧
        vectorFourierSobolevNorm (s : ℝ) (S (parameterListJet u vs c)) ≤
          C * (1 + high) * Dbump * B := by
    obtain ⟨hsm, hsb⟩ := hsource vs hlen hvs
    obtain ⟨hzm, hzb⟩ := hbump U hU hχ (parameterListJet u vs c) hsm
    let z := zeroExtend hU (bumpL2 (p := 2) le_rfl χ (parameterListJet u vs c))
    have hzL2 : ‖z‖ ≤ vectorFourierSobolevNorm (s : ℝ) z := by
      simpa only [vectorFourierSobolevNorm_zero] using
        vectorFourierSobolevNorm_mono hzm (show (0 : ℝ) ≤ s by positivity)
    obtain ⟨hTm, hTb⟩ := hT z hzm
    refine ⟨hTm, hTb.trans ?_⟩
    have hz : vectorFourierSobolevNorm (s : ℝ) z ≤ Dbump * B :=
      hzb.trans (mul_le_mul_of_nonneg_left hsb hDbump.le)
    calc
      _ ≤ C * (Dbump * B + high * (Dbump * B)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hz (mul_le_mul_of_nonneg_left (hzL2.trans hz) hhigh)) hC
      _ = _ := by ring
  have he := iteratedFDeriv_demodulated_fixed_operator_eq_leibniz
    hV hX ρ φ hφc hφ hs S u hu k v hc
  let term := fun t : List Par × List Par ↦ parameterListJet
    (fun a ↦ (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ)
      t.1 c (S (parameterListJet u t.2 c))
  have hterms (t : List Par × List Par)
      (ht : t ∈ parameterLeibnizSplittings (List.ofFn v)) :
      MemVectorFourierSobolev (s : ℝ) (term t) ∧
        vectorFourierSobolevNorm (s : ℝ) (term t) ≤
          (Dphase * C * (1 + high) * Dbump) * ρ ^ (s+k) * K ^ (s+k) * B := by
    have horder := parameterLeibnizSplittings_orders ht
    rw [List.length_ofFn] at horder
    have hdirs := parameterLeibnizSplittings_unit (by simpa using hv) ht
    obtain ⟨hsm, hsb⟩ := hS t.2 (by omega) hdirs.2
    obtain ⟨hm, hb⟩ := hphaseCost hV hX ρ K hρ hK φ hφc hφ hs c hc hphase
      t.1 (by omega) hdirs.1 (S (parameterListJet u t.2 c)) hsm
    refine ⟨hm, hb.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left hsb
      (by positivity : 0 ≤ Dphase * ρ ^ (s+k) * K ^ (s+k))).trans_eq (by ring)
  obtain ⟨hmem, hbound⟩ := list_vectorFourier_bound s
    (parameterLeibnizSplittings (List.ofFn v)) term hterms
  change iteratedFDeriv ℝ k observation c v =
    ((parameterLeibnizSplittings (List.ofFn v)).map term).sum at he
  rw [he]
  refine ⟨hmem, hbound.trans ?_⟩
  rw [length_parameterLeibnizSplittings, List.length_ofFn, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = (D * C * (1 + high)) * ρ ^ (s+k) * K ^ (k+s) * B := by
      dsimp [D]
      rw [Nat.add_comm s k]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ (by omega))
          (by positivity : 0 ≤ D * C * (1 + high)))
        (pow_nonneg (zero_le_one.trans hK) _)) hB

end JanetCartan.FixedDomainInverse
