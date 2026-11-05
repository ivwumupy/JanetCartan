module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.CarrierCoefficients
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Estimates

/-!
# One spatial Sobolev order for every observation coefficient

Compact coefficient multiplication bounds each term of the actual finite
parameter Leibniz formula on precisely `H^s`. The original phase supplies
the coefficient derivatives through `s+k`; no source or output norm above
order `s` is used (`app:ch_regular:eq:inverse-remainder`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ObservedParameterRemainders

open Pseudodifferential IsometricEmbedding.Reconstruction
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem compact_coefficient_fourier_bound (s : ℕ)
    (a : E → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ j ≤ s, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ C)
    (u v : H) (hv : v =ᵐ[volume] fun x ↦ a x • u x)
    (hu : MemVectorFourierSobolev (s : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) v ∧
      vectorFourierSobolevNorm (s : ℝ) v ≤
        (localizedMultiplierConstant n s * (s + 1) * C) *
          vectorFourierSobolevNorm (s : ℝ) u := by
  have he (i : Fin r) : finiteL2CoordinateIsometry volume v i =
      localizedScalarProduct a ha hca (finiteL2CoordinateIsometry volume u i) := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume v i,
      finiteL2Coordinates_apply_ae volume u i, hv,
      localizedScalarProduct_ae a ha hca (finiteL2CoordinateIsometry volume u i)]
      with x hvx hux hvx' hax
    change (finiteL2CoordinateIsometry volume v i : E → ℂ) x = v x i at hvx
    change (finiteL2CoordinateIsometry volume u i : E → ℂ) x = u x i at hux
    rw [hvx, hvx', PiLp.smul_apply, smul_eq_mul, hax, hux]
  have hp (i : Fin r) := localizedScalarProduct_frechet_bound s a ha hca
    (fun _ ↦ C) (fun _ ↦ hC) hjet (finiteL2CoordinateIsometry volume u i) (hu i)
  have hm : MemVectorFourierSobolev (s : ℝ) v := by
    intro i
    rw [he i]
    exact (hp i).1
  refine ⟨hm, vectorFourierSobolevNorm_le_of_coordinate_bounds
    (by positivity [localizedMultiplierConstant_pos n s]) v u ?_⟩
  intro i
  rw [he i]
  apply (hp i).2.trans
  unfold mixedAmplitudeSobolevSum
  calc
    _ ≤ localizedMultiplierConstant n s *
        ∑ j ∈ Finset.range (s + 1),
          C * fourierSobolevNorm (s : ℝ) (finiteL2CoordinateIsometry volume u i) := by
      apply mul_le_mul_of_nonneg_left _ (localizedMultiplierConstant_pos n s).le
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (fourierSobolevNorm_mono (hu i)
          (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]

private theorem parameterListJet_defect_eq_of_nonempty
    {V : Set Par} (hV : IsOpen V) {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (ρ : ℝ) {vs : List Par} (hvs : vs ≠ []) {c : Par} (hc : c ∈ V) (x : E) :
    parameterListJet (fun a ↦ demodulationDefect ρ φ a x) vs c =
      parameterListJet (fun a ↦ carrier (-ρ) (φ a) x) vs c := by
  have hp : ContDiffAt ℝ ∞ (fun a ↦ φ a x) c :=
    (hφ.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).comp c
      (contDiffAt_id.prodMk contDiffAt_const)
  have hcarrier : ContDiffAt ℝ ∞ (fun a ↦ carrier (-ρ) (φ a) x) c := by
    unfold carrier
    exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp c
      (contDiffAt_const.mul hp))).cexp
  unfold parameterListJet
  change iteratedFDeriv ℝ vs.length
    ((fun a ↦ carrier (-ρ) (φ a) x) - fun _ ↦ (1 : ℂ)) c vs.get = _
  rw [iteratedFDeriv_sub_apply (hcarrier.of_le (by simp)) contDiffAt_const]
  have hlen : vs.length ≠ 0 := by
    intro hz
    exact hvs (List.length_eq_zero_iff.mp hz)
  simp only [iteratedFDeriv_const_of_ne hlen, Pi.zero_apply, sub_zero]

/-- Actual parameter derivatives of demodulation act on the SAME Sobolev
order. The cost is polynomial in frequency and phase scale and is fixed
before the phase, domain, source and direction list. In particular, this
estimate can be used for every source derivative at one fixed inverse depth
(`app:ch_regular:eq:inverse-remainder`). -/
theorem exists_demodulation_parameterJet_fourier_cost
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {V : Set Par}, IsOpen V →
      ∀ {X : Set E}, IsCompact X → ∀ (ρ K : ℝ), 1 ≤ ρ → 1 ≤ K →
      ∀ (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c)),
        ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ) →
        (∀ c ∈ V, tsupport (φ c) ⊆ X) →
      ∀ c ∈ V,
        (∀ x ∈ X, ∀ j, 1 ≤ j → j ≤ s + k →
          ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c, x)‖ ≤ P j * K ^ j) →
      ∀ vs : List Par, vs.length ≤ k → (∀ v ∈ vs, ‖v‖ ≤ 1) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        let w := parameterListJet
          (fun a ↦ (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ)
          vs c u
        MemVectorFourierSobolev (s : ℝ) w ∧
          vectorFourierSobolevNorm (s : ℝ) w ≤
            D * ρ ^ (s + k) * K ^ (s + k) * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, hcoefficient⟩ := exists_demodulationDefect_parameterJet_bound (Par := Par) P hP s k
  let D₀ := localizedMultiplierConstant n s * (s + 1) * C
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity [localizedMultiplierConstant_pos n s]
  refine ⟨D₀ + 1, by positivity, ?_⟩
  intro V hV X hX ρ K hρ hK φ hφc hφ hs c hc hphase vs hlen hv u hu w
  let a := fun x ↦ parameterListJet (fun b ↦ demodulationDefect ρ φ b x) vs c
  have hreg := demodulationDefect_parameterJet_regular_support hV hX ρ hφ hs vs hc
  have hca : HasCompactSupport a := hX.of_isClosed_subset (isClosed_tsupport _) hreg.2
  have hjet := hcoefficient hV hX ρ K hρ hK φ hφ hs c hc hphase vs hlen hv
  have hscale : 0 ≤ C * ρ ^ (s + k) * K ^ (s + k) := by positivity
  have hnorm : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u := norm_nonneg _
  have hpow : 1 ≤ ρ ^ (s + k) * K ^ (s + k) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hρ) (one_le_pow₀ hK)
  by_cases hvs : vs = []
  · subst vs
    let z := carrierMultiplication (-ρ) (φ c) (hφc c) u
    have hw : w = z := by simp only [w, parameterListJet, List.length_nil,
      iteratedFDeriv_zero_apply, ContinuousLinearMap.coe_restrictScalars']; rfl
    have he : z - u =ᵐ[volume] fun x ↦ a x • u x := by
      filter_upwards [carrierMultiplication_ae (-ρ) (φ c) (hφc c) u,
        Lp.coeFn_sub z u] with x hz hx
      rw [hx, Pi.sub_apply]
      change z x - u x = a x • u x
      rw [hz]
      simp only [a, parameterListJet, List.length_nil, iteratedFDeriv_zero_apply,
        demodulationDefect, sub_smul, one_smul]
    obtain ⟨hmul, hbound⟩ := compact_coefficient_fourier_bound s a hreg.1 hca hscale hjet u (z-u) he hu
    obtain ⟨hzmem, hzbound⟩ := TerminalBounds.add_bound hmul hu
    rw [sub_add_cancel] at hzmem hzbound
    rw [hw]
    refine ⟨hzmem, hzbound.trans ((add_le_add hbound le_rfl).trans ?_)⟩
    calc
      _ ≤ (localizedMultiplierConstant n s * (s + 1) *
          (C * ρ ^ (s + k) * K ^ (s + k))) * vectorFourierSobolevNorm (s : ℝ) u +
            (ρ ^ (s+k) * K ^ (s+k)) * vectorFourierSobolevNorm (s : ℝ) u :=
        add_le_add le_rfl (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow hnorm)
      _ = _ := by dsimp [D₀]; ring
  · have he : w =ᵐ[volume] fun x ↦ a x • u x := by
      filter_upwards [parameterListJet_demodulationOperators_ae hV hX ρ φ hφc hφ hs vs hc u]
        with x hx
      rw [hx, ← parameterListJet_defect_eq_of_nonempty hV hφ ρ hvs hc x]
    obtain ⟨hmul, hbound⟩ := compact_coefficient_fourier_bound s a hreg.1 hca hscale hjet u w he hu
    refine ⟨hmul, hbound.trans ?_⟩
    calc
      _ = D₀ * ρ ^ (s+k) * K ^ (s+k) * vectorFourierSobolevNorm (s : ℝ) u := by
        dsimp [D₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (pow_nonneg (zero_le_one.trans hρ) _))
          (pow_nonneg (zero_le_one.trans hK) _)) hnorm

end JanetCartan.FixedDomainInverse.ObservedParameterRemainders
