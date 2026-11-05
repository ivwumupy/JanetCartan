module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.CompactMultiplier
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.GradedAtoms

/-!
# Primitive bounds for the finite observation coefficients

Only the phase receives spatial derivatives in the observation multiplier.
Its mixed derivatives through `s+k` bound every coefficient in the finite
parameter Leibniz formula. No additional spatial order is required of the
inverse remainder (`app:ch_regular:eq:inverse-remainder`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ObservedParameterRemainders

open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles

variable {n : ℕ} {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean n

/-- The compact scalar defect of the original demodulation multiplier,
before taking any parameter derivative (`app:ch_regular:eq:inverse-remainder`). -/
def demodulationDefect (ρ : ℝ) (φ : Par → E → ℝ) : Par → E → ℂ :=
  fun c x ↦ carrier (-ρ) (φ c) x - 1

/-- Joint regularity of the actual carrier defect follows from the original
phase (`app:ch_response:eq:response-graded-reduced`). -/
theorem contDiffOn_demodulationDefect {V : Set Par} (ρ : ℝ)
    {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (demodulationDefect ρ φ)) (V ×ˢ univ) := by
  unfold demodulationDefect carrier Function.uncurry
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul hφ))).cexp).sub contDiffOn_const

/-- Every actual parameter coefficient remains supported in the same compact
phase support. This supplies the compact multiplier theorem at the single
target spatial order (`app:ch_regular:eq:inverse-remainder`). -/
theorem demodulationDefect_parameterJet_regular_support
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (vs : List Par) {c : Par} (hc : c ∈ V) :
    ContDiff ℝ ∞ (fun x ↦ parameterListJet (fun a ↦ demodulationDefect ρ φ a x) vs c) ∧
      tsupport (fun x ↦ parameterListJet (fun a ↦ demodulationDefect ρ φ a x) vs c) ⊆ X := by
  have hd := contDiffOn_demodulationDefect ρ hφ
  have hj := contDiffOn_parameterListJet_joint hV isOpen_univ hd vs
  refine ⟨contDiffOn_univ.mp
    (hj.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ ↦ ⟨hc, mem_univ _⟩)), ?_⟩
  apply closure_minimal ?_ hX.isClosed
  intro x hx
  by_contra hxX
  apply hx
  have he : (fun a ↦ demodulationDefect ρ φ a x) =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hV.mem_nhds hc] with a ha
    have hz : φ a x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxX (hs a ha h))
    simp [demodulationDefect, carrier, hz]
  unfold parameterListJet
  change iteratedFDeriv ℝ vs.length (fun a ↦ demodulationDefect ρ φ a x) c vs.get = 0
  rw [(he.iteratedFDeriv ℝ vs.length).eq_of_nhds]
  cases vs <;> simp

private theorem norm_joint_demodulationDefect_le
    {V : Set Par} (hV : IsOpen V) {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {ρ K : ℝ} (hρ : 1 ≤ ρ) (hK : 1 ≤ K)
    (m : ℕ) {c : Par} (hc : c ∈ V) (x : E)
    (hphase : ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c, x)‖ ≤ P j * K ^ j) :
    ‖iteratedFDeriv ℝ m (Function.uncurry (demodulationDefect ρ φ)) (c, x)‖ ≤
      (2 + RawPrimary.phaseJetConstant P m * 2 ^ m) * ρ ^ m * K ^ m := by
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hφat : ContDiffAt ℝ ∞ (Function.uncurry φ) (c, x) :=
    hφ.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)
  have hscaled := hφat.const_smul (-ρ)
  have hb (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j ((-ρ) • Function.uncurry φ) (c, x)‖ ≤
        P j * (ρ * K) * K ^ (j - 1) := by
    rw [iteratedFDeriv_const_smul_apply (hφat.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hρ0]
    apply (mul_le_mul_of_nonneg_left (hphase j hj hjm) hρ0).trans_eq
    have he : K ^ j = K * K ^ (j - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hj]
    rw [he]
    ring
  have hpc : 0 ≤ RawPrimary.phaseJetConstant P m :=
    RawPrimary.phaseJetConstant_nonneg (fun j _ _ ↦ hP j)
  have hexp := RawPrimary.norm_iteratedFDeriv_oscillation_le
    (hscaled.of_le (by simp) : ContDiffAt ℝ m ((-ρ) • Function.uncurry φ) (c, x))
    (mul_nonneg hρ0 hK0) hK0 (fun j _ _ ↦ hP j) hb
  have hbase : ρ * K + K ≤ 2 * ρ * K := by nlinarith
  have hexp' : ‖iteratedFDeriv ℝ m
      (fun z : Par × E ↦ carrier (-ρ) (φ z.1) z.2) (c, x)‖ ≤
        (RawPrimary.phaseJetConstant P m * 2 ^ m) * ρ ^ m * K ^ m := by
    apply hexp.trans
    calc
      _ ≤ RawPrimary.phaseJetConstant P m * (2 * ρ * K) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase m) hpc
      _ = _ := by simp only [mul_pow]; ring
  cases m with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have hn : ‖Function.uncurry (demodulationDefect ρ φ) (c, x)‖ ≤ 2 := by
      have he : ‖carrier (-ρ) (φ c) x‖ = 1 := by simp [carrier, Complex.norm_exp]
      simpa only [demodulationDefect, Function.uncurry_apply_pair, he, norm_one,
        one_add_one_eq_two] using norm_sub_le (carrier (-ρ) (φ c) x) (1 : ℂ)
    exact hn.trans (by simpa only [pow_zero, mul_one] using
      (show (2 : ℝ) ≤ 2 + RawPrimary.phaseJetConstant P 0 from le_add_of_nonneg_right hpc))
  | succ m =>
    have hcarrier : ContDiffAt ℝ (m + 1)
        (fun z : Par × E ↦ carrier (-ρ) (φ z.1) z.2) (c, x) := by
      have hh : ContDiffAt ℝ ∞
          (fun z : Par × E ↦ carrier (-ρ) (φ z.1) z.2) (c, x) := by
        unfold carrier
        exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (c, x)
          (contDiffAt_const.mul hφat))).cexp
      exact hh.of_le (by simp)
    change ‖iteratedFDeriv ℝ (m + 1)
      ((fun z : Par × E ↦ carrier (-ρ) (φ z.1) z.2) - fun _ ↦ (1 : ℂ)) (c, x)‖ ≤ _
    rw [iteratedFDeriv_sub_apply hcarrier contDiffAt_const]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
    exact hexp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
        (pow_nonneg hρ0 _)) (pow_nonneg hK0 _))

/-- The original phase profiles construct a common polynomial bound for all
compact observation coefficients through parameter order `k` and spatial
order `s`. Only the coefficient is differentiated spatially; the source will
remain at precisely Sobolev order `s`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_demodulationDefect_parameterJet_bound
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Par}, IsOpen V →
      ∀ {X : Set E}, IsCompact X → ∀ (ρ K : ℝ), 1 ≤ ρ → 1 ≤ K →
      ∀ (φ : Par → E → ℝ),
        ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ) →
        (∀ c ∈ V, tsupport (φ c) ⊆ X) →
      ∀ c ∈ V,
        (∀ x ∈ X, ∀ j, 1 ≤ j → j ≤ s + k →
          ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c, x)‖ ≤ P j * K ^ j) →
      ∀ vs : List Par, vs.length ≤ k → (∀ v ∈ vs, ‖v‖ ≤ 1) →
      ∀ j ≤ s, ∀ x,
        ‖iteratedFDeriv ℝ j (fun y ↦
          parameterListJet (fun a ↦ demodulationDefect ρ φ a y) vs c) x‖ ≤
            C * ρ ^ (s + k) * K ^ (s + k) := by
  let C₀ := fun m ↦ 2 + RawPrimary.phaseJetConstant P m * 2 ^ m
  have hC₀ : ∀ m, 0 ≤ C₀ m := fun m ↦ add_nonneg (by norm_num)
    (mul_nonneg (RawPrimary.phaseJetConstant_nonneg (fun j _ _ ↦ hP j)) (by positivity))
  let C := ∑ m ∈ Finset.range (s + k + 1), C₀ m
  have hC : 0 ≤ C := Finset.sum_nonneg fun m _ ↦ hC₀ m
  refine ⟨C, hC, ?_⟩
  intro V hV X hX ρ K hρ hK φ hφ hs c hc hphase vs hlen hv j hjs x
  have hreg := demodulationDefect_parameterJet_regular_support hV hX ρ hφ hs vs hc
  by_cases hx : x ∈ X
  · have hjet := norm_sourceJet_parameterListJet_le_joint hV isOpen_univ
      (contDiffOn_demodulationDefect ρ hφ) vs hv j hc (mem_univ x)
    have horder : j + vs.length ≤ s + k := Nat.add_le_add hjs hlen
    have hscalar := norm_joint_demodulationDefect_le hV hφ P hP hρ hK
      (j + vs.length) hc x (fun l hl hl' ↦ hphase x hx l hl (hl'.trans horder))
    apply (hjet.trans hscalar).trans
    have hc₀ : C₀ (j + vs.length) ≤ C :=
      Finset.single_le_sum (fun m _ ↦ hC₀ m) (Finset.mem_range_succ_iff.mpr horder)
    exact mul_le_mul (mul_le_mul hc₀ (pow_le_pow_right₀ hρ horder)
      (pow_nonneg (zero_le_one.trans hρ) _) hC)
      (pow_le_pow_right₀ hK horder) (pow_nonneg (zero_le_one.trans hK) _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans hρ) _))
  · have hz : iteratedFDeriv ℝ j (fun y ↦
        parameterListJet (fun a ↦ demodulationDefect ρ φ a y) vs c) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hreg.2 (tsupport_iteratedFDeriv_subset j h)))
    rw [hz, norm_zero]
    positivity

end JanetCartan.FixedDomainInverse.ObservedParameterRemainders
