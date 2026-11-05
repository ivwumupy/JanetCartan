module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.StrongAssembly
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneBranches

/-!
# Gain one from actual first-output amplitudes

For the gain-one paragraph after `app:ch_regular_base:eq:graph-derivative-transfer`,
apply the low L² reserve to the proved first-output branch bounds, prove the
finite weak expansions, apply the order-zero Fourier assembly at `t`, and
reconstruct regularity at `t+1`. The original output's low L² bound and the
actual first-output weak identities are used before density extension.

Only individual original primitive profiles are quantitative high inputs. Their
normalization from order-minus-one amplitude and homogeneous phase seminorms
remains an obligation of the parent assembly. No branch operator estimate,
operator derivative identity, or Sobolev gain is assumed. The low realizations
and phase/carrier geometry remain conditional inputs from their named producers.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter LineDeriv JanetCartan.Pseudodifferential
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The actual forward first-output amplitude preserves admissibility, even
though the phase is smooth only off zero. The closed frequency exclusion makes
the resulting complete amplitude smooth across zero.
Source: gain one following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ForwardAmplitudeAdmissible.graphFirstOutput
    {X Y F : Set E} {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (i : Fin n) : ForwardAmplitudeAdmissible X Y F (graphFirstOutputAmplitude S A i) := by
  have hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p := by
    intro p _
    exact hA.smooth.contDiffAt.comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hsupp : ∀ p : Point n, p ∉ (X ×ˢ Y) ×ˢ F → uncurry A p = 0 := by
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  have hsupport := (GainOneBranches.support_graphFirstOutput S A i).trans
    (tsupport_subset_carrier (hX.prod hY) hF hsupp)
  have hzero (p : Point n) (hp : p ∉ (X ×ˢ Y) ×ˢ F) :
      uncurry (graphFirstOutputAmplitude S A i) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm ↦ hp (hsupport hm))
  have hreg : ContDiff ℝ ∞ (uncurry (graphFirstOutputAmplitude S A i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 = 0
    · have he : uncurry (graphFirstOutputAmplitude S A i) =ᶠ[𝓝 p] fun _ ↦ 0 := by
        filter_upwards [(continuous_snd.isOpen_preimage _ hF.isOpen_compl).mem_nhds
          (by change p.2 ∉ F; simpa only [hp] using hF0)] with q hq
        exact hzero q (fun h ↦ hq h.2)
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact GainOneBranches.smooth_graphFirstOutput S A hS hsmooth i p hp
  refine ⟨hreg.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd), ?_⟩
  intro x y η h
  exact hzero ((x, y), η) (by simpa only [Set.mem_prod, not_and_or, or_assoc] using h)

private theorem gain_one_all_data
    (t : ℕ) (C₀ D : ℝ) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : H →L[ℂ] H) (T₁ : Fin n → H →L[ℂ] H)
      (Hhigh : ℝ), 1 ≤ Hhigh → ‖T‖ ≤ C₀ →
      (∀ (u : graphTestSpace n r) i,
        lineDerivOp (EuclideanSpace.single i (1 : ℝ))
          (T (graphTestToLp u) : 𝓢'(E, V)) = (T₁ i (graphTestToLp u) : 𝓢'(E, V))) →
      (∀ (u : graphTestSpace n r) i,
        MemVectorFourierSobolev (t : ℝ) (T₁ i (graphTestToLp u)) ∧
          vectorFourierSobolevNorm (t : ℝ) (T₁ i (graphTestToLp u)) ≤ D *
            (vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖)) →
      ∀ u : H, MemVectorFourierSobolev (t : ℝ) u →
        MemVectorFourierSobolev ((t : ℝ) + 1) (T u) ∧
          vectorFourierSobolevNorm ((t : ℝ) + 1) (T u) ≤ C *
            (vectorFourierSobolevNorm (t : ℝ) u + Hhigh * ‖u‖) := by
  let K : ℝ := r * (C₀ + (t + 1 : ℝ) * n * D)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1 + (r : ℝ) * r * K, by positivity, ?_⟩
  intro T T₁ Hhigh hH hT hd hb u hu
  have htest (v : graphTestSpace n r) :
      MemVectorFourierSobolev ((t : ℝ) + 1) (T (graphTestToLp v)) ∧
        vectorFourierSobolevNorm ((t : ℝ) + 1) (T (graphTestToLp v)) ≤ K *
          (vectorFourierSobolevNorm (t : ℝ) (graphTestToLp v) + Hhigh * ‖graphTestToLp v‖) := by
    let W := vectorFourierSobolevNorm (t : ℝ) (graphTestToLp v) + Hhigh * ‖graphTestToLp v‖
    have hW : ‖graphTestToLp v‖ ≤ W := by
      have hn : 0 ≤ vectorFourierSobolevNorm (t : ℝ) (graphTestToLp v) := norm_nonneg _
      have hh := le_mul_of_one_le_left (norm_nonneg (graphTestToLp v)) hH
      dsimp [W]
      linarith
    have hlow : ‖T (graphTestToLp v)‖ ≤ C₀ * W :=
      (T.le_opNorm _).trans (mul_le_mul hT hW (norm_nonneg _) hC₀)
    have hsum : (∑ i, vectorFourierSobolevNorm (t : ℝ) (T₁ i (graphTestToLp v))) ≤
        (n : ℝ) * (D * W) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hb v i).2)
    have hr := graph_vector_reconstruction t (T (graphTestToLp v))
      (fun i ↦ T₁ i (graphTestToLp v)) (fun i ↦ (hb v i).1) (hd v)
    refine ⟨hr.1, hr.2.trans ?_⟩
    calc
      _ ≤ (r : ℝ) * (C₀ * W + (t + 1 : ℝ) * ((n : ℝ) * (D * W))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hlow (mul_le_mul_of_nonneg_left hsum (by positivity))) (Nat.cast_nonneg r)
      _ = K * W := by dsimp [K]; ring
  have he := graph_vector_bound_of_compactSmooth T t ((t : ℝ) + 1) K Hhigh hK
    (zero_le_one.trans hH) htest u hu
  refine ⟨he.1, he.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith)
    (add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans hH) (norm_nonneg _)))

/-- Gain one for the forward graph from original weighted primitive profiles.
The actual first-output formulas, branch bounds and weak expansions are applied
here; the low L² bound reconstructs the original output. The case `t=0` is
included. Normalization of the primitive profiles is a separate parent obligation.
Source: `app:ch_regular_base:eq:fio-input`, `d=1`, output order `t+1`. -/
theorem exists_graph_gain_one_constant_of_primitive_profiles
    (μ₀ t : ℕ) (P C₀ : ℝ) (hP : 1 ≤ P) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y F : Set E), IsCompact X → IsCompact Y → IsClosed F → (0 : E) ∉ F →
      ∀ (S : E → E → ℝ),
      (∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) →
      (∀ p ∈ X ×ˢ Y, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det) →
      (∀ x η, η ≠ 0 → ∀ᶠ a : ℝ in 𝓝 1,
        (fun z ↦ S z (a • η)) =ᶠ[𝓝 x] (fun z ↦ a * S z η)) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X Y F A →
      GraphDistributionalRealization (graphOperator S) χ A (T A) → ‖T A‖ ≤ C₀ →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) →
      (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X Y F G →
        GraphDistributionalRealization (graphOperator S) χ G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      ∀ Hhigh : ℝ, 1 ≤ Hhigh →
      (∀ p ∈ (X ×ˢ Y) ×ˢ F, ∀ w : List (Coordinate n), w.length ≤ μ₀ + (t + 1) →
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤
          P * GainOneBranches.profile (μ₀ + 1) t Hhigh w.length / ρ p.2) →
      (∀ p ∈ (X ×ˢ Y) ×ˢ F, ∀ w : List (Coordinate n), w.length ≤ μ₀ + (t + 1) →
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (phasePrimitive S)) p‖ ≤
          P * GainOneBranches.profile (μ₀ + 1) t Hhigh w.length * ρ p.2) →
      (∀ p ∈ (X ×ˢ Y) ×ˢ F, ∀ a (w : List (Coordinate n)), w.length ≤ μ₀ + (t + 1) →
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
          P * GainOneBranches.profile (μ₀ + 1) t Hhigh w.length) →
      (∀ i (is : List (Fin n)), is.length ≤ t →
        ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
          (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
          GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (t : ℝ) u →
        MemVectorFourierSobolev ((t : ℝ) + 1) (T A u) ∧
          vectorFourierSobolevNorm ((t : ℝ) + 1) (T A u) ≤ C *
            (vectorFourierSobolevNorm (t : ℝ) u + Hhigh * ‖u‖) := by
  obtain ⟨D, hD, hfourier⟩ := exists_graph_vector_sobolev_constant_all_data (n := n) (r := r) t
    (C₀ * GainOneBranches.branchConstant n μ₀ t P)
    (mul_nonneg hC₀ (GainOneBranches.branchConstant_nonneg n μ₀ t hP))
  obtain ⟨C, hC, hgain⟩ := gain_one_all_data (n := n) (r := r) t C₀ D hC₀ hD.le
  refine ⟨C, hC, ?_⟩
  intro X Y F hX hY hF hF0 S hS hinv hhom χ hχ hχs T A hA hrealA hlow
    ρ hρ hl2 Hhigh hH hAmp hPhase hScalar hreal u hu
  have hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p := by
    intro p _
    exact hA.smooth.contDiffAt.comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hsupp : ∀ p : Point n, p ∉ (X ×ˢ Y) ×ˢ F → uncurry A p = 0 := by
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  have hfirst (i : Fin n) := hA.graphFirstOutput hX hY hF hF0 S hS i
  have hinit (i : Fin n) := hreal i [] (Nat.zero_le _) _ (List.mem_singleton_self _)
  apply hgain (T A) (fun i ↦ T (graphFirstOutputAmplitude S A i)) Hhigh hH hlow
    (fun v i ↦ graph_realization_weak_firstOutput hA hX hF hF0 hS χ hχ hχs i
      (T A) (T (graphFirstOutputAmplitude S A i)) hrealA (hinit i) v) ?_ u hu
  intro v i
  apply hfourier (graphTransferRemainder S) (graphTransferDatum S)
    (graphFirstOutputAmplitude S A i) T (T (graphFirstOutputAmplitude S A i))
    Hhigh (zero_le_one.trans hH) ?_ ?_ (graphTestToLp v) (graphTest_memVectorFourierSobolev _ v)
  · intro w is his
    exact graph_realization_weak_derivative_expansion hX hY hF hF0 S hS hhom
      χ hχ hχs T _ (hfirst i) w is (fun js hjs p hp ↦ hreal i js (hjs.trans his) p hp)
  · intro is his p hp
    have hpA : ForwardAmplitudeAdmissible X Y F p.1 :=
      fullAmplitudeDerivativeTerms_preserves_predicate _ _ (ForwardAmplitudeAdmissible X Y F)
        (fun i G hG ↦ hG.graphTransferRemainder hX.isClosed hY.isClosed hF hF0 S hS i)
        (fun i j G hG ↦ hG.graphTransferDatum hF hF0 S hS i j) _ (hfirst i) is p hp
    have hj := GainOneBranches.graph_branch_jet_norm_le_of_profiles μ₀ (t + 1) (by omega)
      P hP Hhigh hH S A (hX.prod hY) hF hF0 hS hinv hsmooth hsupp ρ hρ
      hAmp hPhase hScalar i is (by simpa using his) p hp
    simp only [Nat.add_sub_cancel] at hj
    have hlen := (fullAmplitudeDerivativeTerms_datum_length_le _ _ _ is p hp).trans his
    have hn := hl2 p.1 hpA (hreal i is his p hp)
      (GainOneBranches.branchConstant n μ₀ t P * Hhigh ^ (((t - p.2.length : ℕ) : ℝ) / t))
      (mul_nonneg (GainOneBranches.branchConstant_nonneg _ _ _ hP)
        (Real.rpow_nonneg (zero_le_one.trans hH) _)) hj
    simpa only [Nat.cast_sub hlen, mul_assoc] using hn

/-- Gain one for the supplied literal Hilbert adjoint from original primitive
profiles. The first-output amplitude is conjugated exactly once in the original
coordinate order. Actual weak identities and the entire branch expansion are
proved before reconstruction and extension to all Sobolev data.
Source: `app:ch_regular_base:eq:fio-input`, `d=1`, output order `t+1`. -/
theorem exists_adjoint_gain_one_constant_of_primitive_profiles
    (μ₀ t : ℕ) (P C₀ : ℝ) (hP : 1 ≤ P) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K₀ : Set (E × E)) (F : Set E), IsCompact K₀ → IsClosed F → (0 : E) ∉ F →
      ∀ (S : E → E → ℝ),
      (∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) →
      (∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det) →
      (∀ p ∈ K₀, ∀ η, η ≠ 0 → ∀ᶠ a : ℝ in 𝓝 1,
        (fun z ↦ S z (a • η)) =ᶠ[𝓝 p.1] (fun z ↦ a * S z η)) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) → (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ReverseAmplitudeAdmissible K₀ A → (∀ x y η, η ∉ F → A x y η = 0) →
      ∀ U : H →L[ℂ] H,
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose) U.adjoint →
      ‖U.adjoint‖ ≤ C₀ →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
      (∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ G →
        (∀ x y η, η ∉ F → G x y η = 0) →
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun j η ↦ star (χ j η)) G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      ∀ Hhigh : ℝ, 1 ≤ Hhigh →
      (∀ p ∈ K₀ ×ˢ F, ∀ w : List (Coordinate n), w.length ≤ μ₀ + (t + 1) →
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤
          P * GainOneBranches.profile (μ₀ + 1) t Hhigh w.length / ρ p.2) →
      (∀ p ∈ K₀ ×ˢ F, ∀ a (w : List (Coordinate n)), w.length ≤ μ₀ + (t + 1) →
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
          P * GainOneBranches.profile (μ₀ + 1) t Hhigh w.length) →
      (∀ i (is : List (Fin n)), is.length ≤ t →
        ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
          (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
          GraphDistributionalRealization (reverseGraphOperator S)
            (fun j η ↦ star (χ j η)) p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (t : ℝ) u →
        MemVectorFourierSobolev ((t : ℝ) + 1) (U.adjoint u) ∧
          vectorFourierSobolevNorm ((t : ℝ) + 1) (U.adjoint u) ≤ C *
            (vectorFourierSobolevNorm (t : ℝ) u + Hhigh * ‖u‖) := by
  obtain ⟨D, hD, hfourier⟩ := exists_graph_vector_sobolev_constant_all_data (n := n) (r := r) t
    (C₀ * GainOneBranches.branchConstant n μ₀ t P)
    (mul_nonneg hC₀ (GainOneBranches.branchConstant_nonneg n μ₀ t hP))
  obtain ⟨C, hC, hgain⟩ := gain_one_all_data (n := n) (r := r) t C₀ D hC₀ hD.le
  refine ⟨C, hC, ?_⟩
  intro K₀ F hK₀ hF hF0 S hS hinv hhom χ hχ hχs hχ0 T A hA hAF U hU hlow
    ρ hρ hηρ hl2 Hhigh hH hAmp hScalar hreal u hu
  have hsupp : ∀ p : Point n, p ∉ K₀ ×ˢ F → uncurry A p = 0 := by
    intro p hp
    by_cases hk : p.1 ∈ K₀
    · exact hAF _ _ _ (fun hf ↦ hp ⟨hk, hf⟩)
    · exact image_eq_zero_of_notMem_tsupport (fun hm ↦ hk (hA.support hm))
  have hfirst (i : Fin n) : ReverseAmplitudeAdmissible K₀ (adjointFirstOutputAmplitude A i) :=
    hA.conjTranspose.reverseFirstOutputAmplitude i
  have hinit (i : Fin n) := hreal i [] (Nat.zero_le _) _ (List.mem_singleton_self _)
  apply hgain U.adjoint (fun i ↦ T (adjointFirstOutputAmplitude A i)) Hhigh hH hlow
    (fun v i ↦ adjointGraph_realization_weak_firstOutput hA hK₀ hS χ hχ hχs hχ0 i
      U (T (adjointFirstOutputAmplitude A i)) hU (hinit i) v) ?_ u hu
  intro v i
  apply hfourier (adjointTransferRemainder S) (adjointTransferDatum S)
    (adjointFirstOutputAmplitude A i) T (T (adjointFirstOutputAmplitude A i))
    Hhigh (zero_le_one.trans hH) ?_ ?_ (graphTestToLp v) (graphTest_memVectorFourierSobolev _ v)
  · intro w is his
    apply reverseGraph_realization_weak_derivative_expansion hK₀ S hS hinv hhom
      (fun j η ↦ star (χ j η)) (fun j ↦ (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hχ j))
      (fun j ↦ (hχs j).comp_left (star_zero _))
      (fun j hm ↦ hχ0 j ((tsupport_comp_subset (g := star) (star_zero _) _) hm))
      T _ (hfirst i) w is (fun js hjs p hp ↦ hreal i js (hjs.trans his) p hp)
  · intro is his p hp
    have hpA : ReverseAmplitudeAdmissible K₀ p.1 :=
      fullAmplitudeDerivativeTerms_preserves_predicate _ _ (ReverseAmplitudeAdmissible K₀)
        (fun i G hG ↦ hG.adjointTransferRemainder S hS hinv i)
        (fun i j G hG ↦ hG.adjointTransferDatum S hS hinv i j) _ (hfirst i) is p hp
    have hj := GainOneBranches.adjoint_branch_jet_norm_le_of_profiles μ₀ (t + 1) (by omega)
      P hP Hhigh hH S A hK₀ hF hF0 hS hinv hA.smooth hsupp ρ hρ hηρ
      hAmp hScalar i is (by simpa using his) p hp
    simp only [Nat.add_sub_cancel] at hj
    have hpF : ∀ x y η, η ∉ F → p.1 x y η = 0 := by
      intro x y η hη
      have hs := (adjoint_branch_jet_support is p hp []).trans
        ((GainOneBranches.support_adjointFirstOutput A i).trans
          (tsupport_subset_carrier hK₀ hF hsupp))
      have hz : uncurry (jet [] p.1) ((x, y), η) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hm ↦ hη (hs hm).2)
      exact hz
    have hlen := (fullAmplitudeDerivativeTerms_datum_length_le _ _ _ is p hp).trans his
    have hn := hl2 p.1 hpA hpF (hreal i is his p hp)
      (GainOneBranches.branchConstant n μ₀ t P * Hhigh ^ (((t - p.2.length : ℕ) : ℝ) / t))
      (mul_nonneg (GainOneBranches.branchConstant_nonneg _ _ _ hP)
        (Real.rpow_nonneg (zero_le_one.trans hH) _)) hj
    simpa only [Nat.cast_sub hlen, mul_assoc] using hn

end JanetCartan.FourierIntegral
