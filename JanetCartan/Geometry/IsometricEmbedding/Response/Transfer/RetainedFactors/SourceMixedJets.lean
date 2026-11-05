module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SourceMixedJets.Spatial
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SourceMixedJets.Algebra

/-!
# Mixed source L² jets from the original Fourier-Sobolev profiles

The joint-source hypothesis of `app:ch_response:thm:response-literal-transfer`
controls every parameter derivative in every natural spatial Fourier order.
It yields the actual mixed Fréchet tensor in L², with precisely one power of
`K` per derivative and the physical `2 * π` Fourier convention.

The conclusion is the exact `hDatum` input of
`DirectEvolution.IntegratedEnvelope.Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets`
and
`DirectEvolution.IntegratedEnvelope.Assembly.fullElapsedAdjointEnvelope_hasEnvelopeProfile_of_primitive_jets`.
The response parent supplies the original source and applies those endpoints.
No bound on an operator or transferred envelope is assumed here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
open Complement.ParameterDerivatives Pseudodifferential
variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin 3)
local notation "F" => EuclideanSpace ℂ (Fin r)

private theorem spatialListJet_memLp_norm_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hm : MemLp f 2 volume) (xs : List E) (hx : ∀ x ∈ xs, ‖x‖ ≤ 1)
    (hs : MemVectorFourierSobolev (xs.length : ℝ) (hm.toLp f)) :
    ∃ hj : MemLp (parameterListJet f xs) 2 volume,
      ‖hj.toLp (parameterListJet f xs)‖ ≤
        (((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) ^ xs.length *
          vectorFourierSobolevNorm (xs.length : ℝ) (hm.toLp f) := by
  obtain ⟨hj, hb⟩ := spatialJet_memLp_norm_le hf hm xs.length hs
  have he : MemLp (parameterListJet f xs) 2 volume :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin xs.length ↦ E) F xs.get).comp_memLp' hj
  refine ⟨he, ?_⟩
  apply le_trans _ hb
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono hj.eLpNorm_ne_top
  apply eLpNorm_mono he.aestronglyMeasurable
  intro x
  exact (iteratedFDeriv ℝ xs.length f x).unit_le_opNorm
    (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr (fun i ↦ hx _ (List.get_mem ..)))

variable (n r)

/-- Original source Sobolev profiles imply the quantitative mixed datum
hypothesis of both integrated-envelope endpoints, for
`app:ch_response:eq:direct-envelope-profile` and the joint assertion of
`app:ch_response:thm:response-literal-transfer`.

The constant is chosen before the index type, source, parameter domain,
amplitude and frequency. One possible profile is
`(n + 3)^j * ∑ s ≤ j, B^s * max (C (j-s) s) 0`, where
`B = (r + 1) * (1 + 2 * π * n)`. Thus only original constants of total order
`j` enter, and there is no Sobolev embedding loss. The Fourier hypotheses use
exactly the L² representatives produced by `parameterSource_memLp`.
The supplied `ha` and `has` are the original interfaces shared with both
consumers; global smoothness and support are retained as in their hypotheses.
-/
theorem exists_sourceMixedJet_profile (C : ℕ → ℕ → ℝ) :
    ∃ Dprofile : ℕ → ℝ, (∀ j, 0 ≤ Dprofile j) ∧
      ∀ (I : Type*) (V : Set P) (S : Set E) (hS : IsCompact S) (hV : IsOpen V)
        (a : I → P → E → F) (A₀ K : I → ℝ)
        (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
        (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S),
        (∀ i, ContDiff ℝ ∞ (fun q : E × P ↦ a i q.2 q.1)) →
        (∀ i (q : E × P), q.1 ∉ S → a i q.2 q.1 = 0) →
        (∀ i, 0 ≤ A₀ i) → (∀ i, 1 ≤ K i) →
        (∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
          (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
            ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w))) →
        (∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
          (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
            ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤
                C l s * A₀ i * K i ^ (s + l)) →
        ∀ i c, c ∈ V → ∀ j,
          ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j
              (fun q : E × P ↦ a i q.2 q.1) (x, c)) 2 volume,
            ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j
              (fun q : E × P ↦ a i q.2 q.1) (x, c))‖ ≤
                A₀ i * Dprofile j * K i ^ j := by
  classical
  let B : ℝ := ((r : ℝ) + 1) * (1 + 2 * Real.pi * n)
  let Q : ℕ → ℝ := fun j ↦ ∑ s ∈ Finset.range (j + 1), B ^ s * max (C (j - s) s) 0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : ∀ j, 0 ≤ Q j := fun j ↦ Finset.sum_nonneg (fun s _ ↦
    mul_nonneg (pow_nonneg hB s) (le_max_right _ _))
  refine ⟨fun j ↦ (n + 3 : ℝ) ^ j * Q j, fun j ↦ mul_nonneg (by positivity) (hQ j), ?_⟩
  intro I V S hS hV a A₀ K ha has haj hglobal hA hK hmem hsob i c hc j
  have hAi : 0 ≤ A₀ i := hA i
  have hKi : 0 ≤ K i := zero_le_one.trans (hK i)
  let f : E × P → F := fun q ↦ a i q.2 q.1
  have hf : ContDiff ℝ ∞ f := haj i
  let g := fun (v : Fin j → (Fin n ⊕ Fin 3)) (x : E) ↦
    iteratedFDeriv ℝ j f (x, c) (fun k ↦ sourceJointBasis n (v k))
  have hg (v : Fin j → (Fin n ⊕ Fin 3)) :
      ∃ hm : MemLp (g v) 2 volume, ‖hm.toLp (g v)‖ ≤ Q j * A₀ i * K i ^ j := by
    obtain ⟨xs, ws, hlen, hxs, hws, he⟩ := exists_jointBasisJet_eq_spatial_parameter (r := r) v
    let u : E → F := fun y ↦ parameterListJet (fun b ↦ a i b y) ws c
    have hu : ContDiff ℝ ∞ u := contDiff_originalSourceListJet hV (ha i) ws hc
    have hw : ∀ k, ‖ws.get k‖ ≤ 1 := fun k ↦ hws _ (List.get_mem ..)
    have hm := parameterSource_memLp hS hV (ha i) (has i) ws.length ws.get hc
    obtain ⟨hj, hb⟩ := spatialListJet_memLp_norm_le hu hm xs hxs
      (hmem i c hc ws.length ws.get hw xs.length)
    have heq : g v = parameterListJet u xs := funext (fun x ↦ he f hf x c)
    rw [heq]
    refine ⟨hj, hb.trans ?_⟩
    have hsl : xs.length ≤ j := by omega
    have hl : ws.length = j - xs.length := by omega
    have hterm : B ^ xs.length * max (C ws.length xs.length) 0 ≤ Q j := by
      rw [hl]
      exact Finset.single_le_sum (f := fun s ↦ B ^ s * max (C (j - s) s) 0)
        (fun s _ ↦ mul_nonneg (pow_nonneg hB s) (le_max_right _ _))
        (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ B ^ xs.length * (C ws.length xs.length * A₀ i * K i ^ (xs.length + ws.length)) :=
        mul_le_mul_of_nonneg_left (hsob i c hc ws.length ws.get hw xs.length) (pow_nonneg hB _)
      _ ≤ B ^ xs.length * (max (C ws.length xs.length) 0 * A₀ i * K i ^ j) := by
        rw [hlen]
        gcongr
        exact le_max_left _ _
      _ = (B ^ xs.length * max (C ws.length xs.length) 0) * A₀ i * K i ^ j := by ring
      _ ≤ Q j * A₀ i * K i ^ j := by gcongr
  choose hgm hgb using hg
  let H : E → ℝ := fun x ↦ ∑ v : Fin j → (Fin n ⊕ Fin 3), ‖g v x‖
  have hH : MemLp H 2 volume := memLp_finsetSum Finset.univ (fun v _ ↦ (hgm v).norm)
  have hjc : Continuous (fun x : E ↦ iteratedFDeriv ℝ j f (x, c)) :=
    (hf.continuous_iteratedFDeriv (by simp)).comp (continuous_id.prodMk continuous_const)
  have hpoint (x : E) : ‖iteratedFDeriv ℝ j f (x, c)‖ ≤ ‖H x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun v _ ↦ norm_nonneg (g v x)))]
    exact norm_jointTensor_le_basis_sum _
  have hsupp : tsupport f ⊆ S ×ˢ (univ : Set P) := by
    apply closure_minimal _ (hS.isClosed.prod isClosed_univ)
    intro q hq
    refine ⟨?_, mem_univ _⟩
    by_contra h
    exact hq (hglobal i q h)
  have hzero (x : E) (hx : x ∉ S) : iteratedFDeriv ℝ j f (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hj ↦ hx (hsupp ((tsupport_iteratedFDeriv_subset j) hj)).1
  have hj : MemLp (fun x : E ↦ iteratedFDeriv ℝ j f (x, c)) 2 volume :=
    hjc.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hzero)
  refine ⟨hj, ?_⟩
  have hjH : ‖hj.toLp (fun x : E ↦ iteratedFDeriv ℝ j f (x, c))‖ ≤ ‖hH.toLp H‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hH.eLpNorm_ne_top (eLpNorm_mono hj.aestronglyMeasurable hpoint)
  apply hjH.trans
  have hsum := lpNorm_sum_le (p := 2) (μ := (volume : Measure E))
    (s := Finset.univ) (f := fun v x ↦ ‖g v x‖) (fun v _ ↦ (hgm v).norm) (by norm_num)
  have hHdef : (∑ v : Fin j → (Fin n ⊕ Fin 3), fun x : E ↦ ‖g v x‖) = H := by
    funext x
    simp [H]
  rw [hHdef] at hsum
  have hnorm (v) : lpNorm (fun x ↦ ‖g v x‖) 2 volume = lpNorm (g v) 2 volume :=
    lpNorm_norm (hgm v).aestronglyMeasurable 2
  simp_rw [hnorm] at hsum
  have hn : ‖hH.toLp H‖ ≤ ∑ v, ‖(hgm v).toLp (g v)‖ := by
    simpa only [Lp.norm_toLp, lpNorm] using hsum
  apply hn.trans
  calc
    _ ≤ ∑ _v : Fin j → (Fin n ⊕ Fin 3), Q j * A₀ i * K i ^ j :=
      Finset.sum_le_sum (fun v _ ↦ hgb v)
    _ = _ := by simp [Fintype.card_sum]; ring
end JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
