module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets

/-!
# Mixed source tensors with the original natural reserve

Each mixed spatial/parameter basis word has one total derivative order. Its
spatial part is estimated at exactly that Fourier order, and its parameter
part is the actual derivative of the original compact source. The same natural
subtraction reserve therefore survives the finite tensor reconstruction.

Consumer: finite-order effective-scale application of the selected diagonal
and retarded near estimates in `app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open ResponseTransfer.FullSourceEnvelopes ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential ResponseTransfer.RetainedFactors.SourceMixedJets
variable {n d r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

private theorem reserved_spatialListJet_memLp_norm_le {f : E → F} (hf : ContDiff ℝ ∞ f)
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

variable (n d r)

/-- The original reserved Fourier source profile gives the actual full mixed
Fréchet L² tensor with the same natural reserve and no additional spatial
order. Constants are fixed before the source family, carrier, and history.
Source: `app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:cor:current-atoms`. -/
theorem exists_fullSource_reserved_mixedL2_profile (C : ℕ → ℕ → ℝ) (reserve : ℕ) :
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
            ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w))) →
        (∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
          (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
            ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤
                C l s * A₀ i * K i ^ (s + l - reserve)) →
        ∀ i c, c ∈ V → ∀ j,
          ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j
              (fun q : E × P ↦ a i q.2 q.1) (x, c)) 2 volume,
            ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j
              (fun q : E × P ↦ a i q.2 q.1) (x, c))‖ ≤
                A₀ i * Dprofile j * K i ^ (j - reserve) := by
  classical
  let B : ℝ := ((r : ℝ) + 1) * (1 + 2 * Real.pi * n)
  let Q : ℕ → ℝ := fun j ↦ ∑ s ∈ Finset.range (j + 1), B ^ s * max (C (j - s) s) 0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : ∀ j, 0 ≤ Q j := fun j ↦ Finset.sum_nonneg (fun s _ ↦
    mul_nonneg (pow_nonneg hB s) (le_max_right _ _))
  refine ⟨fun j ↦ ((n : ℝ) + (3 + d)) ^ j * Q j, fun j ↦ mul_nonneg (by positivity) (hQ j), ?_⟩
  intro I V S hS hV a A₀ K ha has haj hglobal hA hK hmem hsob i c hc j
  have hAi : 0 ≤ A₀ i := hA i
  have hKi : 0 ≤ K i := zero_le_one.trans (hK i)
  let f : E × P → F := fun q ↦ a i q.2 q.1
  have hf : ContDiff ℝ ∞ f := haj i
  let g := fun (v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d))) (x : E) ↦
    iteratedFDeriv ℝ j f (x, c) (fun k ↦ fullSourceMixedBasis n d (v k))
  have hg (v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d))) :
      ∃ hm : MemLp (g v) 2 volume, ‖hm.toLp (g v)‖ ≤ Q j * A₀ i * K i ^ (j - reserve) := by
    obtain ⟨xs, ws, hlen, hxs, hws, he⟩ := exists_fullSource_mixedBasisJet_spatial_parameter (r := r) v
    let u : E → F := fun y ↦ parameterListJet (fun b ↦ a i b y) ws c
    have hu : ContDiff ℝ ∞ u := fullSource_parameterJet_contDiff hV (ha i) ws.length ws.get hc
    have hw : ∀ k, ‖ws.get k‖ ≤ 1 := fun k ↦ hws _ (List.get_mem ..)
    have hm := fullSource_parameterJet_memLp hS hV (ha i) (has i) ws.length ws.get hc
    obtain ⟨hj, hb⟩ := reserved_spatialListJet_memLp_norm_le hu hm xs hxs
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
      _ ≤ B ^ xs.length * (C ws.length xs.length * A₀ i * K i ^ (xs.length + ws.length - reserve)) :=
        mul_le_mul_of_nonneg_left (hsob i c hc ws.length ws.get hw xs.length) (pow_nonneg hB _)
      _ ≤ B ^ xs.length * (max (C ws.length xs.length) 0 * A₀ i * K i ^ (j - reserve)) := by
        rw [hlen]
        gcongr
        exact le_max_left _ _
      _ = (B ^ xs.length * max (C ws.length xs.length) 0) * A₀ i * K i ^ (j - reserve) := by ring
      _ ≤ Q j * A₀ i * K i ^ (j - reserve) := by gcongr
  choose hgm hgb using hg
  let H : E → ℝ := fun x ↦ ∑ v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d)), ‖g v x‖
  have hH : MemLp H 2 volume := memLp_finsetSum Finset.univ (fun v _ ↦ (hgm v).norm)
  have hjc : Continuous (fun x : E ↦ iteratedFDeriv ℝ j f (x, c)) :=
    (hf.continuous_iteratedFDeriv (by simp)).comp (continuous_id.prodMk continuous_const)
  have hpoint (x : E) : ‖iteratedFDeriv ℝ j f (x, c)‖ ≤ ‖H x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun v _ ↦ norm_nonneg (g v x)))]
    exact norm_fullSource_mixedTensor_le_sum _
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
  have hHdef : (∑ v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d)), fun x : E ↦ ‖g v x‖) = H := by
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
    _ ≤ ∑ _v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d)), Q j * A₀ i * K i ^ (j - reserve) :=
      Finset.sum_le_sum (fun v _ ↦ hgb v)
    _ = _ := by simp [Fintype.card_sum]; ring

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
