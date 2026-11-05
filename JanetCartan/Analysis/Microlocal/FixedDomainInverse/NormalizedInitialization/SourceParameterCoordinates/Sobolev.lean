module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SourceParameterCoordinates.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphDecay.Normalization

/-!
# Sobolev bounds in the original product parameters

The original source profiles and joint phase bounds are pulled back by the
fixed contractive Euclidean split. The original parameter directions return
with the constant `2^k`. The frequency and slow-scale exponents, spatial
measure, and derivative reserves of the source theorem are unchanged.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.FixedDomainInverse
open ResponseTransfer ResponseTransfer.FullSourceEnvelopes
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential

variable {d r : ℕ}
local notation "P" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3+d)
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "splitP" => (EuclideanSpace.finAddEquivProd : Pc ≃L[ℝ] P)

/-- Apply the actual Euclidean normalized-carrier estimate to the original
product parameters. Only the constant changes by `2^k`; the spatial source
orders remain at most `j+(d+1)+1`, the parameter source orders at most `k`,
and the joint phase orders at most `j+k`. The phase and source hypotheses
are exactly the original profiles supplied by the initializer.

Consumer: the same inverse remainder on actual full-parameter source
derivatives in `ReducedSolutionEnvelopes/ParameterRemainder`
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_productParameterCarrierJet_sobolev_le_unit
    {V : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (C : ℕ → ℕ → ℝ)
    (k : ℕ) (ρ A K : ℝ) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    {φ : P → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    {f : P → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (f a) ⊆ S) {c : P} (hc : c ∈ V)
    (hm : ∀ vs : List P, MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume)
    (hmem : ∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _))
    (hprofile : ∀ vs, vs.length ≤ k → (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        C vs.length j * (A * K ^ vs.length) * K ^ j)
    (v : Fin k → P) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ)
    (hphase : ∀ x ∈ S, ∀ m ≤ j+k,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c,x)‖ ≤ H m * K ^ m) :
    vectorFourierSobolevNorm (j : ℝ)
      ((memLp_productParameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v hc).toLp
        (productParameterCarrierJet ρ φ f k v c)) ≤
      ((2 : ℝ)^k * UniformPhase.unitSobolevBudget (d+1) r S H C k j) *
        (A * ρ ^ k * K ^ (k+(d+1)+1)) * K ^ j := by
  let Vc := splitP ⁻¹' V
  let cc : Pc := (splitP).symm c
  let vc : Fin k → Pc := fun i ↦ (2 : ℝ)⁻¹ • (splitP).symm (v i)
  let φc : Pc → E → ℝ := fun a ↦ φ (splitP a)
  let fc : Pc → E → F := fun a ↦ f (splitP a)
  let pe := (splitP).prodCongr (ContinuousLinearEquiv.refl ℝ E)
  have hVc : IsOpen Vc := hV.preimage (splitP).continuous
  have hcc : cc ∈ Vc := by
    simpa only [cc, Vc, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hc
  have hvc : ∀ i, ‖vc i‖ ≤ 1 := fullSource_parameterTuple_unit v hv
  have hφc : ContDiffOn ℝ ∞ (Function.uncurry φc) (Vc ×ˢ U) :=
    hφ.comp pe.contDiff.contDiffOn (fun _ h ↦ ⟨h.1, h.2⟩)
  have hfc : ContDiffOn ℝ ∞ (Function.uncurry fc) (Vc ×ˢ univ) :=
    hf.comp pe.contDiff.contDiffOn (fun _ h ↦ ⟨h.1, h.2⟩)
  have hsc : ∀ a ∈ Vc, tsupport (fc a) ⊆ S := fun a ha ↦ hs (splitP a) ha
  have hsame (vs : List Pc) :
      (fun x ↦ parameterListJet (fun a ↦ fc a x) vs cc) =
        (fun x ↦ parameterListJet (fun a ↦ f a x) (vs.map splitP) c) := by
    funext x
    simpa only [fc, cc, ContinuousLinearEquiv.apply_symm_apply, Function.comp_def] using
      fullSource_parameterListJet_pullback (fun a ↦ f a x) vs cc
  let hmc (vs : List Pc) : MemLp (fun x ↦ parameterListJet (fun a ↦ fc a x) vs cc) 2 volume := by
    rw [hsame vs]
    exact hm (vs.map splitP)
  have hclass (vs : List Pc) : (hmc vs).toLp _ = (hm (vs.map splitP)).toLp _ := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (hsame vs))
  have hmemc (vs : List Pc) (i : ℕ) :
      MemVectorFourierSobolev (i : ℝ) ((hmc vs).toLp _) := by
    rw [hclass vs]
    exact hmem (vs.map splitP) i
  have hprofilec (vs : List Pc) (hlen : vs.length ≤ k)
      (hvs : ∀ w ∈ vs, ‖w‖ ≤ 1) (i : ℕ) :
      vectorFourierSobolevNorm (i : ℝ) ((hmc vs).toLp _) ≤
        C vs.length i * (A * K ^ vs.length) * K ^ i := by
    rw [hclass vs]
    have hunit : ∀ w ∈ vs.map splitP, ‖w‖ ≤ 1 := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      exact (fullSource_coordinate_norm_bounds.1 u).trans (hvs u hu)
    simpa only [List.length_map] using
      hprofile (vs.map splitP) (by simpa only [List.length_map] using hlen) hunit i
  have hpe (w : Pc × E) : ‖pe w‖ ≤ ‖w‖ :=
    max_le_max (fullSource_coordinate_norm_bounds.1 w.1) le_rfl
  have hphasec (x : E) (hx : x ∈ S) (m : ℕ) (hm : m ≤ j+k) :
      ‖iteratedFDeriv ℝ m (Function.uncurry φc) (cc,x)‖ ≤ H m * K ^ m := by
    change ‖iteratedFDeriv ℝ m ((Function.uncurry φ) ∘ pe) (cc,x)‖ ≤ _
    apply (norm_externalCoordinate_jet_le pe hpe (Function.uncurry φ) (cc,x) m).trans
    simpa [pe, cc] using hphase x hx m hm
  let jet := parameterCarrierJet ρ φc fc k vc cc
  let hj := memLp_parameterCarrierJet_of_original hVc hU hS hSU ρ hφc hfc hsc k vc hcc
  have hjmem : MemVectorFourierSobolev (j : ℝ) (hj.toLp jet) :=
    memVectorFourierSobolev_parameterCarrierJet_of_original hVc hU hS hSU
      ρ hφc hfc hsc k vc hcc j
  have hb := UniformPhase.norm_parameterCarrierJet_sobolev_le_unit
    hVc hU Subset.rfl hS hSU H hH C k ρ A K hρ hA hK hφc hfc hsc hcc
    hmc hmemc hprofilec vc hvc j hphasec
  have hlp :
      (memLp_productParameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v hc).toLp
        (productParameterCarrierJet ρ φ f k v c) = (2 : ℝ)^k • hj.toLp jet := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall
      (congrFun (productParameterCarrierJet_eq_unit_coordinate ρ φ f k v c))
  rw [hlp, (vectorFourierSobolevNorm_parameter_real_smul j ((2 : ℝ)^k) hjmem).2,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)^k)]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 : ℝ)^k)).trans_eq (by ring)

end JanetCartan.FixedDomainInverse
