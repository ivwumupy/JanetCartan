module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Gap
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The smooth simple characteristic root

For `app:ch_seed:prop:seed-actual-menu` and
`app:ch_response:thm:response-compatible-choice`, construct the actual scalar root
of a smooth, positively degree-one homogeneous real symbol at a nonzero simple
characteristic covector. The result includes joint smoothness, uniqueness in an
open conic band, positive homogeneity, a uniform transverse derivative gap and
positive buffers for every compact subpatch.

`X` contains physical coordinates `(t,y)` and any smooth spectator parameters;
`E` is the transverse covector space. The input is the symbol itself, its
smoothness near the base covector, its homogeneity and its simple characteristic
condition. No root or inverse is supplied as an input. This proves the scalar
root construction, not the Hamilton phase or the response operators in the cited
source propositions.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The characteristic root: apply the implicit-function theorem to the symbol,
then extend from a positive angular section by degree-one homogeneity
(`app:ch_seed:prop:seed-actual-menu`). -/
def conicRoot (ℓ : E →L[ℝ] ℝ) {f : (X × E) × ℝ → ℝ} {z : (X × E) × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (hd : scalarDerivative f z ≠ 0) : X × E → ℝ :=
  homogeneousExtension ℓ (localRoot hf hd)

/-- A constructed simple characteristic root on an open conic neighborhood,
with uniqueness, joint smoothness, positive homogeneity and uniform gaps.
This is the scalar-root portion of `app:ch_seed:prop:seed-actual-menu` and
`app:ch_response:thm:response-compatible-choice`.

The angular functional is chosen in the proof, after deriving nonvanishing of
the transverse covector from homogeneity. The constant `c` works on the entire
constructed conic chart. The final assertion supplies a positive buffer around
the root graph over any compact subpatch. -/
theorem exists_conicRoot_patch {f : (X × E) × ℝ → ℝ} {S : Set ((X × E) × ℝ)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    (hh : ∀ (x : X) (η : E) (τ : ℝ) (r : ℝ), 0 < r →
      f ((x, r • η), r * τ) = r * f ((x, η), τ))
    {z : (X × E) × ℝ} (hzS : z ∈ S) (hz : f z = 0)
    (hd : scalarDerivative f z ≠ 0) (hξ : (z.2, z.1.2) ≠ 0) :
    ∃ (ℓ : E →L[ℝ] ℝ) (U : Set (X × E)) (V : Set ℝ) (c : ℝ),
      let H := conicRoot ℓ (hf.contDiffAt (hS.mem_nhds hzS)) hd
      ℓ z.1.2 = 1 ∧ IsOpen U ∧ IsOpen V ∧ 0 < c ∧
      IsOpen (conicDomain ℓ U) ∧ z.1 ∈ conicDomain ℓ U ∧
      H z.1 = z.2 ∧ ContDiffOn ℝ ∞ H (conicDomain ℓ U) ∧
      (∀ p ∈ conicDomain ℓ U, f (p, H p) = 0 ∧ (p, H p) ∈ conicBand ℓ U V) ∧
      (∀ p ∈ conicDomain ℓ U, ∀ r : ℝ, 0 < r →
        (p.1, r • p.2) ∈ conicDomain ℓ U ∧ H (p.1, r • p.2) = r * H p) ∧
      (∀ w ∈ conicBand ℓ U V, f w = 0 ↔ H w.1 = w.2) ∧
      (∀ p ∈ conicDomain ℓ U, ∃ d : ℝ,
        HasDerivAt (fun τ ↦ f (p, τ)) d (H p) ∧ c ≤ |d|) ∧
      (∀ K : Set (X × E), IsCompact K → K ⊆ conicDomain ℓ U →
        ∃ δ : ℝ, 0 < δ ∧
          Metric.cthickening δ ((fun p ↦ (p, H p)) '' K) ⊆ conicBand ℓ U V) := by
  let hf₀ := hf.contDiffAt (hS.mem_nhds hzS)
  have hη : z.1.2 ≠ 0 := transverse_ne_zero hh (hf₀.differentiableAt (by simp)) hz hd hξ
  obtain ⟨L, _, hL⟩ := exists_dual_vector ℝ z.1.2 (norm_ne_zero_iff.mpr hη)
  let ℓ : E →L[ℝ] ℝ := ‖z.1.2‖⁻¹ • L
  have hℓ : ℓ z.1.2 = 1 := by
    simp only [ℓ, smul_apply, smul_eq_mul, hL, RCLike.ofReal_real_eq_id, id_eq]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη)
  let H₀ := localRoot hf₀ hd
  obtain ⟨U, V, c, hU, hzU, hV, _, hc, hH, hgraph, huniq⟩ :=
    exists_localRoot_patch hS hf hzS hz hd
  have hnorm : normalize ℓ z.1 = z.1 := by
    simp only [normalize, hℓ, inv_one, one_smul, Prod.eta]
  refine ⟨ℓ, U, V, c, hℓ, hU, hV, hc, isOpen_conicDomain ℓ hU,
    ⟨by rw [hℓ]; norm_num, by rwa [hnorm]⟩, ?_,
    contDiffOn_homogeneousExtension ℓ hU hH, ?_, ?_, ?_, ?_, ?_⟩
  · change ℓ z.1.2 * H₀ (normalize ℓ z.1) = z.2
    rw [hℓ, hnorm, one_mul]
    exact localRoot_base hf₀ hd
  · intro p hp
    exact ⟨homogeneousExtension_zero ℓ hh (fun q hq ↦ (hgraph q hq).2.2.1) hp,
      homogeneousExtension_mem_conicBand ℓ (fun q hq ↦ (hgraph q hq).1) hp⟩
  · intro p hp r hr
    exact ⟨mem_conicDomain_smul ℓ U hp hr, homogeneousExtension_smul ℓ H₀ p hr⟩
  · intro w hw
    exact homogeneousExtension_unique ℓ hh huniq hw.1 hw.2
  · intro p hp
    let q := normalize ℓ p
    have hq : q ∈ U := hp.2
    have hdiff : DifferentiableAt ℝ f (q, H₀ q) :=
      (hf.contDiffAt (hS.mem_nhds (hgraph q hq).2.1)).differentiableAt (by simp)
    refine ⟨scalarDerivative f (q, H₀ q), ?_, (hgraph q hq).2.2.2⟩
    have hs := hasDerivAt_scaled hh hp.1 (hasDerivAt_scalar hdiff)
    simpa only [q, normalize, smul_inv_smul₀ hp.1.ne', Prod.eta,
      conicRoot, homogeneousExtension] using hs
  · intro K hK hKU
    exact exists_compact_graph_buffer ℓ hU hV hH (fun q hq ↦ (hgraph q hq).1) hK hKU

end JanetCartan.CharacteristicRoot
