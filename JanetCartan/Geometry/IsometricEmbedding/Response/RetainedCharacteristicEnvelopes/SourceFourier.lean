module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.CompactSobolev

/-!
# Fourier words of the retained full source

Convert the mixed L² tensors of the literal localized reduced source to the
ordered full-parameter Fourier bounds consumed by
`FullSourceEnvelopes.fullSource_capped_solver_residual_envelopes`. The conversion
uses precisely the total derivative order, with no Sobolev embedding loss.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open Pseudodifferential AmplitudeBound FullSourceEnvelopes ResponsePrimarySources
variable {n d r : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

private theorem scalar_derivative_family_of_word_L2 (s : ℕ)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ α : List (Fin n), α.length ≤ s →
      ∃ hm : MemLp (euclideanCoordinateDerivList α u) 2 volume,
        ‖hm.toLp (euclideanCoordinateDerivList α u)‖ ≤ B) :
    ∃ v : EuclideanL2DerivativeFamily n s,
      HasEuclideanL2Derivatives s
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) v ∧
      euclideanL2DerivativeNormSum v ≤ ((n : ℝ) + 1) ^ s * B := by
  induction s generalizing u with
  | zero =>
    obtain ⟨hm, hb⟩ := hb [] (by simp)
    refine ⟨fun _ ↦ (hu.continuous.memLp_of_hasCompactSupport hus).toLp u, rfl, ?_⟩
    simpa only [euclideanL2DerivativeNormSum, euclideanCoordinateDerivList, pow_zero, one_mul] using hb
  | succ s ih =>
    let u₂ : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    have hroot : ‖u₂‖ ≤ B := by
      obtain ⟨hm, hb⟩ := hb [] (by simp)
      exact hb
    let D (i : Fin n) := euclideanCoordinateDerivList [i] u
    have hd (i : Fin n) : ContDiff ℝ ∞ (D i) :=
      contDiff_euclideanCoordinateDerivList hu [i]
    have hds (i : Fin n) : HasCompactSupport (D i) := hus.fderiv_apply ℝ _
    have hdb (i : Fin n) (α : List (Fin n)) (hα : α.length ≤ s) :
        ∃ hm : MemLp (euclideanCoordinateDerivList α (D i)) 2 volume,
          ‖hm.toLp (euclideanCoordinateDerivList α (D i))‖ ≤ B := by
      rw [← euclideanCoordinateDerivList_append]
      exact hb (α ++ [i]) (by simpa using Nat.succ_le_succ hα)
    choose w hw hwbound using fun i ↦ ih (D i) (hd i) (hds i) (hdb i)
    let v : EuclideanL2DerivativeFamily n (s + 1) := fun a ↦
      match a with
      | none => u₂
      | some (i, a) => w i a
    have hv : HasEuclideanL2Derivatives (s + 1) u₂ v := by
      refine ⟨rfl, fun i ↦ ?_⟩
      change HasEuclideanL2CoordinateDerivative i u₂ (w i (.empty n s)) ∧
        HasEuclideanL2Derivatives s (w i (.empty n s)) (w i)
      rw [(hw i).root]
      exact ⟨hasEuclideanL2CoordinateDerivative_toLp u hu hus i, hw i⟩
    refine ⟨v, hv, ?_⟩
    have hpow : 1 ≤ ((n : ℝ) + 1) ^ s := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
    calc
      euclideanL2DerivativeNormSum v = ‖u₂‖ +
          ∑ i : Fin n, euclideanL2DerivativeNormSum (w i) := rfl
      _ ≤ ((n : ℝ) + 1) ^ s * B + ∑ _i : Fin n, ((n : ℝ) + 1) ^ s * B :=
        add_le_add (hroot.trans (le_mul_of_one_le_left hB hpow))
          (Finset.sum_le_sum fun i _ ↦ hwbound i)
      _ = ((n : ℝ) + 1) ^ (s + 1) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
        ring

/-- Mixed L² bounds for the SAME full-source function give the exact ordered
parameter Fourier bounds of `app:ch_response:eq:direct-envelope-profile`.
Only mixed tensors of orders `k` through `s+k` enter; the fixed reserve and
the source size (in the application, `τ³`) are preserved. -/
theorem fullSource_parameterWord_fourier_of_mixedL2
    {S : Set E} (hS : IsCompact S) {V : Set Par} (hV : IsOpen V)
    (a : E × Par → F) (ha : ContDiff ℝ ∞ a)
    (hz : ∀ q, q.1 ∉ S → a q = 0)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) {A L : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    {c : Par} (hc : c ∈ V)
    (hmixed : ∀ j, ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j a (x,c)) 2 volume,
      ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j a (x,c))‖ ≤ C j * A * L ^ j)
    (k : ℕ) (v : Fin k → Par) (hv : ∀ i, ‖v i‖ ≤ 1) (s : ℕ) :
    let f := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ a (x,b)) c v
    ∃ hm : MemLp f 2 volume,
      MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
          ((r : ℝ) * LowEnvelope.compactCoordinateSobolevConstant n s *
            ∑ j ∈ Finset.range (s + 1), C (j + k)) * A * L ^ (s + k) := by
  classical
  intro f
  have haj : ContDiffOn ℝ ∞ (Function.uncurry (fun b x ↦ a (x,b))) (V ×ˢ univ) :=
    (ha.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have hs : ∀ b ∈ V, tsupport (fun x ↦ a (x,b)) ⊆ S := by
    intro b _
    exact closure_minimal (fun x hx ↦ by by_contra h; exact hx (hz (x,b) h)) hS.isClosed
  let hm := fullSource_parameterJet_memLp hS hV haj hs k v hc
  have hf : ContDiff ℝ ∞ f := fullSource_parameterJet_contDiff hV haj k v hc
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.intro hS
    intro x hx
    have he : (fun b ↦ a (x,b)) = fun _ ↦ (0 : F) := funext fun b ↦ hz (x,b) hx
    dsimp only [f]
    rw [he]
    cases k <;> simp
  have hsp := primary_carrier_derivative_spatial_bounds isOpen_univ isOpen_univ
    ha.contDiffOn k v hv (c := c) (mem_univ c)
  let B := (∑ j ∈ Finset.range (s + 1), C (j + k)) * A * L ^ (s + k)
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hC (j + k))) hA)
    (pow_nonneg (zero_le_one.trans hL) _)
  let u (i : Fin r) : E → ℂ := fun x ↦ f x i
  have hu (i : Fin r) : ContDiff ℝ ∞ (u i) :=
    ((EuclideanSpace.proj i : F →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf
  have hus (i : Fin r) : HasCompactSupport (u i) :=
    hfs.comp_left (g := fun z : F ↦ z i) rfl
  have hub (i : Fin r) (α : List (Fin n)) (hα : α.length ≤ s) :
      ∃ hc : MemLp (euclideanCoordinateDerivList α (u i)) 2 volume,
        ‖hc.toLp (euclideanCoordinateDerivList α (u i))‖ ≤ B := by
    obtain ⟨hj, hjb⟩ := hmixed (α.length + k)
    have hproj : ‖(EuclideanSpace.proj i : F →L[ℂ] ℂ).restrictScalars ℝ‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z ↦ by
        change ‖z i‖ ≤ 1 * ‖z‖
        simpa only [one_mul] using PiLp.norm_apply_le z i)
    have hpoint (x : E) : ‖euclideanCoordinateDerivList α (u i) x‖ ≤
        ‖iteratedFDeriv ℝ (α.length + k) a (x,c)‖ := by
      apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv (hu i) α x).trans
      apply (((EuclideanSpace.proj i : F →L[ℂ] ℂ).restrictScalars ℝ).norm_iteratedFDeriv_comp_left
        hf.contDiffAt (by simp)).trans
      exact (mul_le_of_le_one_left (norm_nonneg _) hproj).trans (hsp.2 x (mem_univ x) _)
    have hc : MemLp (euclideanCoordinateDerivList α (u i)) 2 volume :=
      hj.mono (contDiff_euclideanCoordinateDerivList (hu i) α).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hpoint)
    refine ⟨hc, le_trans ?_ (hjb.trans ?_)⟩
    · rw [Lp.norm_toLp, Lp.norm_toLp]
      exact ENNReal.toReal_mono hj.eLpNorm_ne_top (eLpNorm_mono hc.aestronglyMeasurable hpoint)
    · exact mul_le_mul
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ ↦ hC (j+k))
          (Finset.mem_range_succ_iff.mpr hα)) hA)
        (pow_le_pow_right₀ hL (Nat.add_le_add_right hα k))
        (pow_nonneg (zero_le_one.trans hL) _)
        (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hC (j+k))) hA)
  choose w hw hwb using fun i ↦ scalar_derivative_family_of_word_L2 s (u i) (hu i) (hus i) hB (hub i)
  have he (i : Fin r) : finiteL2CoordinateIsometry volume (hm.toLp f) i =
      ((hu i).continuous.memLp_of_hasCompactSupport (hus i)).toLp (u i) := by
    rw [finiteL2CoordinateIsometry_toLp]
  have hmem : MemVectorFourierSobolev (s : ℝ) (hm.toLp f) := by
    intro i
    rw [he]
    exact (hw i).memFourierSobolev
  refine ⟨hm, hmem, ?_⟩
  calc
    _ ≤ ∑ i, fourierSobolevNorm (s : ℝ) (finiteL2CoordinateIsometry volume (hm.toLp f) i) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _i : Fin r, LowEnvelope.compactCoordinateSobolevConstant n s * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [he]
      exact (hw i).fourierSobolevNorm_le.trans
        ((mul_le_mul_of_nonneg_left (hwb i) (by positivity)).trans_eq (by
          unfold LowEnvelope.compactCoordinateSobolevConstant
          ring))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [B]; ring

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
