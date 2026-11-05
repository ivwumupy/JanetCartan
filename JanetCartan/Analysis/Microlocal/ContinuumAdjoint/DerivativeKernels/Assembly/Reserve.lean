module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation

/-!
# Primitive conic reserves for the actual differentiated amplitudes

For `app:ch_background:prop:bg-adjoint`, assemble support preservation and
fixed-baseline interpolation into the exact input of the conic L² theorem.
The high interpolation order is independent of the derivative word length:
this includes the empty word when estimating all derivatives through order s.
The consumer is the raw adjoint Sobolev assembly. Only original symbol profiles
and closed geometric buffers are inputs; generated reserves are conclusions.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol
variable {n : ℕ}

/-- A common constant for all low symbol derivatives, with any positive
interpolation order T, including the empty derivative word. This is the
all-orders version needed to sum the physical derivatives in
`app:ch_background:prop:bg-adjoint`. The reserve Q does not occur in the high
exponent, and the constant is chosen before T and H. -/
theorem exists_expansion_reserve_symbol_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (Q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H T R : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ Q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) *
          Real.sqrt R := by
  classical
  have hex (q : Fin (Q+1)) := exists_expansion_rescaled_reserve_bound
    L V a ha hfield ds χ t ht Q q W B hW hB
  choose C hC hb using hex
  refine ⟨∑ q, C q, Finset.sum_nonneg (fun q _ ↦ hC q), ?_⟩
  intro H T R hH hT U hU hlocal p hp hrad hradBound hamp hcoeff q hq
  let i : Fin (Q+1) := ⟨q, Nat.lt_succ_of_le hq⟩
  have hci : C i ≤ ∑ j, C j := Finset.single_le_sum
    (fun j _ ↦ hC j) (Finset.mem_univ i)
  have hq' : ds.length - t.dataDerivatives.length + q - Q ≤
      ds.length - t.dataDerivatives.length := by omega
  have he : H ^ (((ds.length - t.dataDerivatives.length + q - Q : ℕ) : ℝ) / T) ≤
      H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) :=
    Real.rpow_le_rpow_of_exponent_le hH
      (div_le_div_of_nonneg_right (by exact_mod_cast hq') hT.le)
  apply (hb i H T R hH hT U hU hlocal p hp hrad
    (fun j hj ↦ hradBound j (hj.trans hq))
    (fun j hj ↦ hamp j (hj.trans (Nat.add_le_add_left hq _)))
    (fun d hd j l hl ↦ hcoeff d hd j l (hl.trans (Nat.add_le_add_left hq _)))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hci he (Real.rpow_nonneg (le_trans zero_le_one hH) _) 
      (Finset.sum_nonneg (fun j _ ↦ hC j))) (Real.sqrt_nonneg R)

/-- The actual expansion satisfies every field of the conic amplitude reserve
in `app:ch_background:prop:bg-adjoint`. The original normalized amplitude and
L,V need jets only through length(ds)-k+Q. Taking Q=2(n+1) supplies the checked
matrix PDO bound with a reserve independent of the Sobolev order. Geometry,
original primitive profiles, and their eventual production from G and r remain
explicit conditional inputs; no generated jet estimate is assumed. -/
theorem exists_expansion_primitiveAmplitudeReserve (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (Q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i)
    (g : Chart n) (ρ : ℝ) (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n-1))) (J : Set (JointVariables n))
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω)
    (hΩunit : Ω ⊆ {η | ‖η‖ = 1}) (hρ : 0 < ρ)
    (hsupp : ∀ z x η, frequencyScaleAmplitude (halfOrderRadialFactor χ) a z x η ≠ 0 →
      z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖)
    (hJ : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ J)
    (hclosed : IsClosed (g.push '' J)) (himage : g.push '' J ⊆ g.outputDomain) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U → {η | ‖η‖ = 1} ⊆ U →
      (∀ R, ρ ≤ R → ∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ i ≤ Q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ R, ρ ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i-Q : ℕ) : ℝ) / T)) →
      (∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 → ∀ d ∈ ds, ∀ j i,
        i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i-Q : ℕ) : ℝ) / T)) →
      PrimitiveAmplitudeReserve g Q ρ
        (C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T))
        X (Prod.snd '' Z) Z Ω J t.amplitude := by
  obtain ⟨C, hC, hb⟩ := exists_expansion_reserve_symbol_bound
    L V a ha hfield ds χ t ht Q W B hW hB
  refine ⟨C, hC, ?_⟩
  intro H T hH hT U hU hunit hlocal hrad hradBound hamp hcoeff
  obtain ⟨hc, hs, hbuf⟩ := adjointDerivativeExpansion_conic_properties L V ds
    (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) hX hZ hΩ hρ hsupp
    g J hJ hclosed himage t ht
  refine ⟨mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hH) _),
    hc, hZ, hΩ, hΩunit, hs, hbuf, ?_⟩
  intro R hR p hp q hq
  rw [norm_iteratedFDeriv_scaledOriginalAmplitude]
  exact hb H T R hH hT U hU (hlocal R hR) ((p.1,p.2.1),p.2.2) (hunit hp)
    (hrad R hR _ hp) (hradBound R hR _ hp) (hamp R hR _ hp)
    (hcoeff _ hp) q hq

end JanetCartan.ContinuumAdjoint.DerivativeKernels
