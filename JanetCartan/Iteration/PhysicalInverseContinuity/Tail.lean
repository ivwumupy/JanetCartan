module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Compact

/-!
# Uncut raw adjoint comparison from compact kernels and actual raw regularity

The frequency projection is used only to estimate the difference of the same
uncut Hilbert adjoints. The raw Sobolev memberships and budgets are produced by
the actual retained adjoint estimates. In the fixed-reference application,
order one already controls the discarded frequency tail. This is the strong
adjoint term in the raw inverse perturbation identity for
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow RawCutoffBounds RawInputPartition CarrierSobolev
open ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- The actual uncut adjoints differ by the derived compact-frequency term and
two actual raw Sobolev tails. This is a strong estimate on the supplied datum,
not an operator-norm comparison of the moving uncut Fourier integral rows. -/
theorem norm_carrier_adjoint_sub_le_of_primitive_kernel (d d₀ : CarrierData n N)
    (T T₀ : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ w, T.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w)
    (hT₀ : ∀ w, T₀.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ w)
    (hd : ∀ u, MemLp (fun x ↦ carrierKernel d x u) 2 (volume : Measure (Torus n)))
    (hd₀ : ∀ u, MemLp (fun x ↦ carrierKernel d₀ x u) 2 (volume : Measure (Torus n)))
    {Z : Set CarrierParameter} (hZ : IsCompact Z)
    (hs : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (hs₀ : ∀ z ∉ Z, ∀ η, d₀.angularCutoff z η = 0)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hsmall : ∀ x u, ‖u.2‖ ≤ 4 * K → ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤ ε)
    (w : ComplexOutputL2 n) (s : ℕ)
    (hraw : MemRawSobolev s (T.adjoint w)) (hraw₀ : MemRawSobolev s (T₀.adjoint w)) :
    ‖T.adjoint w - T₀.adjoint w‖ ≤
      (K ^ s)⁻¹ * (rawSobolevNorm s (T.adjoint w) + rawSobolevNorm s (T₀.adjoint w)) +
        (ε * ‖w‖) * carrierBoxFactor (n := n) Z K := by
  let P := carrierSquaredCutoff (roundedCarrierMask n K)
  let u := T.adjoint w
  let v := T₀.adjoint w
  have htail : ‖u - P u‖ ≤ (K ^ s)⁻¹ * rawSobolevNorm s u :=
    carrierSquaredCutoff_tail_of_rawSobolev hK s (roundedCarrierMask n K) u
      (roundedCarrierMask_mem n K)
      ((roundedCarrierMask_eq_one (n := n) hK).mono fun _ hx ↦ fun _ hy ↦ hx hy) hraw
  have htail₀ : ‖v - P v‖ ≤ (K ^ s)⁻¹ * rawSobolevNorm s v :=
    carrierSquaredCutoff_tail_of_rawSobolev hK s (roundedCarrierMask n K) v
      (roundedCarrierMask_mem n K)
      ((roundedCarrierMask_eq_one (n := n) hK).mono fun _ hx ↦ fun _ hy ↦ hx hy) hraw₀
  have hcompact : ‖P (u - v)‖ ≤ (ε * ‖w‖) * carrierBoxFactor (n := n) Z K :=
    norm_roundedCarrier_adjoint_sub_le d d₀ T T₀ hT hT₀ hd hd₀ hZ hs hs₀ hK hε hsmall w
  calc
    ‖T.adjoint w - T₀.adjoint w‖ = ‖(u - P u) + P (u - v) - (v - P v)‖ := by
      congr 1
      rw [map_sub]
      dsimp only [u, v]
      abel
    _ ≤ (‖u - P u‖ + ‖P (u - v)‖) + ‖v - P v‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ((K ^ s)⁻¹ * rawSobolevNorm s u + (ε * ‖w‖) * carrierBoxFactor (n := n) Z K) +
        (K ^ s)⁻¹ * rawSobolevNorm s v :=
      add_le_add (add_le_add htail hcompact) htail₀
    _ = _ := by ring

end JanetCartan.PhysicalInverseContinuity
