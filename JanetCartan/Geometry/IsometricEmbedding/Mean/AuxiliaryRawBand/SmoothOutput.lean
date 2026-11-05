module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Geometry

/-!
# Smooth full strain and complete auxiliary output

Smoothness in `app:ch_background:prop:bg-mixed-physical` is established for the
fixed representatives and arbitrary raw L² inputs. No Sobolev order enters
these definitions.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n N : ℕ}

private def tensorOfEntries (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- The full periodic strain expression is smooth from primitive smooth
Christoffel coefficients and the final cutoff. Both cutoff-derivative terms
are retained (`app:ch_background:prop:bg-mixed-physical`). -/
theorem isSmoothPeriodic_periodicFullStrain
    (χ : Torus n → ℝ) (hχ : IsSmoothPeriodic χ)
    (Γ : Fin n → Fin n → Fin n → Torus n → ℝ)
    (hΓ : ∀ i j k, IsSmoothPeriodic (Γ i j k))
    (u : Torus n → Euclidean n) (hu : IsSmoothPeriodic u) :
    IsSmoothPeriodic (periodicFullStrain χ Γ u) := by
  have hv (j : Fin n) := hu.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j)
  have hd (i j : Fin n) := (hu.coordinateDeriv i).comp_clm
    (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j)
  constructor
  · apply (tensorOfEntries n).continuous.comp
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hχ.1.mul (((hd i j).1.add (hd j i).1).div_const 2 |>.sub
      (continuous_finsetSum _ fun k _ ↦ (hΓ i j k).1.mul (hv k).1))).add
      (((hχ.coordinateDeriv i).1.mul (hv j).1 |>.add
        ((hχ.coordinateDeriv j).1.mul (hv i).1)).div_const 2)
  · apply (tensorOfEntries n).contDiff.comp
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (hχ.2.mul (((hd i j).2.add (hd j i).2).div_const 2 |>.sub
      (ContDiff.sum fun k _ ↦ (hΓ i j k).2.mul (hv k).2))).add
      (((hχ.coordinateDeriv i).2.mul (hv j).2 |>.add
        ((hχ.coordinateDeriv j).2.mul (hv i).2)).div_const 2)

/-- Smoothness of the full geometric strain, on the original open immersion
domain, for the same raw field (`app:ch_background:prop:bg-mixed-physical`). -/
theorem contDiffOn_physicalStrain
    {G : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W) (himm : IsImmersionOn G W)
    {χout : Euclidean n → ℝ} (hout : ContDiffOn ℝ ∞ χout W)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) :
    ContDiffOn ℝ ∞ (physicalStrain G χout χsrc K h) W := by
  have hv := contDiffOn_physicalField hW hG himm hout χsrc hsrc K h
  apply (tensorOfEntries n).contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact ((contDiffOn_partialDeriv hW hG i).inner ℝ
    (contDiffOn_partialDeriv hW hv j)).add
    ((contDiffOn_partialDeriv hW hv i).inner ℝ (contDiffOn_partialDeriv hW hG j))

/-- The reduced periodic coefficient formula is smooth, retaining its
connection term (`app:ch_waves:eq:reduced-symbol`). -/
theorem isSmoothPeriodic_reducedPeriodicFormula
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (u : Torus n → Euclidean n) (hu : IsSmoothPeriodic u) :
    IsSmoothPeriodic (reducedPeriodicFormula c u) := by
  have hv (j : Fin n) := hu.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j)
  have hd (i j : Fin n) := (hu.coordinateDeriv i).comp_clm
    (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j)
  constructor
  · apply Continuous.add
    · exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun i _ ↦
        continuous_finsetSum _ fun k _ ↦
          ((hc (.inl (a, i, k))).1.mul (hd a k).1).smul continuous_const
    · exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun k _ ↦
        ((hc (.inr (i, k))).1.mul (hv k).1).smul continuous_const
  · apply ContDiff.add
    · exact ContDiff.sum fun a _ ↦ ContDiff.sum fun i _ ↦
        ContDiff.sum fun k _ ↦
          ((hc (.inl (a, i, k))).2.mul (hd a k).2).smul contDiff_const
    · exact ContDiff.sum fun i _ ↦ ContDiff.sum fun k _ ↦
        ((hc (.inr (i, k))).2.mul (hv k).2).smul contDiff_const

/-- Smoothness of the actual image representative after both ordered cutoffs
(`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem isSmoothPeriodic_smoothImageOutput
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    IsSmoothPeriodic (smoothImageOutput c χmeas χsrc K h) := by
  have hr := isSmoothPeriodic_reducedPeriodicFormula c hc _
    (isSmoothPeriodic_rawCovector χsrc hs K h)
  exact ⟨hm.1.smul hr.1, hm.2.smul hr.2⟩

/-- Smoothness of the COMPLETE original auxiliary output, including the
original exterior channel (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem isSmoothPeriodic_smoothAuxiliaryOutput
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)) (K : ℝ) (him hout : OutputL2 n) :
    IsSmoothPeriodic (smoothAuxiliaryOutput c χmeas χsrc ψ K him hout) := by
  have hi := isSmoothPeriodic_smoothImageOutput c hc χmeas χsrc hm hs K him
  have he := isSmoothPeriodic_exteriorOutput ψ hψ K hout
  exact ⟨hi.1.add he.1, hi.2.add he.2⟩

end JanetCartan.AuxiliaryRawBand
