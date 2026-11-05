module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.PeriodicMultiplier
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Complex coordinates of the actual real image inverse

Coordinate extraction commutes with the constructed real Bessel inverse of
`app:ch_background:defn:bg-row`. This supplies the Fourier bridge required by
the local comparison in `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory UnitAddTorus
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

section Coordinates
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

/-- Complexification of one actual real L² coordinate, with its original
measure (`app:ch_background:defn:bg-row`). -/
def complexifiedL2Coordinate (μ : Measure X) (i : I) :
    Lp (EuclideanSpace ℝ I) 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I ↦ ℝ) i)).compLpL 2 μ

/-- The coordinate map acts on representatives without changing measure
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_coe (μ : Measure X) (i : I)
    (u : Lp (EuclideanSpace ℝ I) 2 μ) :
    complexifiedL2Coordinate μ i u =ᵐ[μ] fun x ↦ (u x i : ℂ) :=
  (Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I ↦ ℝ) i)).coeFn_compLpL u

/-- Real vector equality can be checked in the complexified coordinates,
also for an empty coordinate type (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem eq_of_complexifiedL2Coordinate_eq (μ : Measure X)
    {u v : Lp (EuclideanSpace ℝ I) 2 μ}
    (h : ∀ i, complexifiedL2Coordinate μ i u = complexifiedL2Coordinate μ i v) : u = v := by
  apply Lp.ext
  have hc := ae_all_iff.mpr (fun i ↦ complexifiedL2Coordinate_coe μ i u)
  have hd := ae_all_iff.mpr (fun i ↦ complexifiedL2Coordinate_coe μ i v)
  filter_upwards [hc, hd] with x hx hy
  apply PiLp.ext
  intro i
  exact Complex.ofReal_injective ((hx i).symm.trans ((congrArg (fun f : Lp ℂ 2 μ ↦ f x)
    (h i)).trans (hy i)))

end Coordinates

variable {n : ℕ}

private theorem mFourierCoeff_congr_volume {f g : Torus n → ℂ}
    (h : f =ᵐ[volume] g) (k : Fin n → ℤ) : mFourierCoeff f k = mFourierCoeff g k := by
  simp only [mFourierCoeff_eq_volume_integral]
  exact integral_congr_ae (h.mono fun x hx ↦ by simp only [hx])

/-- The real Fourier pair encodes the complex coefficient of each coordinate
(`app:not:fourier`); consumed by `complexifiedL2Coordinate_periodicBesselInverse`. -/
theorem mFourierCoeff_complexifiedL2Coordinate
    (u : ContinuumRow.OutputL2 n) (i : Fin n) (k : Fin n → ℤ) :
    mFourierCoeff (complexifiedL2Coordinate volume i u) k =
      ⟨(periodicFourierCoeff u k).1 i, (periodicFourierCoeff u k).2 i⟩ := by
  rw [mFourierCoeff_congr_volume (complexifiedL2Coordinate_coe volume i u)]
  rw [mFourierCoeff_ofReal_memLp ((Lp.memLp u).eval_piLp i)]
  have h := periodicFourierCoeff_inner (Lp.memLp u) (EuclideanSpace.single i 1) k
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
    congrArg (fun p : ℝ × ℝ ↦ (⟨p.1, p.2⟩ : ℂ)) h

/-- Complex scalar Fourier action of every coordinate of the actual real
Bessel inverse (`app:ch_background:defn:bg-row`), proved from its real pairs. -/
theorem mFourierCoeff_complexifiedL2Coordinate_besselInverse
    (u : ContinuumRow.OutputL2 n) (i : Fin n) (k : Fin n → ℤ) :
    mFourierCoeff (complexifiedL2Coordinate volume i (ContinuumRow.periodicBesselInverse u)) k =
      (ContinuumRow.periodicBesselSymbol k : ℂ) *
        mFourierCoeff (complexifiedL2Coordinate volume i u) k := by
  rw [mFourierCoeff_complexifiedL2Coordinate, mFourierCoeff_complexifiedL2Coordinate]
  have h := ContinuumRow.periodicL2FourierCoeff_besselInverse u k
  have hr := congrArg (fun p : FourierPair (EuclideanSpace ℝ (Fin n)) ↦
    (WithLp.ofLp p).1 i) h
  have hi := congrArg (fun p : FourierPair (EuclideanSpace ℝ (Fin n)) ↦
    (WithLp.ofLp p).2 i) h
  apply Complex.ext
  · simpa using hr
  · simpa using hi

/-- The actual real Bessel inverse intertwines with the constructed complex
scalar operator, including dimension zero (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_periodicBesselInverse
    (u : ContinuumRow.OutputL2 n) (i : Fin n) :
    complexifiedL2Coordinate volume i (ContinuumRow.periodicBesselInverse u) =
      complexPeriodicBesselOperator (complexifiedL2Coordinate volume i u) := by
  apply complexPeriodicL2_eq_of_mFourierCoeff_eq
  intro k
  rw [mFourierCoeff_complexifiedL2Coordinate_besselInverse,
    mFourierCoeff_complexPeriodicBesselOperator]

end JanetCartan.ContinuumNormalReduction.ImageNormal
