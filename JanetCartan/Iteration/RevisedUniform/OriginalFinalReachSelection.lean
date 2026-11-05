module
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalReachTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles

/-! # The actual dimension-only initial reach

All six initial thresholds use the same original dimension-only geometry.
The source auxiliary gate is already included in the old reach. Neither the
finite-moment condition nor an accuracy threshold is put into this choice
(`new:sec:order-of-choices`, `main:prop:mean`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Elab Command
open JanetCartan.RevisedUniform.OriginalFinalReachTemplate
run_cmd liftTermElabM do publishThreshold 0
run_cmd liftTermElabM do publishThreshold 1
run_cmd liftTermElabM do publishThreshold 2
run_cmd liftTermElabM do publishThreshold 3
run_cmd liftTermElabM do publishThreshold 4
run_cmd liftTermElabM do publishThreshold 5
run_cmd liftTermElabM do publishSourceAuxPaid
end

@[expose] public noncomputable section
namespace JanetCartan.RevisedUniform.OriginalFinalReach

/-- Fixed before the metric, accuracy and finite source iteration. -/
def Tfinal (d : ℕ) (hn : 5 ≤ d+1) : ℝ :=
  initialReach (OriginalSelectedPrehistory.Tref d hn) (Scomp d hn)
    (Serror d hn) (Sbase d hn) (Sbuffer d hn) (SfullW d hn)

theorem oldTref_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) :
    OriginalSelectedPrehistory.Tref d hn ≤ Tfinal d hn := tref_le_initialReach

theorem two_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : 2 ≤ Tfinal d hn :=
  (OriginalSelectedPrehistory.two_le_Tref d hn).trans (oldTref_le_Tfinal d hn)

theorem Scomp_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : Scomp d hn ≤ Tfinal d hn :=
  scomp_le_initialReach

theorem Serror_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : Serror d hn ≤ Tfinal d hn :=
  serror_le_initialReach

theorem Sbase_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : Sbase d hn ≤ Tfinal d hn :=
  sbase_le_initialReach

theorem Sbuffer_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : Sbuffer d hn ≤ Tfinal d hn :=
  sbuffer_le_initialReach

theorem SfullW_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : SfullW d hn ≤ Tfinal d hn :=
  sfullW_le_initialReach

theorem Saux_le_Tfinal (d : ℕ) (hn : 5 ≤ d+1) : Saux d hn ≤ Tfinal d hn :=
  (Saux_le_oldTref d hn).trans (oldTref_le_Tfinal d hn)

/-- Every INITIAL gate follows at R₀. No later stage is used to pay an
initial condition, and no physical domain or cutoff is changed. -/
theorem initial_gates (d : ℕ) (hn : 5 ≤ d+1) {R₀ : ℝ}
    (hR : Tfinal d hn ≤ R₀) :
    2 ≤ R₀ ∧ OriginalSelectedPrehistory.Tref d hn ≤ R₀ ∧
      Scomp d hn ≤ R₀ ∧ Serror d hn ≤ R₀ ∧ Sbase d hn ≤ R₀ ∧
      Sbuffer d hn ≤ R₀ ∧ SfullW d hn ≤ R₀ ∧ Saux d hn ≤ R₀ :=
  ⟨(two_le_Tfinal d hn).trans hR, (oldTref_le_Tfinal d hn).trans hR,
    (Scomp_le_Tfinal d hn).trans hR, (Serror_le_Tfinal d hn).trans hR,
    (Sbase_le_Tfinal d hn).trans hR, (Sbuffer_le_Tfinal d hn).trans hR,
    (SfullW_le_Tfinal d hn).trans hR, (Saux_le_Tfinal d hn).trans hR⟩
end JanetCartan.RevisedUniform.OriginalFinalReach
end
#print axioms JanetCartan.RevisedUniform.OriginalFinalReach.Tfinal
#print axioms JanetCartan.RevisedUniform.OriginalFinalReach.initial_gates
