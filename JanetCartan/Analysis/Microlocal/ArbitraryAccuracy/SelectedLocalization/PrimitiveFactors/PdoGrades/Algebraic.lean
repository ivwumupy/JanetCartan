module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.JointInverse
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.ConicInverse
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.FieldProfile
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SelectedInverse
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.PhysicalProfiles

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.JointProfiles

/-!
# Joint and physical grades of the complete selected algebraic residual

`exists_selected_algebraic_joint_grades` supplies one profile for both
branch-three symbol inputs of `CompleteFactor`. It retains the exact doubled
threshold, entire source product, full physical action including `B`, both
physical masks, and literal adjunction. The comparable estimate is on the
actual `Kpdo`, with order minus one; the physical estimate has the required
negative `branchRadius` weight. The original reserve `Rstar ≥ 1` absorbs the
first coefficient jet, so the slow-scale offset is zero.

The retained `RootBuffer` and constant-field complement certificates produce
the actual compact inverse domains. The final result assumes no inverse
budget or joint-symbol estimate. `selected_algebraic_residual_amplitude_eq`
identifies the same symbol in the finite direct four-symbol ledger. Combining
this profile with the other two branches into `Dpdo` belongs to the parent.
Sources: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`.
-/
