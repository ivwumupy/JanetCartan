module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardMassStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardMassStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-!
# Exact actual full-source unweighted mass

Apply the native-first input scalar estimate and the SAME all-order common
Picard profile at n+1. The exponent is natural subtraction and n+1≤s0, so
M_N=Cmass44*D_N(n+1) gives exactly M_N*h. Every analytic input is instantiated
from the actual full forcing; only the original numerical auxiliary reach is
retained (`main:eq:primary-fixed-scales`).
-/
set_option warningAsError true
set_option Elab.async false
prove_actual_full_source_mass 1
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.input_fourierMass_le
