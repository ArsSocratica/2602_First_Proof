import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.Basic

/-!
# Problem 1 — Φ⁴₃ Measure Equivalence Under Shifts

**Answer: NO** — the measures are mutually singular.

Let 𝕋³ be the 3D unit torus and μ the Φ⁴₃ measure on 𝒟'(𝕋³).
For a smooth nonzero ψ : 𝕋³ → ℝ, the measures μ and (T_ψ)_* μ
are mutually singular, where T_ψ(u) = u + ψ.

## Formalization scope

The Φ⁴₃ measure is not yet formalized in Mathlib. We formalize the
abstract measure-theoretic shell of the proof:

Given two measures μ, ν on a measurable space, if there exists a
measurable set A with μ(A) = 1 and ν(A) = 0, then μ ⊥ ν.

The analytic content (construction of the separating set A_ψ, the
Barashkov-Gubinelli decomposition, and the variance estimates) is
beyond current Mathlib capabilities.

## References

- Hairer-Kusuoka-Nagoji, arXiv:2409.10037, Theorem 1.1
- Barashkov-Gubinelli, arXiv:2004.01513, Theorem 1.1
-/

open MeasureTheory

namespace FirstProof.P01

/-! ### Abstract measure-theoretic shell

The core logic: a separating set witnesses mutual singularity.
-/

/-- If there exists a measurable set A with μ(A) = μ(univ) and ν(A) = 0,
    then μ and ν are mutually singular. This is the abstract skeleton
    of the P01 proof. -/
theorem mutuallySingular_of_separating_set
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set α} (hA : MeasurableSet A)
    (hμA : μ Aᶜ = 0) (hνA : ν A = 0) :
    μ.MutuallySingular ν :=
  ⟨Aᶜ, hA.compl, hμA, by rwa [compl_compl]⟩

/-- The answer to Problem 1 is NO: the measures are mutually singular.
    We axiomatize the key analytic inputs and derive the conclusion. -/

-- Axiomatize the measurable space of distributions on 𝕋³
axiom DistSpace : Type
axiom instMeasurableDistSpace : MeasurableSpace DistSpace

attribute [instance] instMeasurableDistSpace

-- Axiomatize the Φ⁴₃ measure
axiom Phi43Measure : Measure DistSpace
axiom Phi43Measure_isFinite : IsFiniteMeasure Phi43Measure

attribute [instance] Phi43Measure_isFinite

-- Axiomatize the shift map
axiom shiftMap (ψ : DistSpace) : DistSpace → DistSpace
axiom shiftMap_measurable (ψ : DistSpace) : Measurable (shiftMap ψ)

-- The pushed-forward measure
noncomputable def shiftedMeasure (ψ : DistSpace) : Measure DistSpace :=
  Phi43Measure.map (shiftMap ψ)

-- Axiomatize: the shifted measure is finite
axiom shiftedMeasure_isFinite (ψ : DistSpace) :
  IsFiniteMeasure (shiftedMeasure ψ)

attribute [instance] shiftedMeasure_isFinite

-- Axiomatize the separating set A_ψ from Hairer-Kusuoka-Nagoji
-- (arXiv:2409.10037, Theorem 1.1)
axiom separatingSet (ψ : DistSpace) : Set DistSpace
axiom separatingSet_measurable (ψ : DistSpace) :
  MeasurableSet (separatingSet ψ)

-- Key analytic inputs (from the proof):
-- 1. μ(A_ψ) = 1, i.e., μ(A_ψᶜ) = 0
axiom mu_separatingSet_compl (ψ : DistSpace) :
  Phi43Measure (separatingSet ψ)ᶜ = 0

-- 2. (T_ψ)_* μ (A_ψ) = 0
axiom shifted_separatingSet (ψ : DistSpace) :
  (shiftedMeasure ψ) (separatingSet ψ) = 0

/-- **Main theorem (Problem 1):**
    The Φ⁴₃ measure and its translate under any (nonzero) smooth shift
    are mutually singular. -/
theorem phi43_shift_mutuallySingular (ψ : DistSpace) :
    Phi43Measure.MutuallySingular (shiftedMeasure ψ) :=
  mutuallySingular_of_separating_set
    Phi43Measure (shiftedMeasure ψ)
    (separatingSet_measurable ψ)
    (mu_separatingSet_compl ψ)
    (shifted_separatingSet ψ)

end FirstProof.P01
