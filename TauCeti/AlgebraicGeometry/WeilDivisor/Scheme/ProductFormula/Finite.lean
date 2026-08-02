/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of nonconstant morphisms from smooth proper curves

A proper morphism from an integral Noetherian smooth relative curve is locally quasi-finite as
soon as no fibre is the whole curve. Indeed, a fibre over a closed point is a proper closed
subset and hence finite. A fibre over a non-closed point contains no closed point, because proper
morphisms are closed, and therefore contains at most the generic point. Zariski's main theorem
then upgrades the morphism to a finite morphism.

Applied to the projective-line-valued morphism `[g : 1]`, this isolates the remaining
nonconstancy obligation in the geometric product-formula proof.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

/-- The global projective-line-valued morphism attached to a rational function on a proper
smooth relative curve is proper. -/
theorem isProper_rationalFunctionMorphism
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ) :
    IsProper (rationalFunctionMorphism K X f g) := by
  haveI : IsProper
      (rationalFunctionMorphism K X f g ≫ ProjectiveLine.structureMap K) := by
    rw [rationalFunctionMorphism_comp_structureMap]
    infer_instance
  exact IsProper.of_comp _ (ProjectiveLine.structureMap K)

/-- A proper morphism from an integral Noetherian smooth relative curve is locally quasi-finite
if none of its point fibres is the whole curve. -/
theorem locallyQuasiFinite_of_isProper_of_no_universal_fiber_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    {Y : Scheme.{u}} (φ : X ⟶ Y) [IsProper φ]
    (hfiber : ∀ y, φ ⁻¹' {y} ≠ Set.univ) :
    LocallyQuasiFinite φ := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton φ
  intro y
  by_cases hy : IsClosed ({y} : Set Y)
  · exact finite_closed_subset_of_smoothRelativeDimension_one
      K X f _ (hy.preimage φ.continuous) (hfiber y)
  · refine (Set.finite_singleton (genericPoint X)).subset ?_
    intro x hx
    by_contra hxGeneric
    have hxClosed : IsClosed ({x} : Set X) :=
      isClosed_singleton_of_ne_genericPoint_of_smoothRelativeDimension_one
        K X f x hxGeneric
    apply hy
    have hImage : IsClosed (φ '' ({x} : Set X)) :=
      φ.isClosedMap _ hxClosed
    have hxy : φ x = y := hx
    simpa [hxy] using hImage

/-- The rational-function morphism on a proper smooth curve is finite once no point fibre is the
whole curve. This is the exact finiteness adapter needed before comparing the zero and infinity
fibres. -/
theorem isFinite_rationalFunctionMorphism_of_no_universal_fiber
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hfiber : ∀ y, (rationalFunctionMorphism K X f g) ⁻¹' {y} ≠ Set.univ) :
    IsFinite (rationalFunctionMorphism K X f g) := by
  letI : IsProper (rationalFunctionMorphism K X f g) :=
    isProper_rationalFunctionMorphism K X f g
  letI : LocallyQuasiFinite (rationalFunctionMorphism K X f g) :=
    locallyQuasiFinite_of_isProper_of_no_universal_fiber_smoothRelativeDimension_one
      K X f (rationalFunctionMorphism K X f g) hfiber
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
