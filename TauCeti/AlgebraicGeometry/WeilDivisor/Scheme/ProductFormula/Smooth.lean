/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Valuative
public import TauCeti.RingTheory.Smooth.DimensionOne
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Extending rational functions on smooth relative curves

Every stalk of an integral scheme smooth of relative dimension one over a field is a valuation
ring. Combining this local algebra with properness of the projective line shows that the rational
map `[g : 1]` attached to a nonzero rational function is defined everywhere.

This discharges the local-extension step in the geometric product-formula argument from
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/

public section

open CategoryTheory AlgebraicGeometry
open TauCeti.RingTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

/-- A stalk of an integral scheme smooth of relative dimension one over a field is a valuation
ring. -/
theorem valuationRing_stalk_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : X) : ValuationRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x
  have hfxU : f.base x ∈ U := e hx
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y (f.base x)] using hfxU
  subst U
  letI : Nonempty V := ⟨⟨x, hx⟩⟩
  letI : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, V) :=
    (f.appLE ⊤ V e).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), ⊤) Γ(X, V) := hstd.toAlgebra
  let q : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hx⟩
  exact valuationRing_of_isLocalizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
    Γ(Spec (.of K), ⊤) Γ(X, V) (X.presheaf.stalk x) q

/-- The projective-line-valued rational map `[g : 1]` on an integral smooth relative curve is
defined everywhere. -/
theorem rationalFunctionMap_domain_eq_top_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    (rationalFunctionMap K f g).domain = ⊤ := by
  apply rationalFunctionMap_domain_eq_top_of_valuationRings K f g
  exact fun x ↦ valuationRing_stalk_of_smoothRelativeDimension_one K X f x

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
