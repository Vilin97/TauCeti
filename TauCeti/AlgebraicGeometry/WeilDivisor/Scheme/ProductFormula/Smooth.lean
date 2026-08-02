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

/-- The everywhere-defined morphism `X ⟶ ℙ¹_K` represented by the rational function
`[g : 1]` on an integral smooth relative curve. -/
noncomputable def rationalFunctionMorphism
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) : X ⟶ ProjectiveLine.scheme K :=
  let φ := rationalFunctionMap K f g
  let h : φ.domain = ⊤ :=
    rationalFunctionMap_domain_eq_top_of_smoothRelativeDimension_one K X f g
  X.topIso.inv ≫ (X.isoOfEq h).inv ≫ φ.toPartialMap.hom

/-- The global rational-function morphism represents the rational map from which it was
constructed. -/
@[simp]
theorem rationalFunctionMorphism_toRationalMap
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    (rationalFunctionMorphism K X f g).toRationalMap = rationalFunctionMap K f g := by
  let φ := rationalFunctionMap K f g
  let h : φ.domain = ⊤ :=
    rationalFunctionMap_domain_eq_top_of_smoothRelativeDimension_one K X f g
  have he : (X.isoOfEq h).inv = (X.isoOfEq h.symm).hom := by
    rw [← cancel_mono φ.domain.ι]
    simp
  change (X.topIso.inv ≫ (X.isoOfEq h).inv ≫ φ.toPartialMap.hom).toRationalMap = φ
  calc
    _ = φ.toPartialMap.toRationalMap := by
      apply congrArg Scheme.PartialMap.toRationalMap
      apply Scheme.PartialMap.ext _ _ h.symm
      change X.topIso.hom ≫
          (X.topIso.inv ≫ (X.isoOfEq h).inv ≫ φ.toPartialMap.hom) =
        (X.isoOfEq h.symm).hom ≫ φ.toPartialMap.hom
      simp only [Iso.hom_inv_id_assoc, he]
    _ = φ := φ.toRationalMap_toPartialMap

/-- Restriction of the global rational-function morphism to the function field is the point
`[g : 1]`. -/
@[simp]
theorem rationalFunctionMorphism_fromFunctionField
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    (rationalFunctionMorphism K X f g).toPartialMap.fromFunctionField =
      rationalFunctionGenericMorphism K f g := by
  change (rationalFunctionMorphism K X f g).toRationalMap.fromFunctionField = _
  rw [rationalFunctionMorphism_toRationalMap, rationalFunctionMap_fromFunctionField]

/-- The global rational-function morphism is a morphism over `Spec K`. -/
@[simp]
theorem rationalFunctionMorphism_comp_structureMap
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    rationalFunctionMorphism K X f g ≫ ProjectiveLine.structureMap K = f := by
  have hr :
      (rationalFunctionMorphism K X f g ≫
          ProjectiveLine.structureMap K).toRationalMap = f.toRationalMap := by
    calc
      _ = (rationalFunctionMorphism K X f g).toRationalMap.compHom
          (ProjectiveLine.structureMap K) := rfl
      _ = (rationalFunctionMap K f g).compHom
          (ProjectiveLine.structureMap K) := by
        rw [rationalFunctionMorphism_toRationalMap]
      _ = f.toRationalMap := rationalFunctionMap_comp_structureMap K f g
  have he := Scheme.PartialMap.toRationalMap_eq_iff.mp hr
  have hhom :=
    (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := ⊤_ Scheme)).mp he
  change X.topIso.hom ≫
      (rationalFunctionMorphism K X f g ≫ ProjectiveLine.structureMap K) =
    X.topIso.hom ≫ f at hhom
  apply (cancel_epi X.topIso.hom).mp
  exact hhom

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
