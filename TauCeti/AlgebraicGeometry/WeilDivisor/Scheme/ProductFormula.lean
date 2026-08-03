/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree.Basic
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Rational maps attached to rational functions

For an integral scheme `X` over a field `K`, a nonzero rational function gives the function-field
point `[g : 1]` of the projective line. This file proves that the point respects the base-field
maps and spreads it out to a rational map `X ⤏ ℙ¹_K`.

The construction is the rational-map input to the geometric proof of the product formula in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve". The subsequent
extension across a regular curve and the comparison of the zero and infinity fibres remain
separate mathematical steps.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- On spectra, the base-field map to the function field is the structure morphism restricted
to the generic point. -/
lemma specMap_baseFieldToFunctionField (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) :
    Spec.map (CommRingCat.ofHom (baseFieldToFunctionField K f)) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [← cancel_mono (Spec (.of K)).toSpecΓ]
  rw [Category.assoc, Scheme.toSpecΓ_naturality]
  rw [Scheme.toSpecΓ_naturality]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  rw [Scheme.ΓSpecIso_naturality]
  ext r
  simp [baseFieldToFunctionField]

/-- The function-field point `[g : 1]` of `ℙ¹_K` is compatible with the structure morphism of
`X` at its generic point. -/
lemma rationalFunctionGenericMorphism_comp_structureMap (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    rationalFunctionGenericMorphism K f g ≫ ProjectiveLine.structureMap K =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  change ProjectiveLine.ofElement K X.functionField (baseFieldToFunctionField K f)
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ≫
      ProjectiveLine.structureMap K = _
  rw [ProjectiveLine.ofElement_comp_structureMap]
  exact specMap_baseFieldToFunctionField K f

/-- The rational map over `K` associated to a nonzero rational function, bundled together with
its equality over `Spec K`. -/
noncomputable def rationalFunctionMapOver (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    { φ : X ⤏ ProjectiveLine.scheme K //
      φ.compHom (ProjectiveLine.structureMap K) = f.toRationalMap } :=
  Scheme.RationalMap.equivFunctionField f (ProjectiveLine.structureMap K) <|
    ⟨rationalFunctionGenericMorphism K f g,
      rationalFunctionGenericMorphism_comp_structureMap K f g⟩

/-- The rational map `X ⤏ ℙ¹_K` associated to a nonzero rational function. -/
noncomputable def rationalFunctionMap (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    X ⤏ ProjectiveLine.scheme K :=
  (rationalFunctionMapOver K f g).1

/-- The rational-function map is a rational map over `K`. -/
@[simp]
lemma rationalFunctionMap_comp_structureMap (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    (rationalFunctionMap K f g).compHom (ProjectiveLine.structureMap K) =
      f.toRationalMap :=
  (rationalFunctionMapOver K f g).2

/-- Restricting the rational-function map back to the function field recovers `[g : 1]`. -/
@[simp]
lemma rationalFunctionMap_fromFunctionField (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    (rationalFunctionMap K f g).fromFunctionField =
      rationalFunctionGenericMorphism K f g := by
  exact congrArg Subtype.val
    ((Scheme.RationalMap.equivFunctionField f (ProjectiveLine.structureMap K)).left_inv
      ⟨rationalFunctionGenericMorphism K f g,
        rationalFunctionGenericMorphism_comp_structureMap K f g⟩)

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
