/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Flat
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Residue degrees in the zero and infinity fibres

This file compares residue degree over the ground field with residue degree along the
projective-line morphism attached to a rational function.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

/-- The zero point of the projective line has residue degree one over the base field. -/
@[simp]
theorem ProjectiveLine.residueDegree_structureMap_zeroPoint
    (K : Type u) [Field K] :
    (ProjectiveLine.structureMap K).residueDegree (ProjectiveLine.zeroPoint K) = 1 := by
  rw [← ProjectiveLine.zeroSection_closedPoint K]
  exact residueDegree_eq_one_of_section
    (ProjectiveLine.zeroSection_comp_structureMap K) (IsLocalRing.closedPoint K)

/-- The point at infinity of the projective line has residue degree one over the base field. -/
@[simp]
theorem ProjectiveLine.residueDegree_structureMap_infinityPoint
    (K : Type u) [Field K] :
    (ProjectiveLine.structureMap K).residueDegree (ProjectiveLine.infinityPoint K) = 1 := by
  rw [← ProjectiveLine.infinitySection_closedPoint K]
  exact residueDegree_eq_one_of_section
    (ProjectiveLine.infinitySection_comp_structureMap K) (IsLocalRing.closedPoint K)

/-- Above zero, residue degree over the base field equals residue degree along the
rational-function morphism. -/
theorem residueDegree_eq_rationalFunctionMorphism_of_eq_zeroPoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : X)
    (hx : rationalFunctionMorphism K X f g x = ProjectiveLine.zeroPoint K) :
    f.residueDegree x = (rationalFunctionMorphism K X f g).residueDegree x := by
  let φ := rationalFunctionMorphism K X f g
  calc
    f.residueDegree x = (φ ≫ ProjectiveLine.structureMap K).residueDegree x :=
      congrArg (fun ψ : X ⟶ Spec (.of K) ↦ ψ.residueDegree x)
        (rationalFunctionMorphism_comp_structureMap K X f g).symm
    _ = (ProjectiveLine.structureMap K).residueDegree (φ x) * φ.residueDegree x :=
      residueDegree_comp φ (ProjectiveLine.structureMap K) x
    _ = φ.residueDegree x := by
      rw [hx, ProjectiveLine.residueDegree_structureMap_zeroPoint, one_mul]

/-- Above infinity, residue degree over the base field equals residue degree along the
rational-function morphism. -/
theorem residueDegree_eq_rationalFunctionMorphism_of_eq_infinityPoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : X)
    (hx : rationalFunctionMorphism K X f g x = ProjectiveLine.infinityPoint K) :
    f.residueDegree x = (rationalFunctionMorphism K X f g).residueDegree x := by
  let φ := rationalFunctionMorphism K X f g
  calc
    f.residueDegree x = (φ ≫ ProjectiveLine.structureMap K).residueDegree x :=
      congrArg (fun ψ : X ⟶ Spec (.of K) ↦ ψ.residueDegree x)
        (rationalFunctionMorphism_comp_structureMap K X f g).symm
    _ = (ProjectiveLine.structureMap K).residueDegree (φ x) * φ.residueDegree x :=
      residueDegree_comp φ (ProjectiveLine.structureMap K) x
    _ = φ.residueDegree x := by
      rw [hx, ProjectiveLine.residueDegree_structureMap_infinityPoint, one_mul]

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
