/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.DegreeZero
public import TauCeti.AlgebraicGeometry.WeilDivisor.PicZeroQuotient

/-!
# Picard-group consumer of the smooth proper curve product formula

The checked product formula supplies the weighted-degree-zero hypothesis needed to identify
residue-degree-zero divisors modulo principal divisors with the abstract `Pic⁰` subgroup of the
divisor class group.  This file is deliberately downstream of the geometric proof, so changes to
the product-formula interface are checked against a concrete Picard-theoretic consumer.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

/-- The quotient of residue-degree-zero divisors by principal divisors on a smooth proper curve
is the abstract residue-degree-zero Picard group. -/
noncomputable def properCurveDegreeZeroQuotientEquivPicZero
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f] :
    WeilDivisor.weightedDegreeZeroSubgroup
        (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ)) ⧸
      (orderSystem X).principalSubgroupOfWeightedDegreeZero
        (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ)) ≃+
      (orderSystem X).picZero
        (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ))
        (divisorProductFormula K X f) :=
  (orderSystem X).weightedDegreeZeroQuotientEquivPicZero
    (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ))
    (divisorProductFormula K X f)

/-- The Picard consumer sends a degree-zero divisor to its ordinary divisor class. -/
@[simp]
lemma coe_properCurveDegreeZeroQuotientEquivPicZero_mk
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (D : WeilDivisor.weightedDegreeZeroSubgroup
      (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ))) :
    ((properCurveDegreeZeroQuotientEquivPicZero K X f
      (QuotientAddGroup.mk D) :
        (orderSystem X).picZero
          (fun x : CodimensionOnePoint X ↦ (f.residueDegree x.1 : ℤ))
          (divisorProductFormula K X f)) :
      (orderSystem X).ClassGroup) =
        (orderSystem X).divisorClass (D : WeilDivisor (CodimensionOnePoint X)) := by
  exact (orderSystem X).coe_weightedDegreeZeroQuotientEquivPicZero_mk
    (divisorProductFormula K X f) D

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
