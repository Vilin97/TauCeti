/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ResidueDegree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Relative degrees of scheme-theoretic Weil divisors

This file specializes `WeilDivisor.weightedDegree` to the residue-degree weights associated to a
scheme morphism. For a curve over a field, applied to its structure morphism, this is the divisor
degree `Σ_x [κ(x) : k] · ord_x`.

The composition formula records how these weights change through successive scheme morphisms.
This supplies the residue-field-weighted divisor degree required in Layer A of the Jacobian
challenge roadmap.

For the product formula on a proper curve, this file also supplies the exact finite-sum normal
form and the first geometric case: a rational function extending to a global section has zero
principal divisor. On a proper integral scheme every nonzero global section is a unit, so the
remaining product-formula obligation consists precisely of rational functions which do not
extend globally.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X Y Z : Scheme.{u}}

noncomputable section

/-- The degree of a scheme-theoretic Weil divisor weighted by the residue degrees of `f`. -/
def relativeDegree (f : X ⟶ Y) : SchemeWeilDivisor X →+ ℤ :=
  WeilDivisor.weightedDegree fun x : CodimensionOnePoint X ↦ (f.residueDegree x : ℤ)

/-- The relative degree is the finite sum of coefficients times residue degrees. -/
lemma relativeDegree_apply (f : X ⟶ Y) (D : SchemeWeilDivisor X) :
    relativeDegree f D = D.sum fun x n ↦ n * (f.residueDegree x : ℤ) := by
  rw [relativeDegree, WeilDivisor.weightedDegree_apply]

/-- A prime divisor has relative degree equal to the residue degree of its generic point. -/
@[simp]
lemma relativeDegree_ofPoint (f : X ⟶ Y) (x : CodimensionOnePoint X) :
    relativeDegree f (WeilDivisor.ofPoint x) = (f.residueDegree x : ℤ) := by
  simp [relativeDegree]

/-- Relative degree along a composite uses the product of the successive residue degrees. -/
@[simp]
lemma relativeDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (D : SchemeWeilDivisor X) :
    relativeDegree (f ≫ g) D =
      WeilDivisor.weightedDegree
        (fun x : CodimensionOnePoint X ↦
          (g.residueDegree (f x) : ℤ) * f.residueDegree x) D := by
  simp only [relativeDegree, residueDegree_comp, Nat.cast_mul]

section ProductFormulaBoundary

variable [IsIntegral X] [IsNoetherian X]

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The relative degree of a principal divisor for the concrete scheme order system is the
finite residue-degree-weighted sum of its geometric orders of vanishing. This is the exact
finite-sum target of the product formula. -/
lemma relativeDegree_orderSystem_principalDivisor_apply (f : X ⟶ Y)
    (g : Additive X.functionFieldˣ) :
    relativeDegree f ((orderSystem X).principalDivisor g) =
      ∑ x ∈ ((orderSystem X).principalDivisor g).support,
        orderAt x g * (f.residueDegree x : ℤ) := by
  rw [relativeDegree_apply]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro x _
  change WeilDivisor.coeff ((orderSystem X).principalDivisor g) x * _ = _
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor, orderSystem_ord]

/-- The weighted-degree-zero assertion for the concrete scheme order system is equivalent to
the explicit residue-degree-weighted finite sum. This exposes the mathematical product formula
without any abstract order-system wrapper. -/
lemma orderSystem_isWeightedDegreeZero_iff (f : X ⟶ Y) :
    (orderSystem X).IsWeightedDegreeZero (fun x ↦ (f.residueDegree x : ℤ)) ↔
      ∀ g : Additive X.functionFieldˣ,
        ∑ x ∈ ((orderSystem X).principalDivisor g).support,
          orderAt x g * (f.residueDegree x : ℤ) = 0 := by
  constructor
  · intro h g
    have hg := h g
    change relativeDegree f ((orderSystem X).principalDivisor g) = 0 at hg
    rw [relativeDegree_orderSystem_principalDivisor_apply] at hg
    exact hg
  · intro h g
    change relativeDegree f ((orderSystem X).principalDivisor g) = 0
    rw [relativeDegree_orderSystem_principalDivisor_apply]
    exact h g

/-- Transport the geometric weighted-degree-zero theorem to any abstract order system whose
order homomorphisms are exactly Mathlib's scheme-theoretic orders of vanishing. This is the
permanent adapter consumed by the proper-curve Challenge contract; finite-support proof fields
need not be propositionally identified. -/
lemma isWeightedDegreeZero_of_ord_eq_orderAt
    (f : X ⟶ Y)
    (S : WeilDivisor.OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = orderAt)
    (hConcrete : (orderSystem X).IsWeightedDegreeZero
      (fun x ↦ (f.residueDegree x : ℤ))) :
    S.IsWeightedDegreeZero (fun x ↦ (f.residueDegree x : ℤ)) := by
  have hOrders : S.ord = (orderSystem X).ord := by
    funext x
    rw [hord, orderSystem_ord]
  exact (S.isWeightedDegreeZero_congr_ord hOrders _).mpr hConcrete

/-- A rational function represented by a unit on an open neighbourhood has order zero at every
codimension-one point of that neighbourhood. -/
lemma orderAt_eq_zero_of_eq_germToFunctionField
    (U : X.Opens) [Nonempty U] {a : Γ(X, U)} (ha : IsUnit a)
    (x : CodimensionOnePoint X) (hx : x.1 ∈ U)
    (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField U a) :
    orderAt x g = 0 := by
  rw [orderAt_apply, hg]
  exact X.ord_of_isUnit ha hx

/-- A rational function which is represented by a unit on all of an integral Noetherian scheme
has zero principal divisor for the concrete scheme order system. -/
lemma principalDivisor_eq_zero_of_eq_germToFunctionField_top
    {a : Γ(X, ⊤)} (ha : IsUnit a) (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField ⊤ a) :
    (orderSystem X).principalDivisor g = 0 := by
  ext x
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.coeff_zero]
  rw [orderSystem_ord]
  exact orderAt_eq_zero_of_eq_germToFunctionField (X := X) ⊤ ha x trivial g hg

/-- On a proper integral scheme, every rational function extending to a global section has
zero principal divisor. Properness is used through the theorem that the global-section ring of
an integral universally closed scheme over a field is a field. -/
lemma principalDivisor_eq_zero_of_proper_of_eq_germToFunctionField_top
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f]
    {a : Γ(X, ⊤)} (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField ⊤ a) :
    (orderSystem X).principalDivisor g = 0 := by
  letI : Field Γ(X, ⊤) := (isField_of_universallyClosed K f).toField
  have ha : a ≠ 0 := by
    intro ha
    have hgzero : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) = 0 := by
      rw [hg, ha, map_zero]
    exact Units.ne_zero (Additive.toMul g) hgzero
  exact principalDivisor_eq_zero_of_eq_germToFunctionField_top (X := X)
    (isUnit_iff_ne_zero.mpr ha) g hg

/-- Consequently, every globally represented rational function on a proper integral scheme has
relative degree zero for any target morphism. This is the global-function case of the proper
curve product formula, stated using the concrete order system from `Scheme.Order`. -/
lemma relativeDegree_principalDivisor_eq_zero_of_proper_of_eq_germToFunctionField_top
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f]
    {a : Γ(X, ⊤)} (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField ⊤ a) :
    relativeDegree f ((orderSystem X).principalDivisor g) = 0 := by
  rw [principalDivisor_eq_zero_of_proper_of_eq_germToFunctionField_top
    (X := X) K f g hg, map_zero]

/-- To prove the product formula on a proper integral scheme it is enough to treat rational
functions which do not extend to a global section. The complementary case is discharged by
`principalDivisor_eq_zero_of_proper_of_eq_germToFunctionField_top`; no product-formula content
is placed in an assumption-bearing structure. -/
lemma orderSystem_isWeightedDegreeZero_of_nonGlobal
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (h : ∀ g : Additive X.functionFieldˣ,
      (¬ ∃ a : Γ(X, ⊤),
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
          X.germToFunctionField ⊤ a) →
      relativeDegree f ((orderSystem X).principalDivisor g) = 0) :
    (orderSystem X).IsWeightedDegreeZero (fun x ↦ (f.residueDegree x : ℤ)) := by
  intro g
  change relativeDegree f ((orderSystem X).principalDivisor g) = 0
  by_cases hg : ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a
  · obtain ⟨a, ha⟩ := hg
    exact relativeDegree_principalDivisor_eq_zero_of_proper_of_eq_germToFunctionField_top
      (X := X) K f g ha
  · exact h g hg

end ProductFormulaBoundary

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
