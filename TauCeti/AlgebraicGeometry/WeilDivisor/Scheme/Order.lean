/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Orders of rational functions at codimension-one points

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point. This file packages its restriction to
nonzero rational functions at a codimension-one point as an additive homomorphism

`SchemeWeilDivisor.orderAt x : Additive X.functionFieldˣ →+ ℤ`.

The global finiteness theorem `SchemeWeilDivisor.finite_support_orderAt` proves that a nonzero
rational function has nonzero order at only finitely many codimension-one points. It packages
the local maps into `SchemeWeilDivisor.orderSystem`, the scheme-theoretic order system used to
construct principal divisors.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the
"principal divisors" part of "Divisors on a curve". It reuses Mathlib's
`AlgebraicGeometry.Scheme.ord`, representation of a nonzero rational function by a unit on a
nonempty affine open, and finiteness of irreducible components in a Noetherian space; no external
formalization is vendored.
-/

public section

open AlgebraicGeometry TopologicalSpace Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

section LocalOrder

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of a nonzero rational function at a codimension-one point, as an additive
homomorphism from the additive form of the unit group of the function field. -/
noncomputable def orderAt (x : CodimensionOnePoint X) :
    Additive (X.functionFieldˣ) →+ ℤ :=
  MonoidHom.toAdditiveLeft
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (X.ordHom x x.property).toMonoidHom))

/-- Evaluating `orderAt` gives Mathlib's integer-valued order of vanishing. -/
@[simp]
lemma orderAt_apply (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x := by
  rw [X.ord_eq_unzero_ordHom x.property
    (Units.ne_zero (Additive.toMul f : X.functionFieldˣ))]
  simp only [orderAt, MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, WithZero.unitsWithZeroEquiv_apply]
  congr 1

end LocalOrder

/-- The codimension-one points outside a nonempty open of a Noetherian integral scheme are the
generic points of irreducible components of the closed complement. -/
private theorem codimensionOne_outside_open_finite
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : CodimensionOnePoint X | (x : X) ∉ U}.Finite := by
  let Z : Set X := (U : Set X)ᶜ
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  letI : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hgp : (genericPoints Z).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  rw [← Set.finite_coe_iff]
  let toGeneric : {x : CodimensionOnePoint X | (x : X) ∉ U} → genericPoints Z :=
    fun x ↦ ⟨⟨x.1.1, x.2⟩, by
      rw [genericPoints]
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro T hT hsub
      let p : Z := hT.genericPoint
      have hpGeneric : IsGenericPoint p (closure T) :=
        hT.isGenericPoint_genericPoint_closure
      have hxT : (⟨x.1.1, x.2⟩ : Z) ∈ T :=
        hsub (subset_closure (Set.mem_singleton _))
      have hpx : p ⤳ (⟨x.1.1, x.2⟩ : Z) :=
        hpGeneric.specializes (subset_closure hxT)
      have hxp : x.1.1 ≤ (p : X) := by
        rw [Scheme.le_iff_specializes]
        exact (subtype_specializes_iff p (⟨x.1.1, x.2⟩ : Z)).mp hpx
      letI : PartialOrder X := specializationOrder X
      have hp_eq_x : (p : X) = x.1.1 := by
        apply le_antisymm
        · by_contra hp_not_le
          have hxp_strict : x.1.1 < (p : X) := lt_of_le_not_ge hxp hp_not_le
          have hp_coheight_lt : coheight (p : X) < 1 :=
            (Order.coheight_eq_coe_iff.mp x.1.2).2.2 (p : X) hxp_strict
          have hp_coheight_zero : coheight (p : X) = 0 := by
            exact nonpos_iff_eq_zero.mp (by simpa using hp_coheight_lt)
          have hp_top : (p : X) = ⊤ :=
            (Order.coheight_eq_zero.mp hp_coheight_zero).eq_top
          have htopU : (⊤ : X) ∈ U := by
            change genericPoint X ∈ U
            exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
              (by simpa using (‹Nonempty U› : Nonempty U))
          exact p.2 (hp_top.symm ▸ htopU)
        · exact hxp
      intro y hy
      have hpy : p ⤳ y := hpGeneric.specializes (subset_closure hy)
      have hp_eq_z : p = (⟨x.1.1, x.2⟩ : Z) := Subtype.ext hp_eq_x
      rw [hp_eq_z] at hpy
      exact specializes_iff_mem_closure.mp hpy⟩
  exact @Finite.of_injective _ _ (Set.finite_coe_iff.mpr hgp) toGeneric (by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z ↦ (z.1 : X)) hxy)))

/-- A nonzero rational function on a Noetherian integral scheme has nonzero order at only
finitely many codimension-one points. -/
theorem finite_support_orderAt
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (g : Additive X.functionFieldˣ) :
    (Function.support fun x : CodimensionOnePoint X => orderAt x g).Finite := by
  let f : X.functionField := (Additive.toMul g : X.functionFieldˣ)
  have hf : f ≠ 0 := Units.ne_zero _
  obtain ⟨U, _, f', hU, hrepr, hf'⟩ := exists_isUnit_germ_eq X f hf
  letI : Nonempty U := hU
  refine (codimensionOne_outside_open_finite X U).subset ?_
  intro x hx
  change (x : X) ∉ U
  intro hxU
  apply hx
  change orderAt x g = 0
  rw [orderAt_apply]
  change X.ord f x = 0
  rw [← hrepr]
  exact X.ord_of_isUnit hf' hxU

/-- The scheme-theoretic order system on the codimension-one points of a Noetherian integral
scheme. -/
noncomputable def orderSystem
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    WeilDivisor.OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ) where
  ord := orderAt
  finite_support := finite_support_orderAt X

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
