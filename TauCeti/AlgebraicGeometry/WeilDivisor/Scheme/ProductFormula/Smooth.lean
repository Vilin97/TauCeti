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
ring, and its non-generic stalks are discrete valuation rings. Consequently every non-generic
point has codimension one and is closed, so proper closed subsets of a Noetherian relative curve
are finite. Combining this local algebra with properness of the projective line shows that the
rational map `[g : 1]` attached to a nonzero rational function is defined everywhere.

This discharges the local-extension step in the geometric product-formula argument from
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/

public section

open CategoryTheory AlgebraicGeometry Order TopologicalSpace
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

/-- The stalk at any non-generic point of an integral scheme smooth of relative dimension one
over a field is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_ne_genericPoint_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : PartialOrder X := specializationOrder X
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : ValuationRing (X.presheaf.stalk x) :=
    valuationRing_stalk_of_smoothRelativeDimension_one K X f x
  have hfield : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    letI : Field (X.presheaf.stalk x) := h.toField
    have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) := inferInstance
    rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight] at hdim
    have hxzero : coheight x = 0 := by
      exact le_antisymm (by exact_mod_cast hdim) (by simp)
    exact hx ((coheight_eq_zero.mp hxzero).eq_of_le (genericPoint_specializes x))
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hfield).out 1 0).mp
    (show ValuationRing (X.presheaf.stalk x) from inferInstance)

/-- A codimension-one stalk of an integral scheme smooth of relative dimension one over a field
is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x.1) := by
  apply isDiscreteValuationRing_stalk_of_ne_genericPoint_of_smoothRelativeDimension_one
    K X f x.1
  intro hx
  have hco := x.2
  rw [hx] at hco
  change coheight (⊤ : X) = 1 at hco
  norm_num at hco

/-- Every non-generic point of an integral smooth relative curve has codimension one. -/
theorem coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : x ≠ genericPoint X) :
    coheight x = 1 := by
  letI : PartialOrder X := specializationOrder X
  letI : OrderTop X :=
    { top := genericPoint X
      le_top a := genericPoint_specializes a }
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_ne_genericPoint_of_smoothRelativeDimension_one
      K X f x hx
  have hdim := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- Every non-generic point of an integral smooth relative curve is a closed point. -/
theorem isClosed_singleton_of_ne_genericPoint_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  letI : PartialOrder X := specializationOrder X
  letI : OrderTop X :=
    { top := genericPoint X
      le_top a := genericPoint_specializes a }
  have hxone : coheight x = 1 :=
    coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one K X f x hx
  have hxMin : IsMin x := by
    intro y hy
    apply le_of_eq
    by_contra hxy
    have hyx : y < x := lt_of_le_of_ne' hy hxy
    have hyne : y ≠ genericPoint X := by
      intro hygen
      subst y
      exact hx (le_antisymm (genericPoint_specializes x) hy)
    have hyone : coheight y = 1 :=
      coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one K X f y hyne
    have hlt : coheight x < coheight y := coheight_strictAnti hyx (by simp [hxone])
    rw [hxone, hyone] at hlt
    exact lt_irrefl _ hlt
  rw [← closure_eq_iff_isClosed, closure_singleton_eq_Iic, hxMin.Iic_eq]

/-- Every proper closed subset of an integral Noetherian smooth relative curve is finite. -/
theorem finite_closed_subset_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (Z : Set X) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    Z.Finite := by
  letI : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hgp : (genericPoints Z).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have hgpClosed : IsClosed (genericPoints Z) := by
    rw [← (genericPoints Z).biUnion_of_singleton]
    refine hgp.isClosed_biUnion fun z _ ↦ ?_
    have hzGeneric : (z : X) ≠ genericPoint X := by
      intro heq
      have hmem : genericPoint X ∈ Z := heq ▸ z.property
      have hsub : (Set.univ : Set X) ⊆ Z :=
        ((genericPoint_spec X).mem_closed_set_iff hZ).mp hmem
      exact hZne (Set.eq_univ_of_univ_subset hsub)
    have hclosedX : IsClosed ({(z : X)} : Set X) :=
      isClosed_singleton_of_ne_genericPoint_of_smoothRelativeDimension_one
        K X f z hzGeneric
    convert hclosedX.preimage continuous_subtype_val using 1
    ext w
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · exact fun h ↦ Subtype.ext h
  have hgpEq : genericPoints Z = Set.univ := by
    rw [← hgpClosed.closure_eq, genericPoints.closure]
  apply Set.finite_coe_iff.mpr
  exact Set.finite_univ_iff.mp (by
    rw [← hgpEq]
    exact hgp)

/-- On a smooth relative curve, a rational function represented by a nonzero element of a
codimension-one stalk has order equal to the finite order of that stalk element. -/
theorem orderAt_eq_ord_stalk_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X)
    {a : X.presheaf.stalk x.1} (ha : a ≠ 0)
    (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk x.1) X.functionField a) :
    orderAt x g = (Ring.ord (X.presheaf.stalk x.1) a).toNat := by
  letI : IsDiscreteValuationRing (X.presheaf.stalk x.1) :=
    isDiscreteValuationRing_stalk_of_smoothRelativeDimension_one K X f x
  exact orderAt_eq_ord_stalk_of_eq_algebraMap x ha g hg

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
