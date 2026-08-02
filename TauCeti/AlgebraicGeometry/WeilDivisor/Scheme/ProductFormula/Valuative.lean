/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Extending rational-function maps from valuation-ring stalks

The properness of `ℙ¹_K` extends the function-field point `[g : 1]` over any point whose local
ring is a valuation ring. Mathlib's spreading-out theorem then produces a representative of the
rational map on an open neighbourhood of that point. Consequently, if every stalk of an integral
scheme is a valuation ring, the rational map attached to `g` is defined everywhere.

This is the extension step in the geometric proof of the product formula from
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve". For a smooth curve,
the remaining input to this theorem is the local regularity/DVR result for its stalks.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemePartialMap

variable {X Y : Scheme.{u}}

/-- Restriction of a partial map to stalks is compatible with specialization inside its domain. -/
lemma specMap_stalkSpecializes_fromSpecStalkOfMem
    (p : X.PartialMap Y) {x y : X} (hxy : x ⤳ y) (hy : y ∈ p.domain) :
    Spec.map (X.presheaf.stalkSpecializes hxy) ≫ p.fromSpecStalkOfMem hy =
      p.fromSpecStalkOfMem (hxy.mem_open p.domain.2 hy) := by
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono p.domain.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk hxy

/-- The function-field restriction of a partial map factors through its restriction to the stalk
at any point of its domain. -/
lemma fromFunctionField_eq_specMap_fromSpecStalkOfMem
    [IrreducibleSpace X] (p : X.PartialMap Y) (x : X) (hx : x ∈ p.domain) :
    p.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)) ≫ p.fromSpecStalkOfMem hx := by
  exact (specMap_stalkSpecializes_fromSpecStalkOfMem p
    ((genericPoint_spec X).specializes trivial) hx).symm

end SchemePartialMap

namespace SchemeWeilDivisor

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

private noncomputable def specOfCarrierTo (R : CommRingCat.{u}) :
    Spec (.of R) ⟶ Spec R :=
  eqToHom (congrArg Spec (CommRingCat.of_carrier R))

private noncomputable def specToOfCarrier (R : CommRingCat.{u}) :
    Spec R ⟶ Spec (.of R) :=
  eqToHom (congrArg Spec (CommRingCat.of_carrier R).symm)

private noncomputable instance (R : CommRingCat.{u}) : IsIso (specOfCarrierTo R) := by
  dsimp only [specOfCarrierTo]
  infer_instance

private noncomputable instance (R : CommRingCat.{u}) : IsIso (specToOfCarrier R) := by
  dsimp only [specToOfCarrier]
  infer_instance

@[simp]
private lemma specToOfCarrier_specOfCarrierTo (R : CommRingCat.{u}) :
    specToOfCarrier R ≫ specOfCarrierTo R = 𝟙 _ := by
  simp [specToOfCarrier, specOfCarrierTo]

@[simp]
private lemma specOfCarrierTo_specToOfCarrier (R : CommRingCat.{u}) :
    specOfCarrierTo R ≫ specToOfCarrier R = 𝟙 _ := by
  simp [specToOfCarrier, specOfCarrierTo]

private lemma specMap_algebraMap_comp_specOfCarrierTo
    (x : X) (hηx : genericPoint X ⤳ x) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        specOfCarrierTo (X.presheaf.stalk x) =
      specOfCarrierTo X.functionField ≫
        Spec.map (X.presheaf.stalkSpecializes hηx) := by
  change Spec.map (X.presheaf.stalkSpecializes hηx) ≫
      specOfCarrierTo (X.presheaf.stalk x) =
    specOfCarrierTo X.functionField ≫
      Spec.map (X.presheaf.stalkSpecializes hηx)
  simp only [specOfCarrierTo, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

private lemma specMap_stalkSpecializes_comp_specToOfCarrier
    (x : X) :
    Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫
        specToOfCarrier (X.presheaf.stalk x) =
      specToOfCarrier X.functionField ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField)) := by
  let hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  change Spec.map (X.presheaf.stalkSpecializes hηx) ≫
      specToOfCarrier (X.presheaf.stalk x) =
    specToOfCarrier X.functionField ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField))
  rw [← cancel_mono (specOfCarrierTo (X.presheaf.stalk x))]
  rw [Category.assoc, specToOfCarrier_specOfCarrierTo, Category.comp_id]
  rw [Category.assoc, specMap_algebraMap_comp_specOfCarrierTo x hηx]
  rw [← Category.assoc, specToOfCarrier_specOfCarrierTo, Category.id_comp]

private lemma rationalFunctionGenericMorphism_comp_structureMap_carrier
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    rationalFunctionGenericMorphism K f g ≫ ProjectiveLine.structureMap K =
      specOfCarrierTo X.functionField ≫
        X.fromSpecStalk (genericPoint X) ≫ f := by
  simpa only [specOfCarrierTo, eqToHom_refl, Category.id_comp] using
    rationalFunctionGenericMorphism_comp_structureMap K f g

private noncomputable def rationalFunctionValuativeCommSq (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    ValuativeCommSq (ProjectiveLine.structureMap K) where
  R := X.presheaf.stalk x
  commRing := (X.presheaf.stalk x).commRing
  domain := inferInstance
  valuationRing := inferInstance
  K := X.functionField
  field := inferInstance
  algebra := inferInstance
  isFractionRing := inferInstance
  i₁ := rationalFunctionGenericMorphism K f g
  i₂ := specOfCarrierTo (X.presheaf.stalk x) ≫ X.fromSpecStalk x ≫ f
  commSq := ⟨by
    rw [rationalFunctionGenericMorphism_comp_structureMap_carrier]
    let hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    calc
      (specOfCarrierTo X.functionField ≫ X.fromSpecStalk (genericPoint X)) ≫ f =
          specOfCarrierTo X.functionField ≫
            (X.fromSpecStalk (genericPoint X) ≫ f) := Category.assoc _ _ _
      _ = specOfCarrierTo X.functionField ≫
          ((Spec.map (X.presheaf.stalkSpecializes hηx) ≫ X.fromSpecStalk x) ≫ f) := by
        rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      _ = (specOfCarrierTo X.functionField ≫
          Spec.map (X.presheaf.stalkSpecializes hηx)) ≫
            (X.fromSpecStalk x ≫ f) := by simp only [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
            specOfCarrierTo (X.presheaf.stalk x)) ≫
              (X.fromSpecStalk x ≫ f) := by
        rw [specMap_algebraMap_comp_specOfCarrierTo x hηx]
      _ = Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
            specOfCarrierTo (X.presheaf.stalk x) ≫ X.fromSpecStalk x ≫ f := by
        simp only [Category.assoc]⟩

private noncomputable def rationalFunctionStalkExtensionRaw (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    Spec (.of (X.presheaf.stalk x)) ⟶ ProjectiveLine.scheme K :=
  ((ProjectiveLine.structureMap_valuativeCriterion K).existence
    (rationalFunctionValuativeCommSq K f g x)).exists_lift.some.l

private lemma specMap_algebraMap_comp_rationalFunctionStalkExtensionRaw
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        rationalFunctionStalkExtensionRaw K f g x =
      rationalFunctionGenericMorphism K f g := by
  exact ((ProjectiveLine.structureMap_valuativeCriterion K).existence
    (rationalFunctionValuativeCommSq K f g x)).exists_lift.some.fac_left

private lemma rationalFunctionStalkExtensionRaw_comp_structureMap
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    rationalFunctionStalkExtensionRaw K f g x ≫ ProjectiveLine.structureMap K =
      specOfCarrierTo (X.presheaf.stalk x) ≫ X.fromSpecStalk x ≫ f := by
  exact ((ProjectiveLine.structureMap_valuativeCriterion K).existence
    (rationalFunctionValuativeCommSq K f g x)).exists_lift.some.fac_right

private noncomputable def rationalFunctionStalkExtension (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    Spec (X.presheaf.stalk x) ⟶ ProjectiveLine.scheme K :=
  specToOfCarrier (X.presheaf.stalk x) ≫
    rationalFunctionStalkExtensionRaw K f g x

private lemma rationalFunctionStalkExtension_comp_structureMap
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    rationalFunctionStalkExtension K f g x ≫ ProjectiveLine.structureMap K =
      X.fromSpecStalk x ≫ f := by
  rw [rationalFunctionStalkExtension, Category.assoc,
    rationalFunctionStalkExtensionRaw_comp_structureMap]
  rw [← Category.assoc, specToOfCarrier_specOfCarrierTo, Category.id_comp]

private lemma specMap_stalkSpecializes_comp_rationalFunctionStalkExtension
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫
        rationalFunctionStalkExtension K f g x =
      specToOfCarrier X.functionField ≫
        rationalFunctionGenericMorphism K f g := by
  rw [rationalFunctionStalkExtension, ← Category.assoc,
    specMap_stalkSpecializes_comp_specToOfCarrier, Category.assoc,
    specMap_algebraMap_comp_rationalFunctionStalkExtensionRaw]

private noncomputable def rationalFunctionPartialMapAt (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    X.PartialMap (ProjectiveLine.scheme K) :=
  Scheme.PartialMap.ofFromSpecStalk f (ProjectiveLine.structureMap K)
    (rationalFunctionStalkExtension K f g x)
    (rationalFunctionStalkExtension_comp_structureMap K f g x)

private lemma mem_domain_rationalFunctionPartialMapAt (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    x ∈ (rationalFunctionPartialMapAt K f g x).domain :=
  Scheme.PartialMap.mem_domain_ofFromSpecStalk f (ProjectiveLine.structureMap K)
    (rationalFunctionStalkExtension K f g x)
    (rationalFunctionStalkExtension_comp_structureMap K f g x)

private lemma rationalFunctionPartialMapAt_fromSpecStalkOfMem
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    (rationalFunctionPartialMapAt K f g x).fromSpecStalkOfMem
        (mem_domain_rationalFunctionPartialMapAt K f g x) =
      rationalFunctionStalkExtension K f g x := by
  exact Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk f
    (ProjectiveLine.structureMap K) (rationalFunctionStalkExtension K f g x)
    (rationalFunctionStalkExtension_comp_structureMap K f g x)

private lemma rationalFunctionPartialMapAt_fromFunctionField
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    (rationalFunctionPartialMapAt K f g x).fromFunctionField =
      specToOfCarrier X.functionField ≫ rationalFunctionGenericMorphism K f g := by
  calc
    (rationalFunctionPartialMapAt K f g x).fromFunctionField =
        Spec.map (X.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes trivial)) ≫
          (rationalFunctionPartialMapAt K f g x).fromSpecStalkOfMem
            (mem_domain_rationalFunctionPartialMapAt K f g x) :=
      SchemePartialMap.fromFunctionField_eq_specMap_fromSpecStalkOfMem _ _ _
    _ = Spec.map (X.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes trivial)) ≫
          rationalFunctionStalkExtension K f g x := by
      rw [rationalFunctionPartialMapAt_fromSpecStalkOfMem]
    _ = specToOfCarrier X.functionField ≫ rationalFunctionGenericMorphism K f g :=
      specMap_stalkSpecializes_comp_rationalFunctionStalkExtension K f g x

private lemma rationalFunctionMap_fromFunctionField_carrier
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) :
    (rationalFunctionMap K f g).fromFunctionField =
      specToOfCarrier X.functionField ≫ rationalFunctionGenericMorphism K f g := by
  simpa only [specToOfCarrier, eqToHom_refl, Category.id_comp] using
    rationalFunctionMap_fromFunctionField K f g

private lemma rationalFunctionPartialMapAt_toRationalMap
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    (rationalFunctionPartialMapAt K f g x).toRationalMap =
      rationalFunctionMap K f g := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  rw [rationalFunctionPartialMapAt_fromFunctionField,
    rationalFunctionMap_fromFunctionField_carrier]

/-- If the local ring at `x` is a valuation ring, the rational-function map to `ℙ¹_K` is defined
at `x`. -/
lemma mem_rationalFunctionMap_domain_of_valuationRing
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ) (x : X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    x ∈ (rationalFunctionMap K f g).domain := by
  rw [Scheme.RationalMap.mem_domain]
  exact ⟨rationalFunctionPartialMapAt K f g x,
    mem_domain_rationalFunctionPartialMapAt K f g x,
    rationalFunctionPartialMapAt_toRationalMap K f g x⟩

/-- If every local ring of an integral scheme is a valuation ring, every rational-function map
`X ⤏ ℙ¹_K` is defined on all of `X`. -/
lemma rationalFunctionMap_domain_eq_top_of_valuationRings
    (K : Type u) [Field K]
    (f : X ⟶ Spec (.of K)) (g : Additive X.functionFieldˣ)
    (hValuation : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    (rationalFunctionMap K f g).domain = ⊤ := by
  apply top_unique
  intro x _
  letI : ValuationRing (X.presheaf.stalk x) := hValuation x
  exact mem_rationalFunctionMap_domain_of_valuationRing K f g x

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
