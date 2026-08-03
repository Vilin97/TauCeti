/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.FibreDegree

/-!
# The zero fibre of a rational function

This file identifies the local order of a rational function with ramification in the zero fibre
of its associated projective-line morphism.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- On the inverse image of the standard affine chart of `ℙ¹`, the pullback of `X₀ / X₁`
represents the rational function used to define the map. -/
theorem germToFunctionField_rationalFunctionMorphism_app_affineCoordinate
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    let φ := rationalFunctionMorphism K X f g
    let V := φ ⁻¹ᵁ ProjectiveLine.standardAffineOpen K
    letI : Nonempty V := ⟨⟨genericPoint X,
      rationalFunctionMorphism_genericPoint_mem_standardAffineOpen K X f g⟩⟩
    X.germToFunctionField V
        (φ.app (ProjectiveLine.standardAffineOpen K)
          (ProjectiveLine.affineCoordinate K)) =
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  let U := ProjectiveLine.standardAffineOpen K
  let V := φ ⁻¹ᵁ U
  have hηV : genericPoint X ∈ V :=
    rationalFunctionMorphism_genericPoint_mem_standardAffineOpen K X f g
  letI : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  let η := X.fromSpecStalk (genericPoint X)
  have hηpre : η ⁻¹ᵁ V = ⊤ := by
    apply top_unique
    intro z _
    change η z ∈ V
    letI : Subsingleton (Spec X.functionField) :=
      show Subsingleton (PrimeSpectrum X.functionField) from inferInstance
    have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
    rw [hz, Scheme.fromSpecStalk_closedPoint]
    exact hηV
  have hff : η ≫ φ = rationalFunctionGenericMorphism K f g := by
    simpa [η, φ] using rationalFunctionMorphism_fromFunctionField K X f g
  have hcomp := Scheme.Hom.appLE_comp_appLE η φ U V ⊤ le_rfl hηpre.ge
  have hcompEval := congrArg (fun h ↦ h (ProjectiveLine.affineCoordinate K)) hcomp
  simp only [hff] at hcompEval
  have hpull :
      η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.affineCoordinate K)) =
        (Scheme.ΓSpecIso X.functionField).inv
          ((Additive.toMul g : X.functionFieldˣ) : X.functionField) := by
    rw [φ.app_eq_appLE]
    change ((φ.appLE U V le_rfl ≫ η.appLE V ⊤ hηpre.ge)
      (ProjectiveLine.affineCoordinate K)) = _
    rw [hcompEval]
    simpa only [rationalFunctionGenericMorphism, CommRingCat.of_carrier] using
      ProjectiveLine.ofElement_appLE_affineCoordinate K X.functionField
        (baseFieldToFunctionField K f)
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField)
  have hgerm :
      η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.affineCoordinate K)) =
        (Scheme.ΓSpecIso X.functionField).inv
          (X.germToFunctionField V
            (φ.app U (ProjectiveLine.affineCoordinate K))) := by
    let r := (Spec X.functionField).presheaf.map
      (homOfLE (le_top : η ⁻¹ᵁ V ≤ ⊤)).op
    have hr : (homOfLE (le_top : η ⁻¹ᵁ V ≤ ⊤)) = eqToHom hηpre :=
      Subsingleton.elim _ _
    have hrinj : Function.Injective r := by
      dsimp only [r]
      rw [hr]
      exact ConcreteCategory.bijective_of_isIso _ |>.1
    apply hrinj
    have happ :
        r (η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.affineCoordinate K))) =
          η.app V (φ.app U (ProjectiveLine.affineCoordinate K)) := by
      have hmap := η.appLE_map' (U := V) (V := η ⁻¹ᵁ V)
        (V' := ⊤) le_rfl hηpre
      have hmapEval := congrArg
        (fun q ↦ q (φ.app U (ProjectiveLine.affineCoordinate K))) hmap
      simpa only [r, hr, CommRingCat.comp_apply, η.appLE_eq_app] using hmapEval
    rw [happ, Scheme.fromSpecStalk_app hηV]
    rfl
  apply (Scheme.ΓSpecIso X.functionField).symm.commRingCatIsoToRingEquiv.injective
  exact hgerm.symm.trans hpull

/-- At a point mapping into the standard affine chart, the standard coordinate pulled back to
the source stalk maps to the original rational function in the function field. -/
theorem algebraMap_stalkMap_germ_affineCoordinate_eq
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : X)
    (hx : rationalFunctionMorphism K X f g x ∈
      ProjectiveLine.standardAffineOpen K) :
    algebraMap (X.presheaf.stalk x) X.functionField
        ((rationalFunctionMorphism K X f g).stalkMap x
          ((ProjectiveLine.scheme K).presheaf.germ
            (ProjectiveLine.standardAffineOpen K)
            (rationalFunctionMorphism K X f g x) hx
            (ProjectiveLine.affineCoordinate K))) =
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) := by
  let φ := rationalFunctionMorphism K X f g
  let V := φ ⁻¹ᵁ ProjectiveLine.standardAffineOpen K
  have hηV : genericPoint X ∈ V :=
    rationalFunctionMorphism_genericPoint_mem_standardAffineOpen K X f g
  letI : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  have hxV : x ∈ V := hx
  rw [Scheme.Hom.germ_stalkMap_apply]
  change algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ V x hxV
        (φ.app (ProjectiveLine.standardAffineOpen K)
          (ProjectiveLine.affineCoordinate K))) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact germToFunctionField_rationalFunctionMorphism_app_affineCoordinate K X f g

/-- On the standard affine chart, the scheme-theoretic order of the rational function is the
finite order of the pulled-back affine coordinate in the source DVR. -/
theorem orderAt_eq_ord_stalkMap_affineCoordinate
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hx : rationalFunctionMorphism K X f g x.1 ∈
      ProjectiveLine.standardAffineOpen K) :
    orderAt x g =
      (Ring.ord (X.presheaf.stalk x.1)
        ((rationalFunctionMorphism K X f g).stalkMap x.1
          ((ProjectiveLine.scheme K).presheaf.germ
            (ProjectiveLine.standardAffineOpen K)
            (rationalFunctionMorphism K X f g x.1) hx
            (ProjectiveLine.affineCoordinate K)))).toNat := by
  let a := (rationalFunctionMorphism K X f g).stalkMap x.1
    ((ProjectiveLine.scheme K).presheaf.germ
      (ProjectiveLine.standardAffineOpen K)
      (rationalFunctionMorphism K X f g x.1) hx
      (ProjectiveLine.affineCoordinate K))
  have haMap : algebraMap (X.presheaf.stalk x.1) X.functionField a =
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) :=
    algebraMap_stalkMap_germ_affineCoordinate_eq K X f g x.1 hx
  have ha : a ≠ 0 := by
    intro ha
    have : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) = 0 := by
      rw [← haMap, ha, map_zero]
    exact Units.ne_zero (Additive.toMul g) this
  exact orderAt_eq_ord_stalk_of_smoothRelativeDimension_one K X f x ha g haMap.symm

/-- The generic point of a smooth relative curve maps into the affine chart `D₊(X₀)` containing
infinity. The inverse coordinate there is the inverse of the nonzero function-field element. -/
theorem rationalFunctionMorphism_genericPoint_mem_infinityAffineOpen
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    rationalFunctionMorphism K X f g (genericPoint X) ∈
      ProjectiveLine.infinityAffineOpen K := by
  have hff :
      X.fromSpecStalk (genericPoint X) ≫ rationalFunctionMorphism K X f g =
        rationalFunctionGenericMorphism K f g := by
    simpa using rationalFunctionMorphism_fromFunctionField K X f g
  let z : Spec X.functionField := IsLocalRing.closedPoint X.functionField
  have happ := congrArg (fun φ ↦ φ z) hff
  change rationalFunctionMorphism K X f g
      (X.fromSpecStalk (genericPoint X) z) = rationalFunctionGenericMorphism K f g z at happ
  dsimp [z] at happ
  rw [Scheme.fromSpecStalk_closedPoint] at happ
  rw [happ]
  change z ∈
    ProjectiveLine.ofElement K X.functionField
      (baseFieldToFunctionField K f)
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K
  rw [ProjectiveLine.ofElement_preimage_basicOpen_X_zero K X.functionField
    (baseFieldToFunctionField K f)
    ((Additive.toMul g : X.functionFieldˣ) : X.functionField)
    (Units.ne_zero (Additive.toMul g))]
  trivial

/-- On the inverse image of the chart at infinity, the pullback of `X₁ / X₀` represents the
inverse of the rational function used to define the map. -/
theorem germToFunctionField_rationalFunctionMorphism_app_inverseAffineCoordinate
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    let φ := rationalFunctionMorphism K X f g
    let V := φ ⁻¹ᵁ ProjectiveLine.infinityAffineOpen K
    letI : Nonempty V := ⟨⟨genericPoint X,
      rationalFunctionMorphism_genericPoint_mem_infinityAffineOpen K X f g⟩⟩
    X.germToFunctionField V
        (φ.app (ProjectiveLine.infinityAffineOpen K)
          (ProjectiveLine.inverseAffineCoordinate K)) =
      (((Additive.toMul g : X.functionFieldˣ) : X.functionField)⁻¹) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  let U := ProjectiveLine.infinityAffineOpen K
  let V := φ ⁻¹ᵁ U
  have hηV : genericPoint X ∈ V :=
    rationalFunctionMorphism_genericPoint_mem_infinityAffineOpen K X f g
  letI : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  let η := X.fromSpecStalk (genericPoint X)
  have hηpre : η ⁻¹ᵁ V = ⊤ := by
    apply top_unique
    intro z _
    change η z ∈ V
    letI : Subsingleton (Spec X.functionField) :=
      show Subsingleton (PrimeSpectrum X.functionField) from inferInstance
    have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
    rw [hz, Scheme.fromSpecStalk_closedPoint]
    exact hηV
  have hff : η ≫ φ = rationalFunctionGenericMorphism K f g := by
    simpa [η, φ] using rationalFunctionMorphism_fromFunctionField K X f g
  have hcomp := Scheme.Hom.appLE_comp_appLE η φ U V ⊤ le_rfl hηpre.ge
  have hcompEval := congrArg
    (fun h ↦ h (ProjectiveLine.inverseAffineCoordinate K)) hcomp
  simp only [hff] at hcompEval
  have hpull :
      η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.inverseAffineCoordinate K)) =
        (Scheme.ΓSpecIso X.functionField).inv
          (((Additive.toMul g : X.functionFieldˣ) : X.functionField)⁻¹) := by
    rw [φ.app_eq_appLE]
    change ((φ.appLE U V le_rfl ≫ η.appLE V ⊤ hηpre.ge)
      (ProjectiveLine.inverseAffineCoordinate K)) = _
    rw [hcompEval]
    simpa only [rationalFunctionGenericMorphism, CommRingCat.of_carrier] using
      ProjectiveLine.ofElement_appLE_inverseAffineCoordinate K X.functionField
        (baseFieldToFunctionField K f)
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField)
        (Units.ne_zero (Additive.toMul g))
  have hgerm :
      η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.inverseAffineCoordinate K)) =
        (Scheme.ΓSpecIso X.functionField).inv
          (X.germToFunctionField V
            (φ.app U (ProjectiveLine.inverseAffineCoordinate K))) := by
    let r := (Spec X.functionField).presheaf.map
      (homOfLE (le_top : η ⁻¹ᵁ V ≤ ⊤)).op
    have hr : (homOfLE (le_top : η ⁻¹ᵁ V ≤ ⊤)) = eqToHom hηpre :=
      Subsingleton.elim _ _
    have hrinj : Function.Injective r := by
      dsimp only [r]
      rw [hr]
      exact ConcreteCategory.bijective_of_isIso _ |>.1
    apply hrinj
    have happ :
        r (η.appLE V ⊤ hηpre.ge
          (φ.app U (ProjectiveLine.inverseAffineCoordinate K))) =
          η.app V (φ.app U (ProjectiveLine.inverseAffineCoordinate K)) := by
      have hmap := η.appLE_map' (U := V) (V := η ⁻¹ᵁ V)
        (V' := ⊤) le_rfl hηpre
      have hmapEval := congrArg
        (fun q ↦ q (φ.app U (ProjectiveLine.inverseAffineCoordinate K))) hmap
      simpa only [r, hr, CommRingCat.comp_apply, η.appLE_eq_app] using hmapEval
    rw [happ, Scheme.fromSpecStalk_app hηV]
    rfl
  apply (Scheme.ΓSpecIso X.functionField).symm.commRingCatIsoToRingEquiv.injective
  exact hgerm.symm.trans hpull

/-- At a point mapping into the affine chart at infinity, the inverse coordinate pulled back to
the source stalk maps to the inverse rational function in the function field. -/
theorem algebraMap_stalkMap_germ_inverseAffineCoordinate_eq
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : X)
    (hx : rationalFunctionMorphism K X f g x ∈
      ProjectiveLine.infinityAffineOpen K) :
    algebraMap (X.presheaf.stalk x) X.functionField
        ((rationalFunctionMorphism K X f g).stalkMap x
          ((ProjectiveLine.scheme K).presheaf.germ
            (ProjectiveLine.infinityAffineOpen K)
            (rationalFunctionMorphism K X f g x) hx
            (ProjectiveLine.inverseAffineCoordinate K))) =
      (((Additive.toMul g : X.functionFieldˣ) : X.functionField)⁻¹) := by
  let φ := rationalFunctionMorphism K X f g
  let V := φ ⁻¹ᵁ ProjectiveLine.infinityAffineOpen K
  have hηV : genericPoint X ∈ V :=
    rationalFunctionMorphism_genericPoint_mem_infinityAffineOpen K X f g
  letI : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  have hxV : x ∈ V := hx
  rw [Scheme.Hom.germ_stalkMap_apply]
  change algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ V x hxV
        (φ.app (ProjectiveLine.infinityAffineOpen K)
          (ProjectiveLine.inverseAffineCoordinate K))) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact germToFunctionField_rationalFunctionMorphism_app_inverseAffineCoordinate K X f g

/-- On the chart at infinity, the finite order of the pulled-back inverse coordinate is the
negative of the scheme-theoretic order of the original rational function. -/
theorem neg_orderAt_eq_ord_stalkMap_inverseAffineCoordinate
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hx : rationalFunctionMorphism K X f g x.1 ∈
      ProjectiveLine.infinityAffineOpen K) :
    -orderAt x g =
      (Ring.ord (X.presheaf.stalk x.1)
        ((rationalFunctionMorphism K X f g).stalkMap x.1
          ((ProjectiveLine.scheme K).presheaf.germ
            (ProjectiveLine.infinityAffineOpen K)
            (rationalFunctionMorphism K X f g x.1) hx
            (ProjectiveLine.inverseAffineCoordinate K)))).toNat := by
  let a := (rationalFunctionMorphism K X f g).stalkMap x.1
    ((ProjectiveLine.scheme K).presheaf.germ
      (ProjectiveLine.infinityAffineOpen K)
      (rationalFunctionMorphism K X f g x.1) hx
      (ProjectiveLine.inverseAffineCoordinate K))
  have haMap : algebraMap (X.presheaf.stalk x.1) X.functionField a =
      (((Additive.toMul g : X.functionFieldˣ) : X.functionField)⁻¹) :=
    algebraMap_stalkMap_germ_inverseAffineCoordinate_eq K X f g x.1 hx
  have ha : a ≠ 0 := by
    intro ha
    have : (((Additive.toMul g : X.functionFieldˣ) : X.functionField)⁻¹) = 0 := by
      rw [← haMap, ha, map_zero]
    exact inv_ne_zero (Units.ne_zero (Additive.toMul g)) this
  have hginv :
      ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField) =
        algebraMap (X.presheaf.stalk x.1) X.functionField a := by
    change (((Additive.toMul g : X.functionFieldˣ)⁻¹ : X.functionFieldˣ) :
      X.functionField) = _
    simpa only [Units.val_inv_eq_inv_val] using haMap.symm
  have horder := orderAt_eq_ord_stalk_of_smoothRelativeDimension_one
    K X f x ha (-g) hginv
  simpa only [map_neg] using horder

/-- A point above zero of a non-global rational function is a codimension-one point of the source
curve. -/
noncomputable def zeroFibreCodimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.zeroPoint K}) :
    CodimensionOnePoint X := by
  refine ⟨x.1, coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
    K X f x.1 ?_⟩
  intro hx
  have himage := congrArg (rationalFunctionMorphism K X f g) hx
  rw [x.2, rationalFunctionMorphism_genericPoint_eq_genericPoint_of_nonGlobal
    K X f g hg] at himage
  exact ProjectiveLine.zeroPoint_ne_genericPoint K himage

/-- The canonical codimension-one point above zero has the original fibre point as its
underlying scheme point. -/
@[simp]
theorem zeroFibreCodimensionOnePoint_val
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.zeroPoint K}) :
    (zeroFibreCodimensionOnePoint K X f g hg x).1 = x.1 := by
  rfl

/-- Above the zero point of the rational-function morphism, the affine ramification index is the
scheme-theoretic order of the rational function. -/
theorem ramificationIdx_primeIdealOf_zero_eq_orderAt
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : CodimensionOnePoint X)
    (hxzero : rationalFunctionMorphism K X f g x.1 = ProjectiveLine.zeroPoint K) :
    let φ := rationalFunctionMorphism K X f g
    letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
    let U := ProjectiveLine.standardAffineOpen K
    let hxU : φ x.1 ∈ U := by rw [hxzero]; exact ProjectiveLine.zeroPoint_mem_standardAffineOpen K
    let V := φ ⁻¹ᵁ U
    let hV : IsAffineOpen V :=
      (ProjectiveLine.isAffineOpen_standardAffineOpen K).preimage φ
    let a := φ.appLE U V le_rfl
    letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
    let q := (hV.primeIdealOf ⟨x.1, hxU⟩).asIdeal
    (q.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) = orderAt x g := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
  have hxU : φ x.1 ∈ U := by
    rw [hxzero]
    exact hz
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let R := Γ(ProjectiveLine.scheme K, U)
  let S := Γ(X, V)
  let a : R ⟶ S := φ.appLE U V le_rfl
  let t : R := ProjectiveLine.affineCoordinate K
  let p : Ideal R := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal
  let q : Ideal S := (hV.primeIdealOf ⟨x.1, hxU⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).isPrime
  letI : q.IsPrime := (hV.primeIdealOf ⟨x.1, hxU⟩).isPrime
  letI : Algebra R S := a.hom.toAlgebra
  have hover : q.LiesOver p := by
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV
      (f := φ) le_rfl hxU
    constructor
    calc
      p = (hU.primeIdealOf ⟨φ x.1, hxU⟩).asIdeal := by
        exact congrArg PrimeSpectrum.asIdeal
          (congrArg hU.primeIdealOf (Subtype.ext hxzero.symm))
      _ = Ideal.comap a.hom q := by
        simpa only [a, q, PrimeSpectrum.comap_asIdeal] using
          congrArg PrimeSpectrum.asIdeal hcomap |>.symm
      _ = q.under R := by
        rw [Ideal.under_def, RingHom.algebraMap_toAlgebra]
  letI : q.LiesOver p := hover
  have hp : p = Ideal.span ({t} : Set R) := by
    exact ProjectiveLine.primeIdealOf_zeroPoint_asIdeal_of_mem K hz
  have hram := ramificationIdx_eq_ord_algebraMap_of_eq_span_singleton p q t hp
  letI : Algebra S (X.presheaf.stalk x.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x.1, hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x.1) q :=
    hV.isLocalization_stalk ⟨x.1, hxU⟩
  let estalk : Localization.AtPrime q ≃ₐ[S] X.presheaf.stalk x.1 :=
    IsLocalization.algEquiv q.primeCompl _ _
  have helem : estalk (algebraMap R (Localization.AtPrime q) t) =
      φ.stalkMap x.1
        ((ProjectiveLine.scheme K).presheaf.germ U (φ x.1) hxU t) := by
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q), estalk.commutes]
    simp only [RingHom.algebraMap_toAlgebra]
    rw [Scheme.Hom.germ_stalkMap_apply]
    change X.presheaf.germ V x.1 hxU (a.hom t) =
      X.presheaf.germ V x.1 hxU (φ.app U t)
    rw [φ.app_eq_appLE]
  have hord := ord_ringEquiv estalk.toRingEquiv
    (algebraMap R (Localization.AtPrime q) t)
  have horder := orderAt_eq_ord_stalkMap_affineCoordinate K X f g x hxU
  calc
    (q.ramificationIdx R : ℤ) =
        ((Ring.ord (Localization.AtPrime q)
          (algebraMap R (Localization.AtPrime q) t)).toNat : ℤ) := by
      exact_mod_cast hram
    _ = ((Ring.ord (X.presheaf.stalk x.1)
          (estalk (algebraMap R (Localization.AtPrime q) t))).toNat : ℤ) := by
      exact_mod_cast congrArg ENat.toNat hord
    _ = ((Ring.ord (X.presheaf.stalk x.1)
          (φ.stalkMap x.1
            ((ProjectiveLine.scheme K).presheaf.germ U (φ x.1) hxU t))).toNat : ℤ) := by
      rw [helem]
    _ = orderAt x g := horder.symm

/-- The order/residue-degree sum above zero is the finite-flat degree of the rational-function
morphism. -/
theorem sum_orderAt_residueDegree_zero_eq_finrank
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    let φ := rationalFunctionMorphism K X f g
    letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
    letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
    let U := ProjectiveLine.standardAffineOpen K
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
    let p := ((ProjectiveLine.isAffineOpen_standardAffineOpen K).primeIdealOf
      ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal
    letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
    letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
      change a.hom.Finite
      simpa [a, V, φ.appLE_eq_app] using φ.finite_app U
        (ProjectiveLine.isAffineOpen_standardAffineOpen K)
    letI : Fintype (p.primesOver Γ(X, V)) :=
      (Algebra.QuasiFinite.finite_primesOver p).fintype
    let e := fibrePointPrimesOverEquiv φ U
      (ProjectiveLine.isAffineOpen_standardAffineOpen K)
      (ProjectiveLine.zeroPoint K) hz
    ∑ q : p.primesOver Γ(X, V),
      orderAt (zeroFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
        (φ.residueDegree (e.symm q).1 : ℤ) =
      (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let a := φ.appLE U V le_rfl
  let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.zeroPoint K) hz
  have hbase := sum_ramification_residueDegree_app_eq_finrank
    φ U hU (ProjectiveLine.zeroPoint K) hz
  calc
    ∑ q : p.primesOver Γ(X, V),
        orderAt (zeroFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
          (φ.residueDegree (e.symm q).1 : ℤ) =
        ∑ q : p.primesOver Γ(X, V),
          (q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) *
            (φ.residueDegree (e.symm q).1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      let z := zeroFibreCodimensionOnePoint K X f g hg (e.symm q)
      have hzmap : φ z.1 = ProjectiveLine.zeroPoint K := (e.symm q).2
      have hlocal := ramificationIdx_primeIdealOf_zero_eq_orderAt
        K X f g hg z hzmap
      dsimp only at hlocal
      have hzV : z.1 ∈ V := by
        change φ z.1 ∈ U
        rw [hzmap]
        exact hz
      have heq : (hV.primeIdealOf ⟨z.1, hzV⟩).asIdeal = q.1 := by
        simpa only [e, z, fibrePointPrimesOverEquiv_apply_val,
          zeroFibreCodimensionOnePoint_val] using
            congrArg Subtype.val (e.apply_symm_apply q)
      rw [heq] at hlocal
      exact hlocal.symm
    _ = (φ.finrank (ProjectiveLine.zeroPoint K) : ℤ) := by
      exact_mod_cast hbase

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
