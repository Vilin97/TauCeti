/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of nonconstant morphisms from smooth proper curves

A proper morphism from an integral Noetherian smooth relative curve is locally quasi-finite as
soon as no fibre is the whole curve. Indeed, a fibre over a closed point is a proper closed
subset and hence finite. A fibre over a non-closed point contains no closed point, because proper
morphisms are closed, and therefore contains at most the generic point. Zariski's main theorem
then upgrades the morphism to a finite morphism.

Applied to the projective-line-valued morphism `[g : 1]`, this isolates the remaining
nonconstancy obligation in the geometric product-formula proof.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The global projective-line-valued morphism attached to a rational function on a proper
smooth relative curve is proper. -/
theorem isProper_rationalFunctionMorphism
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ) :
    IsProper (rationalFunctionMorphism K X f g) := by
  haveI : IsProper
      (rationalFunctionMorphism K X f g ≫ ProjectiveLine.structureMap K) := by
    rw [rationalFunctionMorphism_comp_structureMap]
    infer_instance
  exact IsProper.of_comp _ (ProjectiveLine.structureMap K)

/-- The generic point of a smooth relative curve is mapped into the standard affine chart
`D₊(X₁)` by its rational-function morphism. On that chart the map has coordinate `g`. -/
theorem rationalFunctionMorphism_genericPoint_mem_standardAffineOpen
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) :
    rationalFunctionMorphism K X f g (genericPoint X) ∈
      ProjectiveLine.standardAffineOpen K := by
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
  change ProjectiveLine.ofElement K X.functionField
      (baseFieldToFunctionField K f)
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField)
      z ∈ ProjectiveLine.standardAffineOpen K
  change z ∈
    ProjectiveLine.ofElement K X.functionField
      (baseFieldToFunctionField K f)
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K
  rw [ProjectiveLine.ofElement_preimage_basicOpen_X_one]
  trivial

/-- If one fibre of the rational-function morphism is the whole curve, then the rational
function is represented by a global section.

Indeed, the common image lies in `D₊(X₁)` because the generic point does. Pulling the affine
coordinate `X₀ / X₁` back to the curve gives the required global section, and its generic germ
is `g` by `ProjectiveLine.ofElement_appLE_affineCoordinate`. -/
theorem exists_eq_germToFunctionField_top_of_universal_fiber
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (y : ProjectiveLine.scheme K)
    (hyall : (rationalFunctionMorphism K X f g) ⁻¹' {y} = Set.univ) :
    ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a := by
  let φ := rationalFunctionMorphism K X f g
  have hconst : ∀ x : X, φ x = y := by
    intro x
    have hx : x ∈ φ ⁻¹' {y} := by rw [hyall]; trivial
    exact hx
  have hyU : y ∈ ProjectiveLine.standardAffineOpen K := by
    rw [← hconst (genericPoint X)]
    exact rationalFunctionMorphism_genericPoint_mem_standardAffineOpen K X f g
  have hpre : φ ⁻¹ᵁ ProjectiveLine.standardAffineOpen K = ⊤ := by
    apply top_unique
    intro x _
    change φ x ∈ ProjectiveLine.standardAffineOpen K
    rw [hconst x]
    exact hyU
  let a : Γ(X, ⊤) := φ.appLE (ProjectiveLine.standardAffineOpen K) ⊤ hpre.ge
    (ProjectiveLine.affineCoordinate K)
  have hff :
      X.fromSpecStalk (genericPoint X) ≫ φ = rationalFunctionGenericMorphism K f g := by
    simpa [φ] using rationalFunctionMorphism_fromFunctionField K X f g
  have hcomp := Scheme.Hom.appLE_comp_appLE
    (X.fromSpecStalk (genericPoint X)) φ
    (ProjectiveLine.standardAffineOpen K) ⊤ ⊤ hpre.ge le_rfl
  have hcompEval := congrArg (fun h ↦ h (ProjectiveLine.affineCoordinate K)) hcomp
  have htop :
      (X.fromSpecStalk (genericPoint X)).appLE ⊤ ⊤ le_rfl =
        (X.fromSpecStalk (genericPoint X)).appTop := by
    change (X.fromSpecStalk (genericPoint X)).appLE ⊤
      ((X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ ⊤) le_rfl = _
    exact Scheme.Hom.appLE_eq_app _
  rw [htop] at hcompEval
  simp only [hff] at hcompEval
  have hpull :
      (X.fromSpecStalk (genericPoint X)).appTop a =
        (Scheme.ΓSpecIso X.functionField).inv
          ((Additive.toMul g : X.functionFieldˣ) : X.functionField) := by
    change (X.fromSpecStalk (genericPoint X)).appTop
      (φ.appLE (ProjectiveLine.standardAffineOpen K) ⊤ hpre.ge
        (ProjectiveLine.affineCoordinate K)) = _
    change (((φ.appLE (ProjectiveLine.standardAffineOpen K) ⊤ hpre.ge) ≫
      (X.fromSpecStalk (genericPoint X)).appTop)
        (ProjectiveLine.affineCoordinate K)) = _
    rw [hcompEval]
    simpa only [rationalFunctionGenericMorphism, CommRingCat.of_carrier] using
      ProjectiveLine.ofElement_appLE_affineCoordinate K X.functionField
        (baseFieldToFunctionField K f)
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField)
  have hgerm :
      (X.fromSpecStalk (genericPoint X)).appTop a =
        (Scheme.ΓSpecIso X.functionField).inv (X.germToFunctionField ⊤ a) := by
    rw [Scheme.fromSpecStalk_appTop]
    change (((X.presheaf.germ ⊤ (genericPoint X) trivial ≫
      (Scheme.ΓSpecIso X.functionField).inv ≫
      (Spec X.functionField).presheaf.map (homOfLE le_top).op)) a) = _
    simp only [CommRingCat.comp_apply]
    simp
  refine ⟨a, ?_⟩
  apply (Scheme.ΓSpecIso X.functionField).symm.commRingCatIsoToRingEquiv.injective
  exact hpull.symm.trans hgerm

/-- A proper morphism from an integral Noetherian smooth relative curve is locally quasi-finite
if none of its point fibres is the whole curve. -/
theorem locallyQuasiFinite_of_isProper_of_no_universal_fiber_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    {Y : Scheme.{u}} (φ : X ⟶ Y) [IsProper φ]
    (hfiber : ∀ y, φ ⁻¹' {y} ≠ Set.univ) :
    LocallyQuasiFinite φ := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton φ
  intro y
  by_cases hy : IsClosed ({y} : Set Y)
  · exact finite_closed_subset_of_smoothRelativeDimension_one
      K X f _ (hy.preimage φ.continuous) (hfiber y)
  · refine (Set.finite_singleton (genericPoint X)).subset ?_
    intro x hx
    by_contra hxGeneric
    have hxClosed : IsClosed ({x} : Set X) :=
      isClosed_singleton_of_ne_genericPoint_of_smoothRelativeDimension_one
        K X f x hxGeneric
    apply hy
    have hImage : IsClosed (φ '' ({x} : Set X)) :=
      φ.isClosedMap _ hxClosed
    have hxy : φ x = y := hx
    simpa [hxy] using hImage

/-- The rational-function morphism on a proper smooth curve is finite once no point fibre is the
whole curve. This is the exact finiteness adapter needed before comparing the zero and infinity
fibres. -/
theorem isFinite_rationalFunctionMorphism_of_no_universal_fiber
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hfiber : ∀ y, (rationalFunctionMorphism K X f g) ⁻¹' {y} ≠ Set.univ) :
    IsFinite (rationalFunctionMorphism K X f g) := by
  letI : IsProper (rationalFunctionMorphism K X f g) :=
    isProper_rationalFunctionMorphism K X f g
  letI : LocallyQuasiFinite (rationalFunctionMorphism K X f g) :=
    locallyQuasiFinite_of_isProper_of_no_universal_fiber_smoothRelativeDimension_one
      K X f (rationalFunctionMorphism K X f g) hfiber
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A rational function which is not represented by a global section has no universal point
fibre under its projective-line-valued morphism. -/
theorem rationalFunctionMorphism_no_universal_fiber_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a) :
    ∀ y, (rationalFunctionMorphism K X f g) ⁻¹' {y} ≠ Set.univ := by
  intro y hy
  exact hg (exists_eq_germToFunctionField_top_of_universal_fiber K X f g y hy)

/-- The rational-function morphism of a non-global rational function on a proper smooth curve
is finite. This is the premise-free nonconstancy consumer needed for the geometric product
formula; the remaining work is to compare the zero and infinity fibres. -/
theorem isFinite_rationalFunctionMorphism_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a) :
    IsFinite (rationalFunctionMorphism K X f g) := by
  exact isFinite_rationalFunctionMorphism_of_no_universal_fiber K X f g
    (rationalFunctionMorphism_no_universal_fiber_of_nonGlobal K X f g hg)

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
