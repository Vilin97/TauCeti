/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective line and its generic points

This file realizes the projective line over a field `K` as the projective spectrum of the
standard grading on `K[X₀, X₁]`. A field extension map `K → F` and an element `g : F` determine
the `F`-valued point `[g : 1]`.

For an integral curve with function field `F`, this is the generic-point morphism attached to a
rational function. It is the first geometric input to the product formula in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace ProjectiveLine

noncomputable section

/-- The standard grading of the homogeneous coordinate ring `K[X₀, X₁]`. -/
abbrev homogeneousPieces (K : Type u) [Field K] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The standard graded-algebra structure on the homogeneous coordinate ring of the projective
line. Mathlib intentionally does not install this instance globally because multivariate
polynomials admit other weighted gradings. -/
noncomputable instance (K : Type u) [Field K] : GradedAlgebra (homogeneousPieces K) :=
  MvPolynomial.gradedAlgebra

/-- The projective line over `K`, realized as `Proj K[X₀, X₁]`. -/
abbrev scheme (K : Type u) [Field K] : Scheme.{u} :=
  Proj (homogeneousPieces K)

/-- The standard affine chart `D₊(X₁)` of the projective line. -/
abbrev standardAffineOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))

/-- The affine chart `D₊(X₀)` containing the point at infinity. -/
abbrev infinityAffineOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))

lemma X_one_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

lemma X_zero_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- The degree-zero homogeneous fraction `X₀ / X₁` on the standard affine chart. -/
@[expose] noncomputable def affineCoordinateAway (K : Type u) [Field K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

/-- The regular function `X₀ / X₁` on the standard affine chart `D₊(X₁)`. -/
@[expose] noncomputable def affineCoordinate (K : Type u) [Field K] :
  Γ(scheme K, standardAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one).hom (affineCoordinateAway K)

/-- The degree-zero homogeneous fraction `X₁ / X₀` on the affine chart containing
infinity. -/
@[expose] noncomputable def inverseAffineCoordinateAway (K : Type u) [Field K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

/-- The regular function `X₁ / X₀` on the affine chart `D₊(X₀)`. -/
@[expose] noncomputable def inverseAffineCoordinate (K : Type u) [Field K] :
    Γ(scheme K, infinityAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one).hom (inverseAffineCoordinateAway K)

/-- The constant-polynomial equivalence from `K` to the degree-zero part of `K[X₀, X₁]`. -/
@[expose]
noncomputable def degreeZeroRingEquiv (K : Type u) [Field K] :
    K ≃+* homogeneousPieces K 0 :=
  RingEquiv.ofBijective (algebraMap K (homogeneousPieces K 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 2) K (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 2) K) ∈
          (1 : Submodule K (MvPolynomial (Fin 2) K)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

@[simp]
lemma coe_degreeZeroRingEquiv_apply (K : Type u) [Field K] (r : K) :
    ((degreeZeroRingEquiv K r : homogeneousPieces K 0) : MvPolynomial (Fin 2) K) =
      MvPolynomial.C r := rfl

private def coordinatePolynomialHom (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : MvPolynomial (Fin 2) K →+* F :=
  MvPolynomial.eval₂Hom ι fun i ↦ if i = 0 then g else 1

private lemma coordinatePolynomialHom_X_zero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom K F ι g (MvPolynomial.X (0 : Fin 2)) = g := by
  simp [coordinatePolynomialHom]

private lemma coordinatePolynomialHom_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom K F ι g (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinatePolynomialHom]

/-- The affine-chart coordinate homomorphism sending `X₀ / X₁` to `g`. -/
private noncomputable def affineCoordinateRingHom
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+* F :=
  (Localization.awayLift (coordinatePolynomialHom K F ι g)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [coordinatePolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma affineCoordinateRingHom_affineCoordinateAway
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    affineCoordinateRingHom K F ι g (affineCoordinateAway K) = g := by
  simp only [affineCoordinateRingHom, RingHom.comp_apply, affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk (coordinatePolynomialHom K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [coordinatePolynomialHom_X_one]; simp) 1
  simpa [coordinatePolynomialHom] using h

private def inverseCoordinatePolynomialHom (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : MvPolynomial (Fin 2) K →+* F :=
  MvPolynomial.eval₂Hom ι fun i ↦ if i = 1 then g else 1

private lemma inverseCoordinatePolynomialHom_X_zero
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseCoordinatePolynomialHom K F ι g (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom]

private lemma inverseCoordinatePolynomialHom_X_one
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseCoordinatePolynomialHom K F ι g (MvPolynomial.X (1 : Fin 2)) = g := by
  simp [inverseCoordinatePolynomialHom]

private noncomputable def inverseAffineCoordinateRingHom
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →+* F :=
  (Localization.awayLift (inverseCoordinatePolynomialHom K F ι g)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

private lemma inverseAffineCoordinateRingHom_inverseAffineCoordinateAway
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    inverseAffineCoordinateRingHom K F ι g (inverseAffineCoordinateAway K) = g := by
  simp only [inverseAffineCoordinateRingHom, RingHom.comp_apply, inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk (inverseCoordinatePolynomialHom K F ι g)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 1
  simpa [inverseCoordinatePolynomialHom] using h

private lemma basicOpenIsoSpec_hom_appTop_affineCoordinateAway
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) =
      (standardAffineOpen K).topIso.inv (affineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (standardAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K))) =
    (standardAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (affineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_affineCoordinate
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).inv.appTop
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  change e.inv.appTop ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_affineCoordinateAway K).symm

private lemma awayι_preimage_standardAffineOpen (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ standardAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_affineCoordinate (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one).appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  have hres : φ.resLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (standardAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (standardAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((standardAffineOpen K).topIso.inv (affineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (φ.resLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge).app ⊤
        ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge)
            ((standardAffineOpen K).topIso.hom
              ((standardAffineOpen K).topIso.inv (affineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
            (affineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_affineCoordinate]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

private lemma basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) =
      (infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (infinityAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K))) =
    (infinityAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (inverseAffineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one).inv.appTop
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one
  change e.inv.appTop ((infinityAffineOpen K).topIso.inv
    (inverseAffineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway K).symm

private lemma awayι_preimage_infinityAffineOpen (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_inverseAffineCoordinate (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one).appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one
  have hres : φ.resLE (infinityAffineOpen K) ⊤
      (awayι_preimage_infinityAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (infinityAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (infinityAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge) (inverseAffineCoordinate K)) =
      (φ.resLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge).app ⊤
        ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen K).ge) (inverseAffineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen K).ge)
            ((infinityAffineOpen K).topIso.hom
              ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
            (inverseAffineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

/-- The `F`-valued point `[g : 1]` of the projective line associated to a field map `K → F`
and an element `g : F`.

For a curve function field, this is the generic-point morphism defined by the corresponding
rational function. The explicit field map makes the base-field structure part of the data and
avoids choosing a global `Algebra K F` instance. -/
noncomputable def ofElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)) ≫
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one

/-- The `F`-valued point `[1 : g]` of the projective line associated to a field map `K → F`
and an element `g : F`. -/
noncomputable def ofInverseElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom K F ι g)) ≫
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one

/-- The point `[1 : g]` lies in the affine chart `D₊(X₀)` containing infinity. -/
@[simp]
lemma ofInverseElement_preimage_basicOpen_X_zero
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    ofInverseElement K F ι g ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  rw [ofInverseElement, Scheme.Hom.comp_preimage]
  dsimp only [infinityAffineOpen]
  rw [
    ← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one]
  simp

/-- The point `[g : 1]` lies in the standard affine chart where the second homogeneous
coordinate is nonzero. -/
@[simp]
lemma ofElement_preimage_basicOpen_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤ := by
  rw [ofElement, Scheme.Hom.comp_preimage,
    ← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one]
  simp

/-- If `g` is nonzero, the point `[g : 1]` also lies in the affine chart `D₊(X₀)` containing
infinity. -/
lemma ofElement_preimage_basicOpen_X_zero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    ofElement K F ι g ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  rw [ofElement, Scheme.Hom.comp_preimage]
  dsimp only [infinityAffineOpen]
  have haway :
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
          (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (X_one_mem_degree_one K) (X_zero_mem_degree_one K)) :=
    Proj.awayι_preimage_basicOpen (𝒜 := homogeneousPieces K)
      (X_one_mem_degree_one K) zero_lt_one (X_zero_mem_degree_one K) zero_lt_one
  change Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)) ⁻¹ᵁ
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))) = ⊤
  rw [haway]
  rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (X_one_mem_degree_one K) (X_zero_mem_degree_one K) = affineCoordinateAway K := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, affineCoordinateAway,
      HomogeneousLocalization.Away.val_mk]
  rw [helem]
  have hcoord : (CommRingCat.ofHom (affineCoordinateRingHom K F ι g))
      (affineCoordinateAway K) = g :=
    affineCoordinateRingHom_affineCoordinateAway K F ι g
  rw [hcoord]
  have hbasic : PrimeSpectrum.basicOpen g =
      (⊤ : TopologicalSpace.Opens (PrimeSpectrum F)) := by
    ext p
    change (g ∉ p.asIdeal) ↔ True
    rw [Ideal.eq_bot_of_prime p.asIdeal]
    simp [hg]
  exact hbasic

private lemma inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap
    (K : Type u) [Field K] :
    HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_one_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) from rfl)
        (inverseAffineCoordinateAway K) *
      HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_zero_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) from mul_comm _ _)
        (affineCoordinateAway K) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    inverseAffineCoordinateAway, affineCoordinateAway,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

private abbrev affineOverlapOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

private lemma affineOverlapOpen_le_infinityAffineOpen (K : Type u) [Field K] :
    affineOverlapOpen K ≤ infinityAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (1 : Fin 2), rfl⟩

private lemma affineOverlapOpen_le_standardAffineOpen (K : Type u) [Field K] :
    affineOverlapOpen K ≤ standardAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (0 : Fin 2), mul_comm _ _⟩

private lemma inverseAffineCoordinate_mul_affineCoordinate_on_overlap
    (K : Type u) [Field K] :
    (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op
        (inverseAffineCoordinate K) *
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op
        (affineCoordinate K) = 1 := by
  change ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op)
        (inverseAffineCoordinateAway K)) *
    ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op)
        (affineCoordinateAway K)) = 1
  rw [← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_one_mem_degree_one K) rfl,
    ← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_zero_mem_degree_one K) (mul_comm _ _)]
  change (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_one_mem_degree_one K) rfl (inverseAffineCoordinateAway K)) *
    (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_zero_mem_degree_one K) (mul_comm _ _) (affineCoordinateAway K)) = 1
  rw [← map_mul, inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap, map_one]

private lemma ofElement_preimage_affineOverlapOpen
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    ofElement K F ι g ⁻¹ᵁ affineOverlapOpen K = ⊤ := by
  rw [affineOverlapOpen, Proj.basicOpen_mul, Scheme.Hom.preimage_inf,
    ofElement_preimage_basicOpen_X_zero K F ι g hg,
    ofElement_preimage_basicOpen_X_one, inf_top_eq]

/-- Pulling the standard affine coordinate `X₀ / X₁` back along `[g : 1]` gives `g`.

This is the computational interface needed to distinguish the rational-function morphism of a
non-global function from a constant morphism. -/
lemma ofElement_appLE_affineCoordinate (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    (ofElement K F ι g).appLE (standardAffineOpen K) ⊤
        (ofElement_preimage_basicOpen_X_one K F ι g).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g := by
  change ((Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).appLE
      (standardAffineOpen K) ⊤ (ofElement_preimage_basicOpen_X_one K F ι g).ge)
        (affineCoordinate K) = _
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)))
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one)
    (standardAffineOpen K) ⊤ ⊤ (awayι_preimage_standardAffineOpen K).ge le_rfl]
  simp only [CommRingCat.comp_apply, awayι_appLE_affineCoordinate]
  change (((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv ≫
        (Spec.map (CommRingCat.ofHom
          (affineCoordinateRingHom K F ι g))).appTop) (affineCoordinateAway K)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (Scheme.ΓSpecIso (.of F)).inv
    (affineCoordinateRingHom_affineCoordinateAway K F ι g)

/-- Pulling the inverse affine coordinate `X₁ / X₀` back along `[1 : g]` gives `g`. -/
lemma ofInverseElement_appLE_inverseAffineCoordinate
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    (ofInverseElement K F ι g).appLE (infinityAffineOpen K) ⊤
        (ofInverseElement_preimage_basicOpen_X_zero K F ι g).ge
        (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g := by
  change ((Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom K F ι g)) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) zero_lt_one).appLE
      (infinityAffineOpen K) ⊤
        (ofInverseElement_preimage_basicOpen_X_zero K F ι g).ge)
          (inverseAffineCoordinate K) = _
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (inverseAffineCoordinateRingHom K F ι g)))
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) zero_lt_one)
    (infinityAffineOpen K) ⊤ ⊤ (awayι_preimage_infinityAffineOpen K).ge le_rfl]
  simp only [CommRingCat.comp_apply, awayι_appLE_inverseAffineCoordinate]
  change (((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv ≫
        (Spec.map (CommRingCat.ofHom
          (inverseAffineCoordinateRingHom K F ι g))).appTop)
        (inverseAffineCoordinateAway K)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (Scheme.ΓSpecIso (.of F)).inv
    (inverseAffineCoordinateRingHom_inverseAffineCoordinateAway K F ι g)

/-- Pulling the inverse affine coordinate `X₁ / X₀` back along a nonzero point `[g : 1]`
gives `g⁻¹`. -/
lemma ofElement_appLE_inverseAffineCoordinate
    (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) (hg : g ≠ 0) :
    (ofElement K F ι g).appLE (infinityAffineOpen K) ⊤
        (ofElement_preimage_basicOpen_X_zero K F ι g hg).ge
        (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g⁻¹ := by
  let φ := ofElement K F ι g
  let W := affineOverlapOpen K
  have hW : φ ⁻¹ᵁ W = ⊤ := ofElement_preimage_affineOverlapOpen K F ι g hg
  have hInf : φ ⁻¹ᵁ infinityAffineOpen K = ⊤ :=
    ofElement_preimage_basicOpen_X_zero K F ι g hg
  have hStd : φ ⁻¹ᵁ standardAffineOpen K = ⊤ :=
    ofElement_preimage_basicOpen_X_one K F ι g
  have hInfPull :
      φ.appLE W ⊤ hW.ge
          ((scheme K).presheaf.map
            (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op
            (inverseAffineCoordinate K)) =
        φ.appLE (infinityAffineOpen K) ⊤ hInf.ge
          (inverseAffineCoordinate K) := by
    change (((scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op ≫
      φ.appLE W ⊤ hW.ge) (inverseAffineCoordinate K)) = _
    rw [Scheme.Hom.map_appLE]
  have hStdPull :
      φ.appLE W ⊤ hW.ge
          ((scheme K).presheaf.map
            (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op
            (affineCoordinate K)) =
        φ.appLE (standardAffineOpen K) ⊤ hStd.ge (affineCoordinate K) := by
    change (((scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op ≫
      φ.appLE W ⊤ hW.ge) (affineCoordinate K)) = _
    rw [Scheme.Hom.map_appLE]
  have hprod := congrArg (φ.appLE W ⊤ hW.ge)
    (inverseAffineCoordinate_mul_affineCoordinate_on_overlap K)
  simp only [map_mul, map_one] at hprod
  rw [hInfPull, hStdPull] at hprod
  have hcoord :
      φ.appLE (standardAffineOpen K) ⊤ hStd.ge (affineCoordinate K) =
        (Scheme.ΓSpecIso (.of F)).inv g := by
    exact ofElement_appLE_affineCoordinate K F ι g
  rw [hcoord] at hprod
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of F)).hom).1
  rw [Iso.inv_hom_id_apply]
  have hprodF := congrArg (Scheme.ΓSpecIso (.of F)).hom hprod
  simp only [map_mul, Iso.inv_hom_id_apply, map_one] at hprodF
  apply mul_right_cancel₀ hg
  rw [hprodF, inv_mul_cancel₀ hg]

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[g : 1]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofElement, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change affineCoordinateRingHom K F ι g
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) (degreeZeroRingEquiv K r)) = ι r
  simp only [affineCoordinateRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk (coordinatePolynomialHom K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [coordinatePolynomialHom_X_one]; simp) 0
  convert h using 1
  · congr 1
  · simp [coordinatePolynomialHom]

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[1 : g]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofInverseElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofInverseElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofInverseElement, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change inverseAffineCoordinateRingHom K F ι g
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2))) (degreeZeroRingEquiv K r)) = ι r
  simp only [inverseAffineCoordinateRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk (inverseCoordinatePolynomialHom K F ι g)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 0
  convert h using 1
  · congr 1
  · simp [inverseCoordinatePolynomialHom]

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti
