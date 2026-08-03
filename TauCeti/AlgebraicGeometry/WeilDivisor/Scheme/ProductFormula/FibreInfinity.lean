/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.FibreZero

/-!
# The infinity fibre and sign loci of a rational function

This file treats the infinity fibre and identifies the positive and negative order loci with the
zero and infinity fibres of the associated projective-line morphism.
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

/-- A point above infinity of a non-global rational function is a codimension-one point of the
source curve. -/
noncomputable def infinityFibreCodimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.infinityPoint K}) :
    CodimensionOnePoint X := by
  refine ⟨x.1, coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
    K X f x.1 ?_⟩
  intro hx
  have himage := congrArg (rationalFunctionMorphism K X f g) hx
  rw [x.2, rationalFunctionMorphism_genericPoint_eq_genericPoint_of_nonGlobal
    K X f g hg] at himage
  exact ProjectiveLine.infinityPoint_ne_genericPoint K himage

/-- The canonical codimension-one point above infinity has the original fibre point as its
underlying scheme point. -/
@[simp]
theorem infinityFibreCodimensionOnePoint_val
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.infinityPoint K}) :
    (infinityFibreCodimensionOnePoint K X f g hg x).1 = x.1 := by
  rfl

/-- Above the point at infinity, the affine ramification index is the negative of the
scheme-theoretic order of the rational function. -/
theorem ramificationIdx_primeIdealOf_infinity_eq_neg_orderAt
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : CodimensionOnePoint X)
    (hxinf : rationalFunctionMorphism K X f g x.1 = ProjectiveLine.infinityPoint K) :
    let φ := rationalFunctionMorphism K X f g
    letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
    let U := ProjectiveLine.infinityAffineOpen K
    let hxU : φ x.1 ∈ U := by
      rw [hxinf]
      exact ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
    let V := φ ⁻¹ᵁ U
    let hV : IsAffineOpen V :=
      (ProjectiveLine.isAffineOpen_infinityAffineOpen K).preimage φ
    let a := φ.appLE U V le_rfl
    letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
    let q := (hV.primeIdealOf ⟨x.1, hxU⟩).asIdeal
    (q.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) = -orderAt x g := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
  have hxU : φ x.1 ∈ U := by
    rw [hxinf]
    exact hinf
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let R := Γ(ProjectiveLine.scheme K, U)
  let S := Γ(X, V)
  let a : R ⟶ S := φ.appLE U V le_rfl
  let t : R := ProjectiveLine.inverseAffineCoordinate K
  let p : Ideal R :=
    (hU.primeIdealOf ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
  let q : Ideal S := (hV.primeIdealOf ⟨x.1, hxU⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf
    ⟨ProjectiveLine.infinityPoint K, hinf⟩).isPrime
  letI : q.IsPrime := (hV.primeIdealOf ⟨x.1, hxU⟩).isPrime
  letI : Algebra R S := a.hom.toAlgebra
  have hover : q.LiesOver p := by
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV
      (f := φ) le_rfl hxU
    constructor
    calc
      p = (hU.primeIdealOf ⟨φ x.1, hxU⟩).asIdeal := by
        exact congrArg PrimeSpectrum.asIdeal
          (congrArg hU.primeIdealOf (Subtype.ext hxinf.symm))
      _ = Ideal.comap a.hom q := by
        simpa only [a, q, PrimeSpectrum.comap_asIdeal] using
          congrArg PrimeSpectrum.asIdeal hcomap |>.symm
      _ = q.under R := by
        rw [Ideal.under_def, RingHom.algebraMap_toAlgebra]
  letI : q.LiesOver p := hover
  have hp : p = Ideal.span ({t} : Set R) := by
    exact ProjectiveLine.primeIdealOf_infinityPoint_asIdeal_of_mem K hinf
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
  have horder := neg_orderAt_eq_ord_stalkMap_inverseAffineCoordinate K X f g x hxU
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
    _ = -orderAt x g := horder.symm

/-- The order/residue-degree sum above infinity is the negative finite-flat degree of the
rational-function morphism. -/
theorem sum_orderAt_residueDegree_infinity_eq_neg_finrank
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    let φ := rationalFunctionMorphism K X f g
    letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
    letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
    let U := ProjectiveLine.infinityAffineOpen K
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
    let p := ((ProjectiveLine.isAffineOpen_infinityAffineOpen K).primeIdealOf
      ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
    letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
    letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
      change a.hom.Finite
      simpa [a, V, φ.appLE_eq_app] using φ.finite_app U
        (ProjectiveLine.isAffineOpen_infinityAffineOpen K)
    letI : Fintype (p.primesOver Γ(X, V)) :=
      (Algebra.QuasiFinite.finite_primesOver p).fintype
    let e := fibrePointPrimesOverEquiv φ U
      (ProjectiveLine.isAffineOpen_infinityAffineOpen K)
      (ProjectiveLine.infinityPoint K) hinf
    ∑ q : p.primesOver Γ(X, V),
      orderAt (infinityFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
        (φ.residueDegree (e.symm q).1 : ℤ) =
      -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ := flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let a := φ.appLE U V le_rfl
  let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf
    ⟨ProjectiveLine.infinityPoint K, hinf⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.infinityPoint K) hinf
  have hbase := sum_ramification_residueDegree_app_eq_finrank
    φ U hU (ProjectiveLine.infinityPoint K) hinf
  calc
    ∑ q : p.primesOver Γ(X, V),
        orderAt (infinityFibreCodimensionOnePoint K X f g hg (e.symm q)) g *
          (φ.residueDegree (e.symm q).1 : ℤ) =
        ∑ q : p.primesOver Γ(X, V),
          -(q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) *
            (φ.residueDegree (e.symm q).1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      let z := infinityFibreCodimensionOnePoint K X f g hg (e.symm q)
      have hzmap : φ z.1 = ProjectiveLine.infinityPoint K := (e.symm q).2
      have hlocal := ramificationIdx_primeIdealOf_infinity_eq_neg_orderAt
        K X f g hg z hzmap
      dsimp only at hlocal
      have hzV : z.1 ∈ V := by
        change φ z.1 ∈ U
        rw [hzmap]
        exact hinf
      have heq : (hV.primeIdealOf ⟨z.1, hzV⟩).asIdeal = q.1 := by
        simpa only [e, z, fibrePointPrimesOverEquiv_apply_val,
          infinityFibreCodimensionOnePoint_val] using
            congrArg Subtype.val (e.apply_symm_apply q)
      rw [heq] at hlocal
      simpa only [z, neg_neg] using congrArg Neg.neg hlocal.symm
    _ = -∑ q : p.primesOver Γ(X, V),
          (q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) *
            (φ.residueDegree (e.symm q).1 : ℤ) := by
      change Finset.univ.sum (fun q ↦
          -(q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) *
            (φ.residueDegree (e.symm q).1 : ℤ)) =
        -Finset.univ.sum (fun q ↦
          (q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) *
            (φ.residueDegree (e.symm q).1 : ℤ))
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = -(φ.finrank (ProjectiveLine.infinityPoint K) : ℤ) := by
      exact congrArg Neg.neg (by exact_mod_cast hbase)

/-- The order of a rational function is nonnegative at every point lying in the standard affine
chart of its map to `ℙ¹`. -/
theorem orderAt_nonneg_of_mem_standardAffineOpen
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hx : rationalFunctionMorphism K X f g x.1 ∈
      ProjectiveLine.standardAffineOpen K) :
    0 ≤ orderAt x g := by
  rw [orderAt_eq_ord_stalkMap_affineCoordinate K X f g x hx]
  exact Int.natCast_nonneg _

/-- Away from the zero point, the standard affine coordinate is a unit in the target stalk, so
the corresponding rational-function order is zero. -/
theorem orderAt_eq_zero_of_mem_standardAffineOpen_of_ne_zeroPoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hx : rationalFunctionMorphism K X f g x.1 ∈
      ProjectiveLine.standardAffineOpen K)
    (hne : rationalFunctionMorphism K X f g x.1 ≠ ProjectiveLine.zeroPoint K) :
    orderAt x g = 0 := by
  let φ := rationalFunctionMorphism K X f g
  let Y := ProjectiveLine.scheme K
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let y := φ x.1
  let R := Γ(Y, U)
  let t : R := ProjectiveLine.affineCoordinate K
  let p : Ideal R := (hU.primeIdealOf ⟨y, hx⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨y, hx⟩).isPrime
  have htNot : t ∉ p := by
    intro ht
    exact hne ((ProjectiveLine.affineCoordinate_mem_primeIdealOf_iff_eq_zeroPoint
      K y hx).mp ht)
  letI : Algebra R (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hx⟩
  letI : IsLocalization.AtPrime (Y.presheaf.stalk y) p :=
    hU.isLocalization_stalk ⟨y, hx⟩
  have htUnit : IsUnit (Y.presheaf.germ U y hx t) := by
    change IsUnit (algebraMap R (Y.presheaf.stalk y) t)
    exact IsLocalization.map_units _ (⟨t, htNot⟩ : p.primeCompl)
  have hsourceUnit := htUnit.map (φ.stalkMap x.1).hom
  rw [orderAt_eq_ord_stalkMap_affineCoordinate K X f g x hx]
  rw [Ring.ord_of_isUnit hsourceUnit]
  rfl

/-- Away from the point at infinity, the inverse affine coordinate is a unit in the target
stalk, so the corresponding rational-function order is zero. -/
theorem orderAt_eq_zero_of_mem_infinityAffineOpen_of_ne_infinityPoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hx : rationalFunctionMorphism K X f g x.1 ∈
      ProjectiveLine.infinityAffineOpen K)
    (hne : rationalFunctionMorphism K X f g x.1 ≠ ProjectiveLine.infinityPoint K) :
    orderAt x g = 0 := by
  let φ := rationalFunctionMorphism K X f g
  let Y := ProjectiveLine.scheme K
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let y := φ x.1
  let R := Γ(Y, U)
  let t : R := ProjectiveLine.inverseAffineCoordinate K
  let p : Ideal R := (hU.primeIdealOf ⟨y, hx⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨y, hx⟩).isPrime
  have htNot : t ∉ p := by
    intro ht
    exact hne
      ((ProjectiveLine.inverseAffineCoordinate_mem_primeIdealOf_iff_eq_infinityPoint
        K y hx).mp ht)
  letI : Algebra R (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hx⟩
  letI : IsLocalization.AtPrime (Y.presheaf.stalk y) p :=
    hU.isLocalization_stalk ⟨y, hx⟩
  have htUnit : IsUnit (Y.presheaf.germ U y hx t) := by
    change IsUnit (algebraMap R (Y.presheaf.stalk y) t)
    exact IsLocalization.map_units _ (⟨t, htNot⟩ : p.primeCompl)
  have hsourceUnit := htUnit.map (φ.stalkMap x.1).hom
  have hneg := neg_orderAt_eq_ord_stalkMap_inverseAffineCoordinate K X f g x hx
  rw [Ring.ord_of_isUnit hsourceUnit] at hneg
  simpa only [ENat.toNat_zero, Int.ofNat_zero, neg_eq_zero] using hneg

/-- Every nonzero order occurs above either zero or infinity of the projective-line morphism. -/
theorem rationalFunctionMorphism_eq_zero_or_infinity_of_orderAt_ne_zero
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hne : orderAt x g ≠ 0) :
    rationalFunctionMorphism K X f g x.1 = ProjectiveLine.zeroPoint K ∨
      rationalFunctionMorphism K X f g x.1 = ProjectiveLine.infinityPoint K := by
  let φ := rationalFunctionMorphism K X f g
  have hmem : φ x.1 ∈
      ProjectiveLine.standardAffineOpen K ⊔ ProjectiveLine.infinityAffineOpen K := by
    rw [ProjectiveLine.standardAffineOpen_sup_infinityAffineOpen_eq_top]
    trivial
  change φ x.1 ∈ ProjectiveLine.standardAffineOpen K ∨
    φ x.1 ∈ ProjectiveLine.infinityAffineOpen K at hmem
  rcases hmem with hxStd | hxInf
  · left
    by_contra hzero
    exact hne (orderAt_eq_zero_of_mem_standardAffineOpen_of_ne_zeroPoint
      K X f g x hxStd hzero)
  · right
    by_contra hinf
    exact hne (orderAt_eq_zero_of_mem_infinityAffineOpen_of_ne_infinityPoint
      K X f g x hxInf hinf)

/-- Positive orders are exactly on the zero fibre. -/
theorem rationalFunctionMorphism_eq_zeroPoint_of_orderAt_pos
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hpos : 0 < orderAt x g) :
    rationalFunctionMorphism K X f g x.1 = ProjectiveLine.zeroPoint K := by
  rcases rationalFunctionMorphism_eq_zero_or_infinity_of_orderAt_ne_zero
    K X f g x hpos.ne' with hzero | hinf
  · exact hzero
  · have hxInf : rationalFunctionMorphism K X f g x.1 ∈
        ProjectiveLine.infinityAffineOpen K := by
      rw [hinf]
      exact ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
    have hneg := neg_orderAt_eq_ord_stalkMap_inverseAffineCoordinate K X f g x hxInf
    have hnonneg : 0 ≤ -orderAt x g := by
      rw [hneg]
      exact Int.natCast_nonneg _
    exact (not_lt_of_ge (neg_nonneg.mp hnonneg) hpos).elim

/-- Negative orders are exactly on the infinity fibre. -/
theorem rationalFunctionMorphism_eq_infinityPoint_of_orderAt_neg
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ) (x : CodimensionOnePoint X)
    (hneg : orderAt x g < 0) :
    rationalFunctionMorphism K X f g x.1 = ProjectiveLine.infinityPoint K := by
  rcases rationalFunctionMorphism_eq_zero_or_infinity_of_orderAt_ne_zero
    K X f g x hneg.ne with hzero | hinf
  · have hxStd : rationalFunctionMorphism K X f g x.1 ∈
        ProjectiveLine.standardAffineOpen K := by
      rw [hzero]
      exact ProjectiveLine.zeroPoint_mem_standardAffineOpen K
    have hnonneg := orderAt_nonneg_of_mem_standardAffineOpen K X f g x hxStd
    exact (not_lt_of_ge hnonneg hneg).elim
  · exact hinf

/-- The zero fibre of a non-global rational function is canonically equivalent to the
codimension-one points where its order is positive. -/
noncomputable def zeroFibreEquivPositiveOrder
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    {x : X // rationalFunctionMorphism K X f g x = ProjectiveLine.zeroPoint K} ≃
      {x : CodimensionOnePoint X // 0 < orderAt x g} := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
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
  let toPositive :
      {x : X // φ x = ProjectiveLine.zeroPoint K} →
        {x : CodimensionOnePoint X // 0 < orderAt x g} := fun x ↦ by
    let z := zeroFibreCodimensionOnePoint K X f g hg x
    let q := e x
    refine ⟨z, ?_⟩
    have hzmap : φ z.1 = ProjectiveLine.zeroPoint K := by
      simpa only [z, zeroFibreCodimensionOnePoint_val] using x.2
    have hlocal := ramificationIdx_primeIdealOf_zero_eq_orderAt
      K X f g hg z hzmap
    dsimp only at hlocal
    have hzV : z.1 ∈ V := by
      change φ z.1 ∈ U
      rw [hzmap]
      exact hz
    have heq : (hV.primeIdealOf ⟨z.1, hzV⟩).asIdeal = q.1 := by
      symm
      simpa only [q, e, z, zeroFibreCodimensionOnePoint_val] using
        fibrePointPrimesOverEquiv_apply_val φ U hU
          (ProjectiveLine.zeroPoint K) hz x
    rw [heq] at hlocal
    have hram : 0 < (q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) := by
      exact_mod_cast q.1.ramificationIdx_pos Γ(ProjectiveLine.scheme K, U)
    rw [hlocal] at hram
    exact hram
  refine
    { toFun := toPositive
      invFun := fun x ↦ ⟨x.1.1,
        rationalFunctionMorphism_eq_zeroPoint_of_orderAt_pos K X f g x.1 x.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp only [toPositive, zeroFibreCodimensionOnePoint_val]
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    simp only [toPositive, zeroFibreCodimensionOnePoint_val]

/-- The positive-order point underlying the zero-fibre equivalence is the canonical
codimension-one point attached to the fibre point. -/
@[simp]
theorem zeroFibreEquivPositiveOrder_apply_val
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.zeroPoint K}) :
    (zeroFibreEquivPositiveOrder K X f g hg x).1 =
      zeroFibreCodimensionOnePoint K X f g hg x := by
  rfl


/-- The infinity fibre of a non-global rational function is canonically equivalent to the
codimension-one points where its order is negative. -/
noncomputable def infinityFibreEquivNegativeOrder
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    {x : X // rationalFunctionMorphism K X f g x = ProjectiveLine.infinityPoint K} ≃
      {x : CodimensionOnePoint X // orderAt x g < 0} := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.infinityAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_infinityAffineOpen K
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let a := φ.appLE U V le_rfl
  let hinf := ProjectiveLine.infinityPoint_mem_infinityAffineOpen K
  let p := (hU.primeIdealOf ⟨ProjectiveLine.infinityPoint K, hinf⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf
    ⟨ProjectiveLine.infinityPoint K, hinf⟩).isPrime
  letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU (ProjectiveLine.infinityPoint K) hinf
  let toNegative :
      {x : X // φ x = ProjectiveLine.infinityPoint K} →
        {x : CodimensionOnePoint X // orderAt x g < 0} := fun x ↦ by
    let z := infinityFibreCodimensionOnePoint K X f g hg x
    let q := e x
    refine ⟨z, ?_⟩
    have hlocal := ramificationIdx_primeIdealOf_infinity_eq_neg_orderAt
      K X f g hg z x.2
    dsimp only at hlocal
    have hzV : z.1 ∈ V := by
      change φ z.1 ∈ U
      change φ x.1 ∈ U
      rw [x.2]
      exact hinf
    have heq : (hV.primeIdealOf ⟨z.1, hzV⟩).asIdeal = q.1 := by
      symm
      simpa only [q, e, z, infinityFibreCodimensionOnePoint_val] using
        fibrePointPrimesOverEquiv_apply_val φ U hU
          (ProjectiveLine.infinityPoint K) hinf x
    rw [heq] at hlocal
    have hram : 0 < (q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) : ℤ) := by
      exact_mod_cast q.1.ramificationIdx_pos Γ(ProjectiveLine.scheme K, U)
    rw [hlocal] at hram
    exact (neg_pos.mp hram)
  refine
    { toFun := toNegative
      invFun := fun x ↦ ⟨x.1.1,
        rationalFunctionMorphism_eq_infinityPoint_of_orderAt_neg K X f g x.1 x.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change x.1 = x.1
    rfl
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change x.1.1 = x.1.1
    rfl

/-- The negative-order point underlying the infinity-fibre equivalence is the canonical
codimension-one point attached to the fibre point. -/
@[simp]
theorem infinityFibreEquivNegativeOrder_apply_val
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b)
    (x : {x : X // rationalFunctionMorphism K X f g x =
      ProjectiveLine.infinityPoint K}) :
    (infinityFibreEquivNegativeOrder K X f g hg x).1 =
      infinityFibreCodimensionOnePoint K X f g hg x := by
  rfl

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
