/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Flat
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Fibre degrees of the rational-function morphism

This file compares the local orders of a rational function with the finite-flat fibres of its
associated morphism to the projective line.  The first bridge identifies the pullback of the
standard affine coordinate with the original element of the function field.
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


/-- The residue degree of a morphism between affine spectra is the inertia degree of the
corresponding prime ideal. -/
theorem residueDegree_SpecMap_eq_inertiaDeg
    (R S : CommRingCat.{u}) (a : R ⟶ S) (q : PrimeSpectrum S) :
    letI : Algebra R S := a.hom.toAlgebra
    (Spec.map a).residueDegree q = q.asIdeal.inertiaDeg R := by
  letI : Algebra R S := a.hom.toAlgebra
  let p : PrimeSpectrum R := PrimeSpectrum.comap a.hom q
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := by
    constructor
    rfl
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : Algebra ((Spec R).residueField p) ((Spec S).residueField q) :=
    ((Spec.map a).residueFieldMap q).hom.toAlgebra
  change Module.finrank ((Spec R).residueField p) ((Spec S).residueField q) = _
  rw [Ideal.inertiaDeg_eq p.asIdeal q.asIdeal]
  apply Algebra.finrank_eq_of_equiv_equiv
    (Scheme.Spec.residueFieldIso R p).commRingCatIsoToRingEquiv
    (Scheme.Spec.residueFieldIso S q).commRingCatIsoToRingEquiv
  ext z
  obtain ⟨z, rfl⟩ := (Spec R).residue_surjective p z
  have hpIso :
      (Scheme.Spec.residueFieldIso R p).hom ((Spec R).residue p z) =
        algebraMap (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
          ((Spec.stalkIso R p).hom z) := by
    have h := congrArg (fun h ↦ h z)
      (Scheme.Spec.residue_residueFieldIso_hom R p)
    change (Scheme.Spec.residueFieldIso R p).hom ((Spec R).residue p z) =
      algebraMap (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
        ((Spec.stalkIso R p).hom z) at h
    exact h
  have hqIso (w : (Spec S).presheaf.stalk q) :
      (Scheme.Spec.residueFieldIso S q).hom ((Spec S).residue q w) =
        algebraMap (Localization.AtPrime q.asIdeal) q.asIdeal.ResidueField
          ((Spec.stalkIso S q).hom w) := by
    have h := congrArg (fun h ↦ h w)
      (Scheme.Spec.residue_residueFieldIso_hom S q)
    change (Scheme.Spec.residueFieldIso S q).hom ((Spec S).residue q w) =
      algebraMap (Localization.AtPrime q.asIdeal) q.asIdeal.ResidueField
        ((Spec.stalkIso S q).hom w) at h
    exact h
  have hresidue :
      (Spec.map a).residueFieldMap q ((Spec R).residue p z) =
        (Spec S).residue q ((Spec.map a).stalkMap q z) := by
    have h := congrArg (fun h ↦ h z)
      (Scheme.residue_residueFieldMap (Spec.map a) q)
    change (Spec.map a).residueFieldMap q ((Spec R).residue p z) =
      (Spec S).residue q ((Spec.map a).stalkMap q z) at h
    exact h
  have hlocal :
      algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
          ((Spec.stalkIso R p).hom z) =
        (Spec.stalkIso S q).hom ((Spec.map a).stalkMap q z) := by
    have h := congrArg (fun h ↦ h z) (Scheme.localRingHom_comp_stalkIso a q)
    change (Spec.stalkIso S q).inv
      (Localization.localRingHom p.asIdeal q.asIdeal a.hom (by rfl)
        ((Spec.stalkIso R p).hom z)) = (Spec.map a).stalkMap q z at h
    apply (ConcreteCategory.bijective_of_isIso (Spec.stalkIso S q).inv).1
    rw [Iso.hom_inv_id_apply]
    simpa only [p, RingHom.algebraMap_toAlgebra,
      Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq] using h
  calc
    algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField
        ((Scheme.Spec.residueFieldIso R p).hom ((Spec R).residue p z)) =
        algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField
          (algebraMap (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
            ((Spec.stalkIso R p).hom z)) := by rw [hpIso]
    _ = IsLocalRing.residue (Localization.AtPrime q.asIdeal)
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
          ((Spec.stalkIso R p).hom z)) :=
      IsLocalRing.ResidueField.algebraMap_residue _
    _ = IsLocalRing.residue (Localization.AtPrime q.asIdeal)
        ((Spec.stalkIso S q).hom ((Spec.map a).stalkMap q z)) := by rw [hlocal]
    _ = (Scheme.Spec.residueFieldIso S q).hom
        ((Spec S).residue q ((Spec.map a).stalkMap q z)) := (hqIso _).symm
    _ = (Scheme.Spec.residueFieldIso S q).hom
        ((Spec.map a).residueFieldMap q ((Spec R).residue p z)) := by rw [hresidue]

/-- If the prime downstairs is generated by one element, the ramification index is the order of
the image of that generator in the localization upstairs. -/
theorem ramificationIdx_eq_ord_algebraMap_of_eq_span_singleton
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (t : R) (hp : p = Ideal.span ({t} : Set R)) :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Ring.ord Sq (algebraMap R Sq t)).toNat := by
  rw [Ideal.ramificationIdx_eq p q, Ring.ord, hp, Ideal.map_span]
  congr 3
  all_goals rw [Set.image_singleton]

/-- The order defined by quotient length is invariant under a ring equivalence. -/
theorem ord_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) :
    Ring.ord R x = Ring.ord S (e x) := by
  rw [Ring.ord, Ring.ord]
  let I : Ideal R := Ideal.span ({x} : Set R)
  let J : Ideal S := Ideal.span ({e x} : Set S)
  have hJ : J = I.map e.toRingHom := by
    dsimp only [I, J]
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.toRingHom_eq_coe]
    congr 2
  let E : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hJ
  letI : Algebra (R ⧸ I) (S ⧸ J) := E.toRingHom.toAlgebra
  let Ealg : (R ⧸ I) ≃ₐ[(R ⧸ I)] (S ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := E) (fun z ↦ by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.id_apply]
      exact DFunLike.congr_fun (RingEquiv.toRingHom_eq_coe E) z |>.symm)
  calc
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = Module.length (R ⧸ I) (S ⧸ J) := Ealg.toLinearEquiv.length_eq
    _ = Module.length (S ⧸ J) (S ⧸ J) :=
      Module.length_eq_of_surjective E.surjective
    _ = Module.length S (S ⧸ J) :=
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

/-- Points of a fibre over a point in an affine chart correspond to prime ideals of the affine
preimage lying over the target prime. -/
noncomputable def fibrePointPrimesOverEquiv
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsAffineHom φ]
    (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
    letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
    {x : X // φ x = y} ≃ p.primesOver Γ(X, V) := by
  dsimp only
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let aComm := φ.appLE U V le_rfl
  let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  letI : Algebra Γ(Y, U) Γ(X, V) := aComm.hom.toAlgebra
  let toPrime : {x : X // φ x = y} → p.primesOver Γ(X, V) := fun x ↦ by
    have hxV : x.1 ∈ V := by
      change φ x.1 ∈ U
      rw [x.2]
      exact hy
    let q := (hV.primeIdealOf ⟨x.1, hxV⟩).asIdeal
    haveI : q.IsPrime := (hV.primeIdealOf ⟨x.1, hxV⟩).isPrime
    have hover : q.LiesOver p := by
      have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV
        (f := φ) le_rfl hxV
      constructor
      simpa only [p, q, RingHom.algebraMap_toAlgebra, PrimeSpectrum.comap_asIdeal,
        Ideal.under_def, x.2] using
        congrArg PrimeSpectrum.asIdeal hcomap |>.symm
    exact ⟨q, inferInstance, hover⟩
  let fromPrime : p.primesOver Γ(X, V) → {x : X // φ x = y} := fun q ↦ by
    let q' : Spec Γ(X, V) := ⟨q.1, q.2.1⟩
    refine ⟨hV.fromSpec q', ?_⟩
    have hmap : Spec.map aComm q' = hU.primeIdealOf ⟨y, hy⟩ := by
      change PrimeSpectrum.comap aComm.hom q' = hU.primeIdealOf ⟨y, hy⟩
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      simpa only [p, RingHom.algebraMap_toAlgebra, Ideal.under_def] using q.2.2.over.symm
    have hsq : Spec.map aComm ≫ hU.fromSpec = hV.fromSpec ≫ φ :=
      IsAffineOpen.SpecMap_appLE_fromSpec φ hU hV le_rfl
    have happ : hU.fromSpec (Spec.map aComm q') = φ (hV.fromSpec q') := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun ψ ↦ ψ q') hsq
    rw [hmap, hU.fromSpec_primeIdealOf] at happ
    exact happ.symm
  refine
    { toFun := toPrime
      invFun := fromPrime
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    dsimp only [fromPrime, toPrime]
    change hV.fromSpec (hV.primeIdealOf ⟨x.1, _⟩) = x.1
    exact hV.fromSpec_primeIdealOf _
  · intro q
    apply Subtype.ext
    dsimp only [fromPrime, toPrime]
    let q' : Spec Γ(X, V) := ⟨q.1, q.2.1⟩
    have hqV : hV.fromSpec q' ∈ V := by
      change hV.fromSpec q' ∈ (V : Set X)
      rw [← hV.range_fromSpec]
      exact Set.mem_range_self q'
    have heq : hV.primeIdealOf ⟨hV.fromSpec q', hqV⟩ = q' := by
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [hV.fromSpec_primeIdealOf]
    simpa only [q'] using congrArg PrimeSpectrum.asIdeal heq

/-- The prime ideal underlying the fibre-point equivalence is the affine-chart prime of the
source point. -/
@[simp]
theorem fibrePointPrimesOverEquiv_apply_val
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsAffineHom φ]
    (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    (x : {x : X // φ x = y}) :
    let V := φ ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage φ
    let a := φ.appLE U V le_rfl
    letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
    (fibrePointPrimesOverEquiv φ U hU y hy x).1 =
      (hV.primeIdealOf ⟨x.1, by
        change φ x.1 ∈ U
        rw [x.2]
        exact hy⟩).asIdeal := by
  rfl

/-- In an affine chart, the inertia degree of the prime corresponding to a source point is the
residue degree of the original scheme morphism at that point. -/
theorem inertiaDeg_primeIdealOf_app_eq_residueDegree
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsAffineHom φ]
    (U : Y.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ φ ⁻¹ᵁ U) :
    let V := φ ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage φ
    let a := φ.appLE U V le_rfl
    letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.inertiaDeg Γ(Y, U) =
      φ.residueDegree x := by
  dsimp only
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let a := φ.appLE U V le_rfl
  letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
  let q : Spec Γ(X, V) := hV.primeIdealOf ⟨x, hx⟩
  have hspec := residueDegree_SpecMap_eq_inertiaDeg Γ(Y, U) Γ(X, V) a q
  have hsq : Spec.map a ≫ hU.fromSpec = hV.fromSpec ≫ φ :=
    IsAffineOpen.SpecMap_appLE_fromSpec φ hU hV le_rfl
  have hdegree := congrArg
    (fun ψ : Spec Γ(X, V) ⟶ Y ↦ ψ.residueDegree q) hsq
  have hdegree' :
      hU.fromSpec.residueDegree (Spec.map a q) * (Spec.map a).residueDegree q =
        φ.residueDegree (hV.fromSpec q) * hV.fromSpec.residueDegree q := by
    calc
      _ = (Spec.map a ≫ hU.fromSpec).residueDegree q :=
        (residueDegree_comp (Spec.map a) hU.fromSpec q).symm
      _ = (hV.fromSpec ≫ φ).residueDegree q := hdegree
      _ = _ := residueDegree_comp hV.fromSpec φ q
  have hUone : hU.fromSpec.residueDegree (Spec.map a q) = 1 :=
    (residueDegree_eq_one_iff hU.fromSpec _).mpr
      (ConcreteCategory.bijective_of_isIso _)
  have hVone : hV.fromSpec.residueDegree q = 1 :=
    (residueDegree_eq_one_iff hV.fromSpec _).mpr
      (ConcreteCategory.bijective_of_isIso _)
  rw [hUone, hVone, one_mul, mul_one, hV.fromSpec_primeIdealOf] at hdegree'
  exact hspec.symm.trans hdegree'

/-- For a finite flat morphism, the ramification-index/inertia-degree sum over an affine fibre
is the scheme-theoretic finite-flat rank at the target point. -/
theorem sum_ramification_inertia_app_eq_finrank
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsFinite φ] [Flat φ]
    (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
    letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
    letI : Module.Finite Γ(Y, U) Γ(X, V) := by
      change a.hom.Finite
      simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
    letI : Fintype (p.primesOver Γ(X, V)) :=
      (Algebra.QuasiFinite.finite_primesOver p).fintype
    ∑ q : p.primesOver Γ(X, V),
      q.1.ramificationIdx Γ(Y, U) * q.1.inertiaDeg Γ(Y, U) =
        φ.finrank y := by
  dsimp only
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let aComm : R ⟶ S := φ.appLE U V le_rfl
  let a : R →+* S := aComm.hom
  let p : Ideal R := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨y, hy⟩).isPrime
  letI : Algebra R S := a.toAlgebra
  letI : Module.Finite R S := by
    change a.Finite
    simpa [a, aComm, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Module.Flat R S := by
    rw [← RingHom.flat_algebraMap_iff]
    simpa [a, aComm, RingHom.algebraMap_toAlgebra] using φ.flat_appLE hU hV le_rfl
  letI : Fintype (p.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hsq : Spec.map aComm ≫ hU.fromSpec = hV.fromSpec ≫ φ :=
    IsAffineOpen.SpecMap_appLE_fromSpec φ hU hV le_rfl
  have hpb : IsPullback (Spec.map aComm) hV.fromSpec hU.fromSpec φ := by
    apply IsOpenImmersion.isPullback
    · exact hsq.symm
    · rw [hU.opensRange_fromSpec, hV.opensRange_fromSpec]
  calc
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R =
        Module.finrank p.ResidueField (p.Fiber S) :=
      Ideal.sum_ramification_inertia_eq_finrank_fiber p S
    _ = Module.rankAtStalk S ⟨p, inferInstance⟩ :=
      p.finrank_fiber_eq_rankAtStalk
    _ = (Spec.map aComm).finrank (hU.primeIdealOf ⟨y, hy⟩) := by
      rw [Scheme.Hom.finrank_SpecMap_eq_finrank
        (by simpa [aComm, V, φ.appLE_eq_app] using φ.finite_app U hU)
        (φ.flat_appLE hU hV le_rfl)]
      rfl
    _ = φ.finrank y := by
      have hrank := Scheme.Hom.finrank_of_isPullback hV.fromSpec (Spec.map aComm)
        φ hU.fromSpec hpb.flip (hU.primeIdealOf ⟨y, hy⟩)
      rw [hU.fromSpec_primeIdealOf] at hrank
      exact hrank

/-- The affine finite-flat fibre formula with the inertia degrees replaced by geometric residue
degrees.  The equivalence with the fibre is kept explicit so the summation still uses the canonical
`primesOver` fintype. -/
theorem sum_ramification_residueDegree_app_eq_finrank
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsFinite φ] [Flat φ]
    (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
    letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
    letI : Module.Finite Γ(Y, U) Γ(X, V) := by
      change a.hom.Finite
      simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
    letI : Fintype (p.primesOver Γ(X, V)) :=
      (Algebra.QuasiFinite.finite_primesOver p).fintype
    let e := fibrePointPrimesOverEquiv φ U hU y hy
    ∑ q : p.primesOver Γ(X, V),
      q.1.ramificationIdx Γ(Y, U) * φ.residueDegree (e.symm q).1 =
        φ.finrank y := by
  dsimp only
  let V := φ ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage φ
  let a := φ.appLE U V le_rfl
  let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  letI : p.IsPrime := (hU.primeIdealOf ⟨y, hy⟩).isPrime
  letI : Algebra Γ(Y, U) Γ(X, V) := a.hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, V) := by
    change a.hom.Finite
    simpa [a, V, φ.appLE_eq_app] using φ.finite_app U hU
  letI : Fintype (p.primesOver Γ(X, V)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let e := fibrePointPrimesOverEquiv φ U hU y hy
  have hbase := sum_ramification_inertia_app_eq_finrank φ U hU y hy
  calc
    ∑ q : p.primesOver Γ(X, V),
        q.1.ramificationIdx Γ(Y, U) * φ.residueDegree (e.symm q).1 =
        ∑ q : p.primesOver Γ(X, V),
          q.1.ramificationIdx Γ(Y, U) * q.1.inertiaDeg Γ(Y, U) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      let x := e.symm q
      have hxV : x.1 ∈ V := by
        change φ x.1 ∈ U
        rw [x.2]
        exact hy
      have hlocal := inertiaDeg_primeIdealOf_app_eq_residueDegree
        φ U hU x.1 hxV
      have heq := congrArg Subtype.val (e.apply_symm_apply q)
      change (hV.primeIdealOf ⟨x.1, _⟩).asIdeal = q.1 at heq
      rw [← heq]
      exact hlocal.symm
    _ = φ.finrank y := hbase

/-- For a non-global rational function, the ramification/inertia sum above the zero point of
`ℙ¹` is the finite-flat degree of its projective-line morphism.  The target prime is normalized
to the principal ideal generated by `X₀ / X₁`. -/
theorem sum_ramification_inertia_zero_eq_finrank_rationalFunctionMorphism
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ b : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ b) :
    let φ := rationalFunctionMorphism K X f g
    let U := ProjectiveLine.standardAffineOpen K
    let V := φ ⁻¹ᵁ U
    let a := φ.appLE U V le_rfl
    let p := Ideal.span ({ProjectiveLine.affineCoordinate K} : Set
      Γ(ProjectiveLine.scheme K, U))
    letI : p.IsPrime := ProjectiveLine.span_affineCoordinate_isPrime K
    letI : Algebra Γ(ProjectiveLine.scheme K, U) Γ(X, V) := a.hom.toAlgebra
    letI : Module.Finite Γ(ProjectiveLine.scheme K, U) Γ(X, V) := by
      change a.hom.Finite
      letI : IsFinite φ :=
        isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
      simpa [a, V, φ.appLE_eq_app] using φ.finite_app U
        (ProjectiveLine.isAffineOpen_standardAffineOpen K)
    letI : Fintype (p.primesOver Γ(X, V)) :=
      (Algebra.QuasiFinite.finite_primesOver p).fintype
    ∑ q : p.primesOver Γ(X, V),
      q.1.ramificationIdx Γ(ProjectiveLine.scheme K, U) *
        q.1.inertiaDeg Γ(ProjectiveLine.scheme K, U) =
      φ.finrank (ProjectiveLine.zeroPoint K) := by
  dsimp only
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ :=
    isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ :=
    flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  let U := ProjectiveLine.standardAffineOpen K
  let hU := ProjectiveLine.isAffineOpen_standardAffineOpen K
  let hz := ProjectiveLine.zeroPoint_mem_standardAffineOpen K
  have h := sum_ramification_inertia_app_eq_finrank φ U hU
    (ProjectiveLine.zeroPoint K) hz
  have hp : (hU.primeIdealOf ⟨ProjectiveLine.zeroPoint K, hz⟩).asIdeal =
      Ideal.span ({ProjectiveLine.affineCoordinate K} : Set
        Γ(ProjectiveLine.scheme K, U)) := by
    exact ProjectiveLine.primeIdealOf_zeroPoint_asIdeal_of_mem K hz
  rw [hp] at h
  simpa only [φ, U] using h

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
