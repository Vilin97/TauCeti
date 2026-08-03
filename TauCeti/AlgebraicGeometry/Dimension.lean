/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.RingTheory.KrullDimension.NoetherNormalization

/-!
# Dimension of schemes over a field

This file connects the topological definition of the dimension of a scheme with the
ring-theoretic Krull dimension of its affine charts. It then combines affine charts with
Noether normalization to prove dimension additivity for products of nonempty finite-type
schemes over a field.

The product theorem is the scheme-theoretic input to dimension additivity for products of
abelian varieties.
-/

public section

open CategoryTheory Limits Order TopologicalSpace Topology
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

attribute [local instance] specializationOrder

private theorem iSup_coe_add_iSup_coe {I J : Type*} [Nonempty I] [Nonempty J]
    (a : I → ℕ∞) (b : J → ℕ∞) :
    (⨆ i, (a i : WithBot ℕ∞)) + (⨆ j, (b j : WithBot ℕ∞)) =
      ⨆ i, ⨆ j, ((a i + b j : ℕ∞) : WithBot ℕ∞) := by
  rw [← WithBot.coe_iSup (OrderTop.bddAbove (Set.range a)),
    ← WithBot.coe_iSup (OrderTop.bddAbove (Set.range b)), ← WithBot.coe_add,
    ENat.iSup_add]
  simp_rw [ENat.add_iSup]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  congr 1
  funext i
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]

/-- On a sober `T₀` space, topological Krull dimension agrees with the Krull dimension of its
specialization order. -/
theorem topologicalKrullDim_eq_orderKrullDim (X : Type*) [TopologicalSpace X]
    [QuasiSober X] [T0Space X] :
    topologicalKrullDim X = krullDim X := by
  rw [topologicalKrullDim]
  exact Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))

/-- Topological Krull dimension is the supremum of point coheights in the specialization order. -/
theorem topologicalKrullDim_eq_iSup_coheight (X : Type*) [TopologicalSpace X]
    [QuasiSober X] [T0Space X] :
    topologicalKrullDim X = ⨆ x : X, (Order.coheight x : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_iSup_coheight]

/-- The dimension of an affine scheme is the Krull dimension of its global section ring. -/
theorem Scheme.topologicalKrullDim_eq_ringKrullDim (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  calc
    topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
      X.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, ⊤) := by
      change topologicalKrullDim (PrimeSpectrum Γ(X, ⊤)) = _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]

/-- Dimension additivity for the fibre product of two affine schemes over a field. -/
theorem Scheme.topologicalKrullDim_pullback_spec_eq_add
    (K R S : Type u) [Field K] [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    [Algebra K R] [Algebra K S] [Algebra.FiniteType K R] [Algebra.FiniteType K S] :
    topologicalKrullDim
        (pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) : Scheme.{u}) =
      topologicalKrullDim (Spec (.of R)) + topologicalKrullDim (Spec (.of S)) := by
  calc
    topologicalKrullDim
        (pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) : Scheme.{u}) =
        topologicalKrullDim (Spec (.of (R ⊗[K] S))) :=
      (pullbackSpecIso K R S).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim (R ⊗[K] S) := by
      change topologicalKrullDim (PrimeSpectrum (R ⊗[K] S)) = _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    _ = ringKrullDim R + ringKrullDim S :=
      Algebra.FiniteType.ringKrullDim_tensorProduct_eq_add K R S
    _ = topologicalKrullDim (Spec (.of R)) + topologicalKrullDim (Spec (.of S)) := by
      change ringKrullDim R + ringKrullDim S =
        topologicalKrullDim (PrimeSpectrum R) + topologicalKrullDim (PrimeSpectrum S)
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]

/-- The upper dimension bound for a product of finite-type schemes over a field. -/
theorem Scheme.topologicalKrullDim_pullback_le_add
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    topologicalKrullDim (pullback f g : Scheme.{u}) ≤
      topologicalKrullDim X + topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun z ↦ ?_
  let x : X := pullback.fst f g z
  let y : Y := pullback.snd f g z
  obtain ⟨R, i, hi, xi, hxi⟩ := Scheme.exists_Spec_apply_eq x
  obtain ⟨S, j, hj, yj, hyj⟩ := Scheme.exists_Spec_apply_eq y
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nontrivial R := xi.nontrivial
  letI : Nontrivial S := yj.nontrivial
  let φ := Spec.preimage (i ≫ f)
  let ψ := Spec.preimage (j ≫ g)
  have hφ : Spec.map φ = i ≫ f := Spec.map_preimage _
  have hψ : Spec.map ψ = j ≫ g := Spec.map_preimage _
  have hφft : φ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  have hψft : ψ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hψ]
    infer_instance
  algebraize [φ.hom, ψ.hom]
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap K R)) = i ≫ f := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hφ
  have hψ' : Spec.map (CommRingCat.ofHom (algebraMap K S)) = j ≫ g := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hψ
  let e :
      pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) ⟶
        pullback f g :=
    pullback.map _ _ _ _ i j (𝟙 _) (by simpa using hφ') (by simpa using hψ')
  letI : IsOpenImmersion e := by
    dsimp [e]
    infer_instance
  have hz : z ∈ Set.range e := by
    dsimp [e]
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨xi, hxi⟩, ⟨yj, hyj⟩⟩
  obtain ⟨w, hw⟩ := hz
  calc
    (Order.coheight z : WithBot ℕ∞) = Order.coheight w := by
      rw [← hw, e.isOpenEmbedding.coheight_eq]
    _ ≤ topologicalKrullDim
        (pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) : Scheme.{u}) := by
      rw [topologicalKrullDim_eq_orderKrullDim]
      exact Order.coheight_le_krullDim w
    _ = topologicalKrullDim (Spec (.of R)) + topologicalKrullDim (Spec (.of S)) :=
      Scheme.topologicalKrullDim_pullback_spec_eq_add K R S
    _ ≤ topologicalKrullDim X + topologicalKrullDim Y :=
      add_le_add i.isOpenEmbedding.isInducing.topologicalKrullDim_le
        j.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The lower dimension bound for a product of nonempty finite-type schemes over a field. -/
theorem Scheme.add_le_topologicalKrullDim_pullback_of_nonempty
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Nonempty X] [Nonempty Y] :
    topologicalKrullDim X + topologicalKrullDim Y ≤
      topologicalKrullDim (pullback f g : Scheme.{u}) := by
  rw [topologicalKrullDim_eq_iSup_coheight,
    topologicalKrullDim_eq_iSup_coheight, iSup_coe_add_iSup_coe]
  refine iSup_le fun x ↦ iSup_le fun y ↦ ?_
  obtain ⟨R, i, hi, xi, hxi⟩ := Scheme.exists_Spec_apply_eq x
  obtain ⟨S, j, hj, yj, hyj⟩ := Scheme.exists_Spec_apply_eq y
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nontrivial R := xi.nontrivial
  letI : Nontrivial S := yj.nontrivial
  let φ := Spec.preimage (i ≫ f)
  let ψ := Spec.preimage (j ≫ g)
  have hφ : Spec.map φ = i ≫ f := Spec.map_preimage _
  have hψ : Spec.map ψ = j ≫ g := Spec.map_preimage _
  have hφft : φ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  have hψft : ψ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hψ]
    infer_instance
  algebraize [φ.hom, ψ.hom]
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap K R)) = i ≫ f := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hφ
  have hψ' : Spec.map (CommRingCat.ofHom (algebraMap K S)) = j ≫ g := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hψ
  let e :
      pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) ⟶
        pullback f g :=
    pullback.map _ _ _ _ i j (𝟙 _) (by simpa using hφ') (by simpa using hψ')
  letI : IsOpenImmersion e := by
    dsimp [e]
    infer_instance
  calc
    ((Order.coheight x + Order.coheight y : ℕ∞) : WithBot ℕ∞) =
        (Order.coheight xi : WithBot ℕ∞) + Order.coheight yj := by
      rw [← WithBot.coe_add]
      congr 2
      · rw [← hxi, i.isOpenEmbedding.coheight_eq]
      · rw [← hyj, j.isOpenEmbedding.coheight_eq]
    _ ≤ topologicalKrullDim (Spec R) + topologicalKrullDim (Spec S) := by
      apply add_le_add
      · rw [topologicalKrullDim_eq_orderKrullDim]
        exact Order.coheight_le_krullDim xi
      · rw [topologicalKrullDim_eq_orderKrullDim]
        exact Order.coheight_le_krullDim yj
    _ = topologicalKrullDim
        (pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (Spec.map (CommRingCat.ofHom (algebraMap K S))) : Scheme.{u}) :=
      (Scheme.topologicalKrullDim_pullback_spec_eq_add K R S).symm
    _ ≤ topologicalKrullDim (pullback f g : Scheme.{u}) :=
      e.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- Dimension is additive on products of nonempty finite-type schemes over a field. -/
theorem Scheme.topologicalKrullDim_pullback_eq_add_of_nonempty
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Nonempty X] [Nonempty Y] :
    topologicalKrullDim (pullback f g : Scheme.{u}) =
      topologicalKrullDim X + topologicalKrullDim Y :=
  le_antisymm
    (Scheme.topologicalKrullDim_pullback_le_add f g)
    (Scheme.add_le_topologicalKrullDim_pullback_of_nonempty f g)

end AlgebraicGeometry
