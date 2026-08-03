/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Dimension in Noether normalization

Noether normalization produces an integral injection from a polynomial ring into any nonzero
finitely generated algebra over a field.  The number of variables in such a normalization is the
Krull dimension of the algebra.  This file records that dimension conclusion using
`Algebra.IsIntegral.ringKrullDim_eq`.

The theorem is a ring-theoretic consumer of the integral-extension dimension API and is part of
the route to dimensions of products of finite-type schemes.
-/

public section

universe u

open scoped TensorProduct

/-- A Noether normalization of a nonzero finitely generated algebra has as many variables as the
Krull dimension of the algebra. -/
theorem Algebra.FiniteType.exists_normalization_ringKrullDim_eq
    (k R : Type u) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
    [Algebra.FiniteType k R] :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.IsIntegral ∧ ringKrullDim R = s := by
  obtain ⟨s, g, hg, hgint⟩ := exists_integral_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hgint, ?_⟩
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  letI : FaithfulSMul (MvPolynomial (Fin s) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hgint⟩
  rw [Algebra.IsIntegral.ringKrullDim_eq (MvPolynomial (Fin s) k) R,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp [ringKrullDim_eq_zero_of_field]

/-- Krull dimension is additive on tensor products of nonzero finitely generated algebras over a
field. -/
theorem Algebra.FiniteType.ringKrullDim_tensorProduct_eq_add
    (k A B : Type u) [Field k] [CommRing A] [CommRing B] [Nontrivial A] [Nontrivial B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B := by
  obtain ⟨s, g, hg, hgint, hdimA⟩ :=
    Algebra.FiniteType.exists_normalization_ringKrullDim_eq k A
  obtain ⟨t, h, hh, hhint, hdimB⟩ :=
    Algebra.FiniteType.exists_normalization_ringKrullDim_eq k B
  let f := Algebra.TensorProduct.map g h
  letI : Module.Free k A := Module.Free.of_divisionRing k A
  letI : Module.Flat k A := Module.Flat.of_free
  letI : Module.Free k (MvPolynomial (Fin t) k) :=
    Module.Free.of_divisionRing k (MvPolynomial (Fin t) k)
  letI : Module.Flat k (MvPolynomial (Fin t) k) := Module.Flat.of_free
  have hf : Function.Injective f := by
    rw [← f.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map]
    exact TensorProduct.map_injective_of_flat_flat g.toLinearMap h.toLinearMap hg hh
  have hfint : f.IsIntegral := RingHom.IsIntegral.tensorProductMap g h hgint hhint
  letI : Algebra
      (MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin t) k) (A ⊗[k] B) :=
    f.toRingHom.toAlgebra
  letI : FaithfulSMul
      (MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin t) k) (A ⊗[k] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  letI : Algebra.IsIntegral
      (MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin t) k) (A ⊗[k] B) :=
    ⟨hfint⟩
  rw [Algebra.IsIntegral.ringKrullDim_eq
    (MvPolynomial (Fin s) k ⊗[k] MvPolynomial (Fin t) k) (A ⊗[k] B)]
  rw [ringKrullDim_eq_of_ringEquiv
    (MvPolynomial.tensorEquivSum k (Fin s) (Fin t) k).toRingEquiv]
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp [ringKrullDim_eq_zero_of_field, hdimA, hdimB]
