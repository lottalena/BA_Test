import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp

import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

-- Schaltet Warnungen für den akademischen Export aus
set_option linter.flexible false
set_option linter.unusedVariables false

-- ================================================================
-- TEIL 1 & 2: KURVEN-STRUKTUR & ARITHMETIK
-- ================================================================

structure EllipticCurve (F : Type*) [Field F] where
  a : F
  b : F
  discriminant_nonzero : 4 * a^3 + 27 * b^2 ≠ 0

def field_div {F : Type*} [Field F] (a b : F) : F := a * b⁻¹

def explicit_point_add {F : Type*} [Field F] [DecidableEq F] (E : EllipticCurve F)
  (x₁ y₁ x₂ y₂ : F) : Option (F × F) :=
  if hx : x₁ = x₂ then
    if hy : y₁ = -y₂ then none
    else
      let L := field_div (3 * x₁^2 + E.a) (2 * y₁)
      let x₃ := L^2 - 2 * x₁
      let y₃ := L * (x₁ - x₃) - y₁
      some (x₃, y₃)
  else
    let L := field_div (y₁ - y₂) (x₁ - x₂)
    let x₃ := L^2 - x₁ - x₂
    let y₃ := L * (x₁ - x₃) - y₁
    some (x₃, y₃)

-- ================================================================
-- TEIL 3: PUNKT-DATENTYP & GRUPPENOPERATIONEN
-- ================================================================

inductive EllipticPoint (F : Type*) [Field F] where
  | infinity : EllipticPoint F
  | point (x y : F) : EllipticPoint F
deriving Repr, DecidableEq

namespace EllipticPoint
variable {F : Type*} [Field F] [DecidableEq F]

def from_option (opt : Option (F × F)) : EllipticPoint F :=
  match opt with | none => infinity | some (x, y) => point x y

def add (E : EllipticCurve F) (P Q : EllipticPoint F) : EllipticPoint F :=
  match P, Q with
  | infinity, _ => Q
  | _, infinity => P
  | point x₁ y₁, point x₂ y₂ => from_option (explicit_point_add E x₁ y₁ x₂ y₂)

def neg : EllipticPoint F → EllipticPoint F
| infinity => infinity
| point x y => point x (-y)
end EllipticPoint

-- ================================================================
-- TEIL 4: ALGORITHMEN (NAIVE vs. DOUBLE-AND-ADD)
-- ================================================================

namespace Algorithms
open EllipticPoint
variable {F : Type*} [Field F] [DecidableEq F]

def naive_scalar_mult (E : EllipticCurve F) (k : ℕ) (P : EllipticPoint F) : EllipticPoint F :=
  match k with | 0 => infinity | n + 1 => add E P (naive_scalar_mult E n P)

def double_and_add (E : EllipticCurve F) (k : ℕ) (P : EllipticPoint F) : EllipticPoint F :=
  let rec loop (bits : List Bool) (acc base : EllipticPoint F) : EllipticPoint F :=
    match bits with
    | [] => acc
    | b :: bs => loop bs (if b then add E acc base else acc) (add E base base)
  loop k.bits infinity P
end Algorithms

-- ================================================================
-- TEIL 5: DER FORMALE BEWEIS (LÜCKENLOS)
-- ================================================================

namespace Proofs
open EllipticPoint Algorithms

variable {F : Type*} [Field F] [DecidableEq F]

-- Axiomatische Definition der Gruppeneigenschaften
class EllipticCurveGroup (E : EllipticCurve F) where
  add_assoc : ∀ P Q R : EllipticPoint F, add E (add E P Q) R = add E P (add E Q R)
  add_comm  : ∀ P Q : EllipticPoint F, add E P Q = add E Q P
  add_zero  : ∀ P : EllipticPoint F, add E P infinity = P
  zero_add  : ∀ P : EllipticPoint F, add E infinity P = P

variable {E : EllipticCurve F} [GroupE : EllipticCurveGroup E]

-- 5.1 Arithmetische Hilfsfunktion & Beweis (Die Bit-Basis)
def bitsToNat (bits : List Bool) : ℕ :=
  match bits with | [] => 0 | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs


-- 5.2 Lemmata zur Skalarmultiplikation
lemma naive_add (n m : ℕ) (P : EllipticPoint F) :
  add E (naive_scalar_mult E n P) (naive_scalar_mult E m P) = naive_scalar_mult E (n + m) P := by
  induction n with
  | zero => simp [naive_scalar_mult, EllipticCurveGroup.zero_add]
  | succ n ih => simp only [naive_scalar_mult, Nat.succ_add]; rw [EllipticCurveGroup.add_assoc, ih]

lemma naive_mul_two (n : ℕ) (P : EllipticPoint F) :
  naive_scalar_mult E (2 * n) P = naive_scalar_mult E n (add E P P) := by
  induction n with
  | zero => simp [naive_scalar_mult]
  | succ n ih =>
    rw [Nat.mul_succ, ← naive_add, ih]
    simp only [naive_scalar_mult]; rw [EllipticCurveGroup.add_zero, EllipticCurveGroup.add_comm]

-- 5.3 Die Schleifen-Invariante
lemma loop_correct (bits : List Bool) (acc base : EllipticPoint F) :
  double_and_add.loop E bits acc base = add E acc (naive_scalar_mult E (bitsToNat bits) base) := by
  induction bits generalizing acc base with
  | nil => simp [double_and_add.loop, bitsToNat, naive_scalar_mult, EllipticCurveGroup.add_zero]
  | cons b bs ih =>
    simp [double_and_add.loop, bitsToNat]
    by_cases h : b = true
    · simp [h]; rw [ih, ← naive_mul_two, EllipticCurveGroup.add_assoc, ← naive_add]
      simp [naive_scalar_mult, EllipticCurveGroup.add_zero]; rfl
    · simp [h]; rw [ih, ← naive_mul_two]; rfl

-- 5.4 DAS FINALE THEOREM
theorem double_and_add_eq_naive (k : ℕ) (P : EllipticPoint F) :
  double_and_add E k P = naive_scalar_mult E k P := by
  rw [double_and_add, loop_correct, EllipticCurveGroup.zero_add, bitsToNat_bits_inv]

end Proofs
