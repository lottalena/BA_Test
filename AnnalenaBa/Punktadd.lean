-- Elliptic Curve Point Addition Implementation
-- Basierend auf "An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves"
-- Paper von David Kurniadi Angdinata & Junyan Xu


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

-- Field-Instanz für ZMod 5
instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : Field (ZMod 5) := ZMod.instField 5

-- Kurve E: y² = x³ + x + 1 über ZMod 5
-- Das entspricht der allgemeinen Form: Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆
-- mit a₁ = a₂ = a₃ = 0, a₄ = 1, a₆ = 1
def E : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩

open WeierstrassCurve.Affine

-- Negationspolynom aus dem Paper: σ_X(Y) = -Y - (a₁X + a₃)
def neg_Y (W : WeierstrassCurve (ZMod 5)) (x y : ZMod 5) : ZMod 5 :=
  -y - (W.a₁ * x + W.a₃)

-- Für E vereinfacht sich das zu: σ_X(Y) = -Y
def neg_Y_simple (y : ZMod 5) : ZMod 5 := -y

-- Steigungsberechnung wie im Paper
def slope (W : WeierstrassCurve (ZMod 5)) (x₁ x₂ y₁ y₂ : ZMod 5) : ZMod 5 :=
  if x₁ = x₂ then
    if y₁ = neg_Y W x₂ y₂ then 0  -- Junk value für vertikale Linie
    else
      -- Tangente (Punktverdopplung): (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)
      (3 * x₁^2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (2 * y₁ + W.a₁ * x₁ + W.a₃)
  else
    -- Sekante: (y₁ - y₂) / (x₁ - x₂)
    (y₁ - y₂) / (x₁ - x₂)

-- X-Koordinate der Summe: λ² + a₁λ - a₂ - x₁ - x₂
def add_X (W : WeierstrassCurve (ZMod 5)) (x₁ x₂ L : ZMod 5) : ZMod 5 :=
  L^2 + W.a₁ * L - W.a₂ - x₁ - x₂

-- Y-Koordinate der Summe (vor Negation)
def add_Y_prime (x₁ y₁ L x₃ : ZMod 5) : ZMod 5 :=
  L * (x₁ - x₃) + y₁

-- Finale Y-Koordinate nach Negation
def add_Y (W : WeierstrassCurve (ZMod 5)) (x₁ x₂ y₁ L : ZMod 5) : ZMod 5 :=
  let x₃ := add_X W x₁ x₂ L
  let y₃_prime := add_Y_prime x₁ y₁ L x₃
  neg_Y W x₃ y₃_prime

-- Vereinfachte Versionen für E
section SpecializedForE

-- Für E: y² = x³ + x + 1 (a₁ = a₂ = a₃ = 0, a₄ = 1, a₆ = 1)
def slope_E (x₁ x₂ y₁ y₂ : ZMod 5) : ZMod 5 :=
  if x₁ = x₂ then
    if y₁ = -y₂ then 0  -- Vertikale Linie
    else (3 * x₁^2 + 1) / (2 * y₁)  -- Tangente
  else (y₁ - y₂) / (x₁ - x₂)  -- Sekante

def add_X_E (x₁ x₂ L : ZMod 5) : ZMod 5 := L^2 - x₁ - x₂

def add_Y_E (x₁ y₁ L x₃ : ZMod 5) : ZMod 5 :=
  -(L * (x₁ - x₃) + y₁)

end SpecializedForE

-- Beweis dass bestimmte Punkte auf der Kurve liegen
lemma point_01_on_curve : (1 : ZMod 5)^2 = (0 : ZMod 5)^3 + 0 + 1 := by norm_num
lemma point_04_on_curve : (4 : ZMod 5)^2 = (0 : ZMod 5)^3 + 0 + 1 := by rfl
lemma point_21_on_curve : (1 : ZMod 5)^2 = (2 : ZMod 5)^3 + 2 + 1 := by rfl
lemma point_24_on_curve : (4 : ZMod 5)^2 = (2 : ZMod 5)^3 + 2 + 1 := by rfl

-- Nicht-Singularitäts-Beweise
-- Ein Punkt (x,y) ist nicht-singulär, wenn nicht beide partiellen Ableitungen gleichzeitig null sind
-- ∂W/∂x = -3x² - a₄ + a₁y (für unsere Kurve: -3x² - 1)
-- ∂W/∂y = 2y + a₁x + a₃ (für unsere Kurve: 2y)



lemma point_01_nonsingular : E.toAffine.Nonsingular 0 1 := by
  -- Für (0,1): ∂W/∂x = -1 ≠ 0, also nicht-singulär
 sorry;

lemma point_04_nonsingular : E.toAffine.Nonsingular 0 4 := by
  -- Für (0,4): ∂W/∂x = -1 ≠ 0, also nicht-singulär
     sorry;

lemma point_21_nonsingular : E.toAffine.Nonsingular 2 1 := by
  -- Für (2,1): ∂W/∂y = 2 ≠ 0, also nicht-singulär
      sorry;

lemma point_24_nonsingular : E.toAffine.Nonsingular 2 4 := by
  -- Für (2,4): ∂W/∂y = 8 ≡ 3 ≠ 0, also nicht-singulär
      sorry;


-- konkrete Punkte erstellen
def P₁ : E.toAffine.Point := Point.some point_01_nonsingular
def P₂ : E.toAffine.Point := Point.some point_04_nonsingular  -- Das ist -P₁
def P₃ : E.toAffine.Point := Point.some point_21_nonsingular
def P₄ : E.toAffine.Point := Point.some point_24_nonsingular  -- Das ist -P₃

#eval! P₁
-- Tests der Punktaddition
section Tests

-- Grundlegende Tests TBD
example : P₁ + 0 = P₁ := by simp
example : 0 + P₁ = P₁ := by simp
example : P₁ + P₂ = 0 := by
  -- P₁ = (0,1), P₂ = (0,4), P₁ + P₂ sollte 0 sein da P₂ = -P₁
  sorry  -- Würde einen detaillierten Beweis über die Additionsformeln benötigen

-- Manuelle Berechnung der Punktaddition für P₃ + P₄
-- P₃ = (2,1), P₄ = (2,4) → sollte auch 0 ergeben da P₄ = -P₃
example : P₃ + P₄ = 0 := by sorry

-- Skalarmultiplikation


-- Tests der Skalarmultiplikation
--example : 1 • P₁ = P₁ := by rfl
--example : 2 • P₁ = P₁ + P₁ := by rfl

end Tests



-- Demonstration der Punktadditionsformeln wie im Paper
section PointAdditionFormulas

-- Explizite Berechnung für zwei verschiedene Punkte nur für E!!!
-- Kurve E: y² = x³ + x + 1 über ZMod 5
-- Basierend auf den Formeln aus dem Paper
def explicit_point_add (x₁ y₁ x₂ y₂ : ZMod 5) : ZMod 5 × ZMod 5 :=
  if x₁ = x₂ then
    if y₁ = -y₂ then (0, 0)  -- Dummy für Punkt im Unendlichen
    else
      -- Punktverdopplung
      let L := (3 * x₁^2 + 1) / (2 * y₁)
      let x₃ := L^2 - 2 * x₁
      let y₃ := -(L * (x₁ - x₃) + y₁)
      (x₃, y₃)
  else
    -- Normale Addition
    let L := (y₁ - y₂) / (x₁ - x₂)
    let x₃ := L^2 - x₁ - x₂
    let y₃ := -(L * (x₁ - x₃) + y₁)
    (x₃, y₃)

-- Test der expliziten Formel
#eval explicit_point_add 0 1 2 1  -- (0,1) + (2,1)


-- Verifikation das explicit add funktioniert
def test_explicit : ZMod 5 × ZMod 5 :=
  let x₁ := (0 : ZMod 5)
  let y₁ := (1 : ZMod 5)
  let x₂ := (2 : ZMod 5)
  let y₂ := (1 : ZMod 5)
  -- Da x₁ ≠ x₂, verwenden wir die Sekantenformel
  let L := (y₁ - y₂) / (x₁ - x₂)
  let x₃ := L^2 - x₁ - x₂
  let y₃ := -(L * (x₁ - x₃) + y₁)
  (x₃, y₃)

#eval test_explicit -- Sollte (3, 4) ergeben

-- Verifikation dass das Ergebnis auf der Kurve liegt
def verify_on_curve (x y : ZMod 5) : Bool := y^2 = x^3 + x + 1

-- Teste alle bekannten Punkte
#eval verify_on_curve 0 1  -- true
#eval verify_on_curve 0 4  -- true
#eval verify_on_curve 2 1  -- true
#eval verify_on_curve 2 4  -- true

end PointAdditionFormulas

-- Eigenschaften die aus dem Paper folgen (einfach importiert )
section Properties

-- Die Punktaddition ist kommutativ
lemma add_comm_A (P Q : E.toAffine.Point) : P + Q = Q + P :=
  add_comm P Q

-- Die Punktaddition ist assoziativ (folgt aus dem Paper)
lemma add_assoc_A (P Q R : E.toAffine.Point) : (P + Q) + R = P + (Q + R) :=
  add_assoc P Q R

-- Neutrales Element
lemma zero_add_A (P : E.toAffine.Point) : 0 + P = P :=
  zero_add P

-- Inverses Element
lemma add_neg_cancel_A (P : E.toAffine.Point) : P + (-P) = 0 :=
  add_neg_cancel P

end Properties


-- Alle Punkte auf unserer Kurve über ZMod 5
def all_points : List (ZMod 5 × ZMod 5) :=
  [(0, 1), (0, 4), (2, 1), (2, 4)]

-- Gruppentafel für unsere elliptische Kurve
def group_operation_table : List (E.toAffine.Point × E.toAffine.Point × E.toAffine.Point) :=
  [(P₁, P₁, P₁ + P₁),
   (P₁, P₂, P₁ + P₂),
   (P₁, P₃, P₁ + P₃),
   (P₃, P₃, P₃ + P₃),
   (P₃, P₄, P₃ + P₄)]

-- Das zeigt dass unsere Implementierung auf dem Paper basiert
-- und alle Gruppengesetze erfüllt
#check P₁ + P₃   -- Funktioniert!
#eval! P₁ + P₃
#check 3 • P₁   -- Skalarmultiplikation funktioniert
#eval! 3 • P₁


#check (3 : ℕ) • P₁   -- Mathlib's Skalarmultiplikation
#check (2 : ℕ) • P₃

-- Teste ob es funktioniert:
def test_mathlib_smul1 : E.toAffine.Point := (3 : ℕ) • P₁
def test_mathlib_smul2 : E.toAffine.Point := (2 : ℕ) • P₃

example : (0 : ℕ) • P₁ = 0 := zero_smul ℕ P₁
example : (1 : ℕ) • P₁ = P₁ := one_smul ℕ P₁
example (n m : ℕ) : (n + m) • P₁ = n • P₁ + m • P₁ := add_smul n m P₁

-- Skalarmultiplikation - eindeutige Definition
def my_scalar_mult : ℕ → E.toAffine.Point → E.toAffine.Point
  | 0, _ => 0
  | 1, P => P
  | k+1, P => P + (my_scalar_mult k P)



-- Verwende eindeutige Funktion statt Notation um Konflikte zu vermeiden
def smul (k : ℕ) (P : E.toAffine.Point) : E.toAffine.Point := my_scalar_mult k P

-- Tests der Skalarmultiplikation (mit expliziter Funktion)
example : smul 1 P₁ = P₁ := by rfl
example : smul 2 P₁ = P₁ + P₁ := by rfl
example : my_scalar_mult 0 P₁ = 0 := by rfl

-- Praktische Tests
def test_2P1 : E.toAffine.Point := smul 2 P₁  -- 2 * (0,1)
def test_3P1 : E.toAffine.Point := smul 3 P₁  -- 3 * (0,1)
def test_3P3 : E.toAffine.Point := smul 3 P₃  -- 3 * (2,1)

#eval! my_scalar_mult 3 P₁  -- leider keine kordinaten zurück gegeben

--  Skalarmultiplikation direkt mit Koordinaten (funktioniert leider noch nicht ganz )
def scalar_mult_coords : ℕ → (ZMod 5 × ZMod 5) → Option (ZMod 5 × ZMod 5)
  | 0, _ => none  -- 0 * P = O (Punkt im Unendlichen)
  | 1, (x, y) => some (x, y)  -- 1 * P = P
  | k+1, (x, y) =>
    -- [k+1]P = P + [k]P
    match scalar_mult_coords k (x, y) with
    | none => some (x, y)  -- [k]P = O, also [k+1]P = P + O = P
    | some (x', y') => some (explicit_point_add x y x' y')

-- Teste die Koordinaten-basierte Skalarmultiplikation
#eval scalar_mult_coords 2 (0, 1)  -- 2 * (0,1)
#eval scalar_mult_coords 3 (0, 1)  -- 3 * (0,1)
#eval scalar_mult_coords 3 (2, 1)  -- 3 * (2,1)
#eval scalar_mult_coords 5 (0, 1)  -- 5 * (0,1) - sollte O ergeben (none)

-- Verifikation der Ergebnisse
def verify_scalar_results : Unit := by
  -- Teste 2 * (0,1)
  have h2 : scalar_mult_coords 2 (0, 1) = some (explicit_point_add 0 1 0 1) := rfl
  -- Teste 3 * (0,1) = (0,1) + 2*(0,1)
  have h3 : scalar_mult_coords 3 (0, 1) =
    match scalar_mult_coords 2 (0, 1) with
    | some (x, y) => some (explicit_point_add 0 1 x y)
    | none => some (0, 1) := rfl
  constructor

-- Konkrete Berechnungen die funktionieren:
#eval explicit_point_add 0 1 0 1  -- (0,1) + (0,1) = 2*(0,1)
#eval let res := explicit_point_add 0 1 0 1; explicit_point_add 0 1 res.1 res.2  -- 3*(0,1)

-- Saubere Interface-Funktion
def compute_scalar_mult (k : ℕ) (x y : ZMod 5) : Option (ZMod 5 × ZMod 5) :=
  scalar_mult_coords k (x, y)

--Tests TBD
#eval compute_scalar_mult 2 0 1  -- 2 * (0,1)
#eval compute_scalar_mult 3 0 1  -- 3 * (0,1)
#eval compute_scalar_mult 3 2 1  -- 3 * (2,1)
#eval compute_scalar_mult 4 0 1  -- 4 * (0,1)
#eval compute_scalar_mult 5 0 1  -- 5 * (0,1) =
