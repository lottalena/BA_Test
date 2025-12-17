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

-- ALLGEMEINE SEKTION: Funktioniert für beliebige Felder
section GeneralTheory

-- Elliptic Curve Point Addition Implementation
-- Basierend auf "An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves"
-- Paper von David Kurniadi Angdinata & Junyan Xu

-- Allgemeiner Parameter für beliebiges Feld
variable (F : Type*) [Field F] [DecidableEq F]

--Decidable ->
--Da mit endlichen Feldern gearbeitet wird bei anderen (uneendlichen )Felder würde das zu problemen führen


-- σ_X(Y) = -Y - (a₁X + a₃)
-- Berechnet das additive Inverse (Spiegelt den Punkt an der generalisierten x-Achse)
--"Given a nonsingular point P ∈ W, its negation −P is defined to be the unique third point of intersection between W and the line through O_W and P, which is vertical when drawn on the affine plane.
-- Explicitly, if P := (x,y), then −P := (x, σ_x(y))"
def neg_Y_general (W : WeierstrassCurve F) (x y : F) : F :=
  -y - (W.a₁ * x + W.a₃)

-- Steigungsberechnung wie im Paper (allgemein)
def slope_general (W : WeierstrassCurve F) (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then
    if y₁ = neg_Y_general F W x₂ y₂ then 0  -- Junk value für vertikale Linie
    else
      -- Tangente (Punktverdopplung): (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)
      (3 * x₁^2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (2 * y₁ + W.a₁ * x₁ + W.a₃)
  else
    -- Sekante: (y₁ - y₂) / (x₁ - x₂)
    (y₁ - y₂) / (x₁ - x₂)

-- X-Koordinate der Summe: λ² + a₁λ - a₂ - x₁ - x₂ (allgemein)
def add_X_general (W : WeierstrassCurve F) (x₁ x₂ L : F) : F :=
  L^2 + W.a₁ * L - W.a₂ - x₁ - x₂

-- Y-Koordinate der Summe (vor Negation) (allgemein)
def add_Y_prime_general (x₁ y₁ L x₃ : F) : F :=
  L * (x₁ - x₃) + y₁

-- Finale Y-Koordinate nach Negation (allgemein)
def add_Y_general (W : WeierstrassCurve F) (x₁ x₂ y₁ L : F) : F :=
  let x₃ := add_X_general F W x₁ x₂ L
  let y₃_prime := add_Y_prime_general F x₁ y₁ L x₃
  neg_Y_general F W x₃ y₃_prime

-- ohne Neutrales Element handling
def general_point_add (W : WeierstrassCurve F) (x₁ y₁ x₂ y₂ : F) : F × F :=
  if x₁ = x₂ then
    if y₁ = neg_Y_general F W x₂ y₂ then (0, 0)  -- P + (-P) = O
    else
      let L := slope_general F W x₁ x₁ y₁ y₁      -- Tangente
      let x₃ := add_X_general F W x₁ x₁ L
      let y₃ := add_Y_general F W x₁ x₁ y₁ L
      (x₃, y₃)
  else
    let L := slope_general F W x₁ x₂ y₁ y₂       -- Sekante
    let x₃ := add_X_general F W x₁ x₂ L
    let y₃ := add_Y_general F W x₁ x₂ y₁ L
    (x₃, y₃)

def general_point_add_option (W : WeierstrassCurve F) :
  Option (F × F) → Option (F × F) → Option (F × F)
  | none, P => P                    -- O + P = P
  | P, none => P                    -- P + O = P
  | some (x₁, y₁), some (x₂, y₂) =>
    -- PRECONDITION: (x₁,y₁) und (x₂,y₂) liegen auf W und sind nonsingulär
    if x₁ = x₂ then
      if y₁ = neg_Y_general F W x₂ y₂ then
        none  -- P + (-P) = O
      else
        -- Punktverdopplung
        let L := slope_general F W x₁ x₁ y₁ y₁
        let x₃ := add_X_general F W x₁ x₁ L
        let y₃ := add_Y_general F W x₁ x₁ y₁ L
        some (x₃, y₃)
    else
      -- Normale Addition
      let L := slope_general F W x₁ x₂ y₁ y₂
      let x₃ := add_X_general F W x₁ x₂ L
      let y₃ := add_Y_general F W x₁ x₂ y₁ L
      some (x₃, y₃)

end GeneralTheory


-- Field-Instanz für ZMod 5
instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : Field (ZMod 5) := ZMod.instField 5
instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
instance : Field (ZMod 7) := ZMod.instField 7

--  Konkrete Kurve E: y² = x³ + x + 1 über ZMod 5
def E : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩

-- Spezialisierte Funktionen für ZMod 5 (für einfachere Tests)
def neg_Y_zmod5 := neg_Y_general (ZMod 5)
def slope_zmod5 := slope_general (ZMod 5)
def add_X_zmod5 := add_X_general (ZMod 5)
def add_Y_zmod5 := add_Y_general (ZMod 5)
def point_add_zmod5 := general_point_add_option (ZMod 5)
def point_add_zmod7 := general_point_add (ZMod 7)

-- Vereinfachte Version für E (da a₁ = a₂ = a₃ = 0, a₄ = 1, a₆ = 1)
def neg_Y_simple (y : ZMod 5) : ZMod 5 := -y

-- Tests der allgemeinen Funktionen
-- Wichtig noch keine Validerung
-- Dokumentierte Vorbedingung:
-- "Alle Eingaben müssen nonsingulär sein"

-- PRECONDITION: Alle Eingabepunkte some (x,y) müssen:
-- 1. Auf der verwendeten Weierstrass-Kurve liegen
-- 2. Nonsingulär sein (keine singulären Punkte)
-- Für elliptische Kurven (Diskriminant ≠ 0) sind alle Punkte automatisch nonsingulär.

#eval neg_Y_zmod5 E 0 1        -- Sollte -1 = 4 ergeben
#eval slope_zmod5 E 2 2 1 1     -- Tangentensteigu ng an (2,1)
#eval add_X_zmod5 E 0 2 3      -- X-Koordinate mit Steigung 3

#eval point_add_zmod5 E (some (0, 1)) (some (2, 1))  -- some Ergebnis
#eval point_add_zmod5 E none (some (2, 1))           -- some (2, 1)
#eval point_add_zmod5 E (some (0, 1)) none          -- some (0, 1)
#eval point_add_zmod5 E (some (0, 1)) (some (0, 4))

--To be Done gruppen axiome
