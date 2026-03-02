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

set_option linter.style.longLine false
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

-- mit Neutralem Element
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

-- Neutrales Element Tests:
#eval point_add_zmod5 E none (some (0, 1))           -- some (0, 1)
#eval point_add_zmod5 E (some (2, 1)) none          -- some (2, 1)

-- Normale Addition:
#eval point_add_zmod5 E (some (0, 1)) (some (2, 1))  -- some (neues Ergebnis)

-- Punktverdopplung:
#eval point_add_zmod5 E (some (0, 1)) (some (0, 1))  -- some (verdoppelter Punkt)

--To be Done gruppen axiome nicht beweisbar (zu komplex)
--- hypothese nicht sigulärer affine punkt als voraussetzung

--versuch äquizalenz "bridge lemma " nicht erfolgreich



-- def point_to_option {F : Type*} [Field F] {W : WeierstrassCurve F} (P : Point W) : Option (F × F) :=
--  P := WeierstrassCurve.Affine.Point ;

-- def point_to_option {F : Type*} [Field F] {W : WeierstrassCurve F} (P : Point W) : Option (F × F) :=
--   match P with
--   | .zero => none
--   | .some h => .some ⟨⟨x, y⟩, _⟩ => some (x, y)

-- theorem bridge_lemma {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
--     (P Q : Point W) :
--     general_point_add_option F W (point_to_option P) (point_to_option Q) = point_to_option (P + Q) := by
--   -- 1. Behandlung der neutralen Elemente
--   cases P with
--   | zero => simp [point_to_option, general_point_add_option]
--   | some p =>
--     cases Q with
--     | zero => simp [point_to_option, general_point_add_option]
--     | some q =>
--       -- 2. Vorbereitung der affinen Koordinaten
--       simp [point_to_option, general_point_add_option]
--       rw [Point.add_def] -- Öffnet die Mathlib-Addition

--       -- Fallunterscheidung: Gleiche x-Koordinate oder nicht
--       by_cases hx : p.x = q.x
--       · simp [hx]
--         -- Unterfall: Inverse Punkte (P = -Q)
--         by_cases hinv : p.y = neg_Y_general F W q.x q.y
--         · simp [hinv]
--           -- Zeige, dass Mathlib in diesem Fall auch 'zero' (none) liefert
--           unfold neg_Y_general at hinv
--           -- Wir nutzen die Mathlib-Bedingung für das Inverse
--           have : p.y = -q.y - W.a₁ * q.x - W.a₃ := by exact hinv
--           simp [this, hx]

--         · -- Unterfall: Punktverdopplung (P = Q)
--           -- Da x1 = x2 und P ≠ -Q, folgt aus der Kurvengleichung P = Q
--           have hpq : p = q := by
--             let hor := eq_or_neg_of_x_eq p.2 q.2
--             simp [hx] at hor
--             cases hor with
--             | inl h_eq => ext <;> assumption
--             | inr h_neg => contradiction

--           simp [hpq]
--           unfold slope_general add_X_general add_Y_general neg_Y_general add_Y_prime_general
--           simp [hinv]
--           congr 1 <;> (field_simp; ring)

--       · -- 3. FALL: Sekante (x1 ≠ x2)
--         simp [hx, Ne.symm hx]
--         unfold slope_general add_X_general add_Y_general neg_Y_general add_Y_prime_general
--         simp [hx]
--         congr 1 <;> (field_simp; ring)




-- -- lemma add_left_neg {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (x y : F) :
-- --   general_point_add_option F W (some (x, neg_Y_general F W x y)) (some (x, y)) = none := by
-- --   -- y₁ = neg_Y_general F W x₂ y₂  → none
-- --   simp [general_point_add_option, neg_Y_general]
-- -- --"Wenn ich einen Punkt (x, y) nehme,
-- -- --sein Inverse berechne, und beide addiere, erhalte ich das neutrale Element"


-- -- --Neutrales Element
-- -- lemma zero_add_k {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (P : Option (F × F)) :
-- --   general_point_add_option F W none P = P :=
-- --   by rfl

-- -- lemma add_zero_k {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (P : Option (F × F)) :
-- --   general_point_add_option F W P none = P :=
-- --   by
-- --     cases P
-- --     · rfl -- Fall P = none
-- --     · rfl -- Fall P = some (x, y)

-- -- lemma add_comm_k {F : Type*} [Field F] [DecidableEq F]
-- --     (W : WeierstrassCurve F) (P Q : Option (F × F)) :
-- --   general_point_add_option F W P Q = general_point_add_option F W Q P := by
-- --   cases P with
-- --   | none =>
-- --     cases Q with
-- --     | none => rfl
-- --     | some _ => rfl
-- --   | some p =>
-- --     cases p with
-- --     | mk x₁ y₁ =>
-- --       cases Q with
-- --       | none => rfl
-- --       | some q =>
-- --         cases q with
-- --         | mk x₂ y₂ =>
-- --           simp only [general_point_add_option]
-- --           by_cases h1 : x₁ = x₂ ∧ y₁ = neg_Y_general F W x₂ y₂
-- --           · -- Fall: Inverse Punkte
-- --             simp [h1.1, h1.2]
-- --             -- Das verbleibende Goal: y₂ = -(-y₂)
-- --             rw [neg_Y_general]
-- --             simp [neg_Y_general]
-- --           · by_cases h2 : x₁ = x₂
-- --             · -- Fall: Punktverdopplung
-- --               simp [h2]
-- --               rfl
-- --               sorry
-- --             · -- Fall: Sekantensteigung
-- --               simp [h1, h2]
-- --               congr 2
-- --               · field_simp; ring
-- --               · field_simp; ring
-- --                 sorry


-- -- lemma add_comm_k {F : Type*} [Field F] [DecidableEq F]
-- --     (W : WeierstrassCurve F) (P Q : Option (F × F)) :
-- --   general_point_add_option F W P Q = general_point_add_option F W Q P := by
-- --   cases P with
-- --   | none =>
-- --     cases Q with
-- --     | none => rfl
-- --     | some _ => rfl
-- --   | some p =>
-- --     cases p with
-- --     | mk x₁ y₁ =>  -- HIER: Explizite Tuple-Entpackung
-- --       cases Q with
-- --       | none => rfl
-- --       | some q =>
-- --         cases q with
-- --         | mk x₂ y₂ =>  -- HIER: Explizite Tuple-Entpackung
-- --           simp only [general_point_add_option]
-- --           by_cases h1 : x₁ = x₂ ∧ y₁ = neg_Y_general F W x₂ y₂
-- --           · -- Fall: Inverse Punkte
-- --             simp [h1]
-- --             constructor
-- --             · exact h1.1.symm
-- --             · rw [neg_Y_general] at h1 ⊢
-- --               simp [h1.2]
-- --               ring
-- --           · by_cases h2 : x₁ = x₂
-- --             · -- Fall: Punktverdopplung
-- --               simp [h2]
-- --               rfl
-- --             · -- Fall: Sekantensteigung
-- --               simp [h1, h2]
-- --               congr 2
-- --               · field_simp; ring  -- x₃-Koordinate
-- --               · field_simp; ring  -- y₃-Koordinate
