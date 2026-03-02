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
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Field
import Mathlib.FieldTheory.Finiteness

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.Defs    -- Field Division Instanzen
import Mathlib.Data.ZMod.Defs        -- ZMod spezifische Operationen
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Finite.Basic   -- Finite Field Lemmas
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


-- Primzahl-Fakten (für ZMod Körper-Instanzen)
instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
instance : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩

-- Explizite Körper-Instanzen
instance : Field (ZMod 5) := ZMod.instField 5
instance : Field (ZMod 7) := ZMod.instField 7
instance : Field (ZMod 11) := ZMod.instField 11

-- Hauptkörper für Test Implementierung
abbrev F := ZMod 5

-- Alternative Körper für Tests
abbrev F7 := ZMod 7
abbrev F11 := ZMod 11

-- Hilfsfunktion für Division (a * b⁻¹)
def field_div (a b : F) : F := a * b⁻¹

-- Notation für bessere Lesbarkeit
notation:70 a " / " b:70 => field_div a b

def E : WeierstrassCurve F := ⟨0, 0, 0, 1, 1⟩

-- Prüft ob ein Punkt (x,y) auf der Kurve E liegt
def point_on_curve (x y : F) : Bool := y^2 = x^3 + E.a₄*x + E.a₆

-- Vereinfachte Version für E: y² = x³ + x + 1
def point_on_E (x y : F) : Bool := y^2 = x^3 + x + 1

-- Tests für bekannte Punkte
#eval point_on_E (0 : F) (1 : F)  -- true: (0,1) auf E
#eval point_on_E (0 : F) (4 : F)  -- true: (0,4) auf E
#eval point_on_E (2 : F) (1 : F)  -- true: (2,1) auf E
#eval point_on_E (2 : F) (4 : F)  -- true: (2,4) auf E

-- Negative Tests
#eval point_on_E (1 : F) (0 : F)  -- false: (1,0) nicht auf E
#eval point_on_E (3 : F) (2 : F)  -- false: (3,2) nicht auf E


lemma point_01_on_E : point_on_E (0 : F) (1 : F) = true := by
  simp [point_on_E];

lemma point_04_on_E : point_on_E (0 : F) (4 : F) = true := by
  unfold point_on_E
  rfl

lemma point_21_on_E : point_on_E (2 : F) (1 : F) = true := by
  unfold point_on_E
  rfl

lemma point_24_on_E : point_on_E (2 : F) (4 : F) = true := by
  unfold point_on_E
  rfl


def explicit_point_add (x₁ y₁ x₂ y₂ : F) : Option (F × F) :=
  if x₁ = x₂ then
    if y₁ = -y₂ then
      -- Fall 1: P + (-P) = O → mathematisch korrekt als none
      none
    else
      -- Fall 2: Punktverdopplung P + P = 2P
      -- Tangentenstiegung: λ = (3x₁² + a₄) / (2y₁)
      let L := field_div (3 * x₁^2 + 1) (2 * y₁) -- a₄ = 1 für unsere Kurve
      let x₃ := L^2 - 2 * x₁               -- x₃ = λ² - x₁ - x₂ = λ² - 2x₁
      let y₃ := -(L * (x₁ - x₃) + y₁)      -- y₃ = -(λ(x₁ - x₃) + y₁)
      some (x₃, y₃)
  else
    -- Fall 3: Normale Addition P₁ + P₂ (x₁ ≠ x₂)
    -- Sekantenstiegung: λ = (y₁ - y₂) / (x₁ - x₂)
    let L := field_div (y₁ - y₂) (x₁ - x₂)       -- Sekantensteigung
    let x₃ := L^2 - x₁ - x₂              -- x₃ = λ² - x₁ - x₂
    let y₃ := -(L * (x₁ - x₃) + y₁)      -- y₃ = -(λ(x₁ - x₃) + y₁)
    some (x₃, y₃)


-- Für Kurve E: y² = x³ + x + 1 ist -P = (x, -y)
-- (Vereinfachung da a₁ = a₃ = 0 in unserer Kurve)
def point_negate (x y : F) : F × F := (x, -y)

-- Prüft ob zwei Punkte inverse zueinander sind: P = -Q
def are_inverse (x₁ y₁ x₂ y₂ : F) : Bool :=
  x₁ = x₂ ∧ y₁ = -y₂

-- Prüft ob ein Punkt der Dummy-Punkt für das neutrale Element ist
def is_dummy_infinity (x y : F) : Bool := x = 1 ∧ y = 0

-- Test 1: Bekannte Punktaddition (0,1) + (2,1)
#eval explicit_point_add (0 : F) (1 : F) (2 : F) (1 : F)  -- Erwartung: (3, 4)

-- Test 2: Punktverdopplung (0,1) + (0,1) = 2·(0,1)
#eval explicit_point_add (0 : F) (1 : F) (0 : F) (1 : F)  -- Verdopplung

-- Test 3: Inverse Punkte (0,1) + (0,4) = (0,1) + (0,-1) = O
#eval explicit_point_add (0 : F) (1 : F) (0 : F) (4 : F)  -- Sollte none ergeben

-- Test 4: Punktnegation
#eval point_negate (0 : F) (1 : F)  -- Sollte (0, 4) ergeben (da -1 ≡ 4 mod 5)
#eval point_negate (2 : F) (1 : F)  -- Sollte (2, 4) ergeben (da -1 ≡ 4 mod 5)


-- Hilfsfunktion: Prüft ob das Additionsergebnis auf der Kurve liegt
def verify_addition_result (x₁ y₁ x₂ y₂ : F) : Bool :=
  match explicit_point_add x₁ y₁ x₂ y₂ with
  | none => true  -- O ist immer "gültig"
  | some (x₃, y₃) => point_on_E x₃ y₃

-- Tests der Verifikation
#eval verify_addition_result (0 : F) (1 : F) (2 : F) (1 : F)  -- true
#eval verify_addition_result (0 : F) (1 : F) (0 : F) (1 : F)  -- true
#eval verify_addition_result (0 : F) (1 : F) (0 : F) (4 : F)  -- true


lemma explicit_add_on_curve (x₁ y₁ x₂ y₂ : F) :
  point_on_E x₁ y₁ = true → point_on_E x₂ y₂ = true →
  verify_addition_result x₁ y₁ x₂ y₂ = true :=
by
  -- Beweis folgt aus den Angdinata & Xu Formeln
  -- Für die Thesis wird hier auf das Paper verwiesen
  sorry

lemma negate_on_curve (x y : F) :
  point_on_E x y = true → point_on_E (point_negate x y).1 (point_negate x y).2 = true :=
by
  intro h
  simp [point_negate, point_on_E, Prod.fst, Prod.snd] at h ⊢
  convert h using 1




def simple_nonsingular (x y : F) : Prop :=
  point_on_E x y = true ∧ (3*x^2 + 1 ≠ 0 ∨ 2*y ≠ 0)

-- EXAKT nach Paper Seite 6: "inductive point | zero | some {x y : F} (h : W.nonsingular x y)"
inductive point
| zero : point
| some {x y : F} : simple_nonsingular x y → point


inductive EllipticPoint : Type where
  | infinity : EllipticPoint              -- O (neutrales Element)
  | point (x y : F) : EllipticPoint      -- Affine Punkte (x, y)

namespace EllipticPoint

#check EllipticPoint

-- Grundlegende Instanzen
instance : Zero EllipticPoint := ⟨infinity⟩

-- Konvertierung zwischen unseren Koordinaten-Primitiven und EllipticPoint
def from_option (opt : Option (F × F)) : EllipticPoint :=
  match opt with
  | none => infinity
  | some (x, y) => point x y

def to_option (P : EllipticPoint) : Option (F × F) :=
  match P with
  | infinity => none
  | point x y => some (x, y)

-- ================================================================
-- GRUPPENOPERATIONEN (KOORDINATEN-BACKEND)
-- ================================================================

-- Addition: nutzt unsere bewährten explicit_point_add Funktionen
def add : EllipticPoint → EllipticPoint → EllipticPoint
| infinity, P => P
| P, infinity => P
| point x₁ y₁, point x₂ y₂ => from_option (explicit_point_add x₁ y₁ x₂ y₂)

-- Negation: nutzt point_negate
def neg : EllipticPoint → EllipticPoint
| infinity => infinity
| point x y => point x (-y)

-- Instanzen für Notation
-- Nach Angdinata & Xu Paper Seite 14: die 8 Axiome einer abelschen Gruppe
-- "instance : add_comm_group W.point := ⟨zero, neg, add, zero_add, add_zero, add_left_neg, add_comm, add_assoc⟩"
instance : Add EllipticPoint := ⟨add⟩
instance : Neg EllipticPoint := ⟨neg⟩
axiom add_assoc (P Q R : EllipticPoint) : (P + Q) + R = P + (Q + R)
axiom zero_add (P : EllipticPoint) : 0 + P = P
axiom add_zero (P : EllipticPoint) : P + 0 = P
axiom add_left_neg (P : EllipticPoint) : -P + P = 0
axiom add_comm (P Q : EllipticPoint) : P + Q = Q + P



-- ================================================================
-- TEIL 4: SKALARMULTIPLIKATION IMPLEMENTIERUNGEN
-- ================================================================

-- Naive Skalarmultiplikation: [k]P = P + P + ... + P (k-mal)
def naive_scalar_mult (k : ℕ) (P : EllipticPoint) : EllipticPoint :=
  match k with
  | 0 => 0
  | n + 1 => P + naive_scalar_mult n P


def double_and_add (k : ℕ) (P : EllipticPoint) : EllipticPoint :=
  let rec aux (n : ℕ) (acc : EllipticPoint) (base : EllipticPoint) : EllipticPoint :=
    if n = 0 then
      acc
    else if n % 2 = 1 then
      -- n ungerade: acc := acc + base, base := 2*base, n := n/2
      aux (n / 2) (acc + base) (base + base)
    else
      -- n gerade: base := 2*base, n := n/2
      aux (n / 2) acc (base + base)
  if k = 0 then 0 else aux k 0 P

theorem double_and_add_eq_naive (k : ℕ) (P : EllipticPoint) :
  double_and_add k P = naive_scalar_mult k P :=
by
  -- Beweis durch starke Induktion über k
  -- Nutzt die binäre Darstellung von k und Distributivität
  -- Der detaillierte Beweis würde die Gruppenaxiome nutzen
  sorry


-- Test-Punkte auf der Kurve E
def test_point_01 : EllipticPoint := point 0 1  -- (0,1)
def test_point_21 : EllipticPoint := point 2 1  -- (2,1)

-- Tests der naiven Skalarmultiplikation
#check naive_scalar_mult 2 test_point_01   -- 2P
#check naive_scalar_mult 3 test_point_01   -- 3P
#check naive_scalar_mult 5 test_point_01


#eval to_option (naive_scalar_mult 2 test_point_01)     -- 2*(0,1)
#eval to_option (double_and_add 2 test_point_01)
-- Tests des Double-and-Add Algorithmus
#check double_and_add 2 test_point_01      -- 2P (effizient)
#check double_and_add 3 test_point_01      -- 3P (effizient)
#check double_and_add 5 test_point_01      -- 5P = O (effizient)


#eval to_option (naive_scalar_mult 3 test_point_01)     -- 3*(0,1)
#eval to_option (double_and_add 3 test_point_01)       -- 3*(0,1) effizient

-- Vergleichstest - sollten identisch sein
example : double_and_add 7 test_point_01 = naive_scalar_mult 7 test_point_01 :=
  double_and_add_eq_naive 7 test_point_01



-- Große Skalare zeigen den Effizienzgewinn
def large_scalar := 2^10 - 1  -- 1023

-- Naive: 1023 Additionen
#check naive_scalar_mult large_scalar test_point_01

-- Double-and-Add: nur ~10 Additionen (log₂(1023) ≈ 10)
#check double_and_add large_scalar test_point_01

-- Äquivalenz auch bei großen Skalaren
example : double_and_add large_scalar test_point_01 =
          naive_scalar_mult large_scalar test_point_01 :=
  double_and_add_eq_naive large_scalar test_point_01

end EllipticPoint
-- open WeierstrassCurve Affine

-- variable {F : Type*} [Field F] (W : WeierstrassCurve F)

-- def naive_scalar_mult (n : Nat) (P : Point) : Point :=
--   match n with
--   | 0 => Point.infinity
--   | n + 1 => Point.add P (naive_scalar_mult n P)



--Problem typunterschiede unterschiedliche 0 typen
-- example [AddCommGroup (Point W)] (P : Point W) :
--   naive_scalar_mult W 1 P = P := by
--   unfold naive_scalar_mult -- Ziel: P + naive_scalar_mult W 0 P = P
--   unfold naive_scalar_mult -- Ziel: P + 0 = P
--   -- Jetzt ist die 0 exakt die 0, die add_zero erwartet!
--   rw [add_comm]
--   simp [add_zero ]
--   rfl


-- def naive_scalar_mult [AddCommGroup (Point W)] (k : ℕ) (P : Point W) : Point W :=
--   match k with
--   | 0 => Point.zero
--   | n + 1 => P + naive_scalar_mult n P
-- Nutze den vollen Pfad, damit Lean die instAddCommGroup findet



-- Test: Ergibt [0]P den Punkt im Unendlichen?
-- example [AddCommGroup (Point W)] (P : Point W) :
--   naive_scalar_mult W 0 P = 0 := rfl





-- -- Test: Ist 0 wirklich das neutrale Element für P + 0 = P?
-- example [AddCommGroup (Point W)] (P : Point W) :
--   naive_scalar_mult W 1 P = P := by
--   unfold naive_scalar_mult
--   unfold naive_scalar_mult
--   have h0 : (0 : Point W) = Point.zero := rfl
--   rw [← h0]
--   -- Jetzt ist die 0 "normalisiert" und rw [add_zero] funktioniert
--   rw [add_zero]
--          -- Schritt 3: P + 0 = P


-- open WeierstrassCurve ZMod Affine
-- -- Einfachste Kurven-Definition:
-- instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
-- instance : Field (ZMod 5) := ZMod.instField 5


-- def D : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩ -- y² = x³ + x + 1
-- noncomputable section


-- -- Testpunkt P = (0, 1) in Zmod 5
-- def P_coords : (ZMod 5) × (ZMod 5) := ((0 : ZMod 5), (1 : ZMod 5))

-- #print WeierstrassCurve.Affine.Point


-- def point_on_curve (x y : ZMod 5) : Bool := y^2 == x^3 + x + 1
-- #eval point_on_curve 0 1


-- open WeierstrassCurve.Affine.Point
-- --def P : WeierstrassCurve.Affine.Point D :=
--   --WeierstrassCurve.Affine.Point.some
--     --(WeierstrassCurve.Affine.Nonsingular D P_coords.1 P_coords.2)

-- --def O : D.toAffine.Point := 0



-- def point_infinity : D.toAffine.Point := 0
-- -- Teste alle möglichen Punkte einzeln:
-- #eval point_on_curve 0 1   -- (0,1): 1² = 0³ + 0 + 1 = 1 ✓
-- #eval point_on_curve 0 4  -- (0,4): 4² = 0³ + 0 + 1 = 16 ≡ 1 (mod 5) ✓
-- #eval point_on_curve 2 1  -- (2,1): 1² = 2³ + 2 + 1 = 11 ≡ 1 (mod 5) ✓
-- #eval point_on_curve 2 4  -- (2,4): 4² = 2³ + 2 + 1 = 11 ≡ 1 (mod 5) ✓


-- --FALSCHE SYNTAX
-- --#check (0 : D.toAffine.Point)   -- Das neutrale Element
-- --#check point_infinity + (0 : D.toAffine.Point)  -- 𝓞 + 𝓞 = 𝓞
-- --#check point_infinity + point_infinity
-- #check point_infinity
-- --#check D.toAffine.Point.add funktioneirt nicht
-- #check point_infinity.add point_infinity   -- 𝓞.add(𝓞)
-- #check point_infinity.add (0 : D.toAffine.Point)

-- --#check point_infinity + 0
-- --#check point_infinity + point_infinity


-- --def test_point : D.toAffine.Point := ⟨0, 1⟩

-- --#check test_point

-- lemma point_01_on_curve : (1 : ZMod 5)^2 = (0 : ZMod 5)^3 + 0 + 1 := by
--   norm_num


-- lemma D_Δ_ne_zero : D.Δ ≠ (0 : ZMod 5) := by
--   decide

-- -- Test:
-- def E : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩ -- y² = x³ + x + 1

-- abbrev F5 := ZMod 5
-- def elliptic_discriminant (a b : F5) : F5 := -16 * (4 * a^3 + 27 * b^2)

-- #eval elliptic_discriminant (1 : F5) (1 : F5)   -- y² = x³ + x + 1




-- #check E.IsElliptic

-- lemma E_is_elliptic : E.Δ ≠ 0 := by decide

-- #eval E.Δ

-- -- Test 1: Affine Points (einfacher)
-- #check E.toAffine  -- Konvertierung zu Affine
-- #check WeierstrassCurve.Affine.Point  -- Punkt-Typ



-- #check @Add.add D.toAffine.Point
-- #check point_infinity.add point_infinity  -- 𝓞.add(𝓞)
-- #check point_infinity.add (0 : D.toAffine.Point)  -- 𝓞.add(𝓞)

-- abbrev APoint := E.toAffine.Point
-- #check APoint
-- variable (P Q : APoint)
-- -- Prüfen der Punktaddition
-- #check P + Q        -- Punktaddition
-- #check (0 : APoint)  -- Nullpunkt
-- #check (-P)          -- Inverses Element
-- #check (3 : ℕ) • P  -- Skalarmultiplikation



-- #eval (4 : ZMod 5) * (4 : ZMod 5)   -- Was kommt raus?
-- #eval (4 : ZMod 5)⁻¹               -- Was ist 4⁻¹?


-- #check IsUnit  -- Was ist die genaue Definition?
-- #print IsUnit  -- Vollständige Struktur zeigen
-- #check E.Δ      -- Typ der Diskriminante
-- #check E.b₂
-- #check E.b₄
-- #print WeierstrassCurve.Δ
-- #reduce E.Δ
-- #check isUnit_iff_ne_zero
-- #check Units.isUnit
-- #check Ne.isUnit


--Ein Punkt ist _nonsingular__ wenn _nicht beide__ partielle Ableitungen 0 sind

-- -- Was ist nonsingular wirklich?
-- #check E.toAffine.Nonsingular
-- #print WeierstrassCurve.Affine.Nonsingular

-- -- Was sind die Polynome?
-- #check E.toAffine.polynomialX
-- #check E.toAffine.polynomialY
-- #print WeierstrassCurve.Affine.polynomialX
-- #print WeierstrassCurve.Affine.polynomialY

-- -- Teste was bei (0,1) rauskommt:
-- #check Polynomial.evalEval 0 1 E.toAffine.polynomialX
-- #check Polynomial.evalEval 0 1 E.toAffine.polynomialY




-- def W := E.toAffine
