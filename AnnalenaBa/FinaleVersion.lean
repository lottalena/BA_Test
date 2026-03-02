import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic

import Mathlib.Tactic


structure EllipticCurve (F : Type*) [Field F] where
  a : F
  b : F
  -- Δ = 4a³ + 27b² ≠ 0
  discriminant_nonzero : 4 * a^3 + 27 * b^2 ≠ 0


def point_on_curve {F : Type*} [Field F] [DecidableEq F] (E : EllipticCurve F) (x y : F) : Prop :=
  y^2 = x^3 + E.a * x + E.b

instance {F : Type*} [Field F] [DecidableEq F] (E : EllipticCurve F) (x y : F) :
  Decidable (point_on_curve E x y) :=
  decidable_of_iff (y^2 = x^3 + E.a * x + E.b) Iff.rfl

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩
instance : Fact (Nat.Prime 17) := ⟨by decide⟩


-- E₅: y² = x³ + x + 1 auf  ZMod 5
-- Diskriminante: 4*1³ + 27*1² = 4 + 27 = 31 ≡ 1 (mod 5) ≠ 0. Gültig!
def E5 : EllipticCurve (ZMod 5) := {
  a := 1
  b := 1
  discriminant_nonzero := by decide
}

-- E₁₃: y² = x³ + x + 1 auf ZMod 13
-- Diskriminante: 4 + 27 = 31 = 5 (mod 13) ≠ 0. Gültig!
def E13 : EllipticCurve (ZMod 13) := {
  a := 1
  b := 1
  discriminant_nonzero := by decide
}

-- E₁₇: y² = x³ + 2x + 3 auf ZMod 17
def E17 : EllipticCurve (ZMod 17) := {
  a := 2
  b := 3
  discriminant_nonzero := by decide
}

-- TESTS
#eval decide (point_on_curve E5 0 1)  -- true
#eval decide (point_on_curve E5 0 4)  -- true
#eval decide (point_on_curve E5 0 2)  -- false



-- Hilfsfunktion für Division
def field_div {F : Type*} [Field F] (a b : F) : F := a * b⁻¹

-- Universelle Punktaddition (Affine Koordinaten)
def explicit_point_add {F : Type*} [Field F] [DecidableEq F] (E : EllipticCurve F)
  (x₁ y₁ x₂ y₂ : F) : Option (F × F) :=
  if hx : x₁ = x₂ then
    if hy : y₁ = -y₂ then
      -- Fall: P + (-P) = O
      none
    else
      -- Fall: P + P = 2P (Verdopplung)
      let L := field_div (3 * x₁^2 + E.a) (2 * y₁)
      let x₃ := L^2 - 2 * x₁
      -- y₃ = λ(x₁ - x₃) - y₁
      let y₃ := L * (x₁ - x₃) - y₁
      some (x₃, y₃)
  else
    -- Fall: P + Q (Addition)
    let L := field_div (y₁ - y₂) (x₁ - x₂)
    let x₃ := L^2 - x₁ - x₂
    let y₃ := L * (x₁ - x₃) - y₁
    some (x₃, y₃)

def point_negate {F : Type*} [Field F] (x y : F) : F × F := (x, -y)


namespace SanityLemmas
variable {F : Type*} [Field F]

/-- Dokumentationslemma: `field_div` ist dieselbe Operation wie `/` im Feld. -/
lemma field_div_eq_div (a b : F) : field_div a b = a / b := by
  simp [field_div, div_eq_mul_inv]

/-- Additionsfall: aus `x₁ ≠ x₂` folgt, dass der Nenner `x₁ - x₂` nicht 0 ist. -/
lemma denom_ne_zero_add {x₁ x₂ : F} (hx : x₁ ≠ x₂) : (x₁ - x₂) ≠ 0 := by
  exact sub_ne_zero.mpr hx

/--
Verdopplungsfall: `2*y ≠ 0` folgt aus `2 ≠ 0` und `y ≠ 0`.
Hinweis: `2 ≠ 0` ist in Charakteristik 2 falsch, daher als Voraussetzung.
-/
lemma denom_ne_zero_double {y : F} (h2 : ((2 : F) ≠ 0)) (hy : y ≠ 0) : (2 * y) ≠ 0 := by
  exact mul_ne_zero h2 hy

/-- Formel-Identität (Addition): deine `L`-Definition ist die Sekantensteigung. -/
lemma slope_add_formula (y₁ y₂ x₁ x₂ : F) :
    field_div (y₁ - y₂) (x₁ - x₂) = (y₁ - y₂) / (x₁ - x₂) := by
  simp [field_div, div_eq_mul_inv]

/-- Formel-Identität (Verdopplung): deine `L`-Definition ist die Tangentensteigung. -/
lemma slope_double_formula (a x₁ y₁ : F) :
    field_div (3 * x₁^2 + a) (2 * y₁) = (3 * x₁^2 + a) / (2 * y₁) := by
  simp [field_div, div_eq_mul_inv]

end SanityLemmas



-- Test: Verdopplung auf E₅ (0,1) + (0,1)
#eval explicit_point_add E5 0 1 0 1
-- Jetzt sollte 'some (4, 2)' herauskommen.
-- Check: 2² = 4. x³+x+1 = 4³+4+1 = 69 = 4 mod 5. STIMMT!

-- Test: Addition auf E₅ (0,1) + (2,1)
#eval explicit_point_add E5 0 1 2 1
-- Erwartung: some (3, 2)

-- Test 4: Addition mit Inversem (P + (-P))
-- (0,1) + (0,4) auf E₅ (da 4 ≡ -1 mod 5)
#eval explicit_point_add E5 0 1 0 4
-- Erwartung: none (Infinity)


--  Definition des Datentyps + verpacken die Koordinaten in einen schönen Typen
inductive EllipticPoint (F : Type*) [Field F] where
  | infinity : EllipticPoint F             -- Das neutrale Element O
  | point (x y : F) : EllipticPoint F      -- Ein normaler Punkt (x,y)
deriving Repr, DecidableEq

namespace EllipticPoint

variable {F : Type*} [Field F] [DecidableEq F]

-- Das neutrale Element ist 0
instance : Zero (EllipticPoint F) := ⟨infinity⟩

-- Hilfsfunktion: Wandelt das 'Option' Ergebnis von der Rechung in den gewünschten Typ um
def from_option (opt : Option (F × F)) : EllipticPoint F :=
  match opt with
  | none => infinity
  | some (x, y) => point x y

-- Die Additions-Funktion (Verbindet Kurve mit Punkten)
def add_or_double (E : EllipticCurve F) (P Q : EllipticPoint F) : EllipticPoint F :=
  match P, Q with
  | infinity, _ => Q  -- 0 + Q = Q
  | _, infinity => P  -- P + 0 = P
  | point x₁ y₁, point x₂ y₂ =>
      from_option (explicit_point_add E x₁ y₁ x₂ y₂)

-- Negation (P -> -P)
def neg : EllipticPoint F → EllipticPoint F
| infinity => infinity
| point x y => point x (-y)

end EllipticPoint

namespace TestSuite
open EllipticPoint

--  Testdaten für die Standardkurve E5: y² = x³ + x + 1 über ZMod 5
def P : EllipticPoint (ZMod 5) := point 0 1
def P_doubled : EllipticPoint (ZMod 5) := point 4 2  --  2P

-- Punkt Q für Fall 5 (Addition P + Q mit P ≠ Q)
-- P + 2P = 3P.
-- (0,1) + (4,2)
-- λ = (2-1)/(4-0) = 1/4 = 1*4 = 4
-- x₃ = 4² - 0 - 4 = 16 - 4 = 12 = 2
-- y₃ = 4*(0 - 2) - 1 = -8 - 1 = -9 = 1
-- Also Q = (2, 1)
def Q : EllipticPoint (ZMod 5) := point 2 1

-- ----------------------------------------------------------------
-- FALL 1: Identität (P + O = P)
-- ----------------------------------------------------------------
-- Logik: Greift im 'match' Block von EllipticPoint.add
#eval EllipticPoint.add_or_double E5 P EllipticPoint.infinity
-- ERWARTUNG: point 0 1

-- ----------------------------------------------------------------
-- FALL 2: Inverse (P + (-P) = O)
-- ----------------------------------------------------------------
-- Logik: x₁ = x₂, y₁ = -y₂ (hier 1 = -4). Greift im 'if y₁ = -y₂'.
-- addieren von (0,1) und (0,4)
#eval EllipticPoint.add_or_double E5 P (EllipticPoint.neg P)
-- ERWARTUNG: infinity

-- ----------------------------------------------------------------
-- FALL 3: Vertikale Tangente (P + P mit y=0 => O)
-- ----------------------------------------------------------------
-- Logik: x₁ = x₂, y₁ = -y₂ (weil 0 = -0). Greift im 'if y₁ = -y₂'.
-- spezielle Kurve E_Vert (y² = x³ + 1) und Punkt V(4,0)
def E_Vert : EllipticCurve (ZMod 5) := {
  a := 0, b := 1, discriminant_nonzero := by decide
}
def V : EllipticPoint (ZMod 5) := point 4 0

#eval EllipticPoint.add_or_double E_Vert V V
-- ERWARTUNG: infinity

-- ----------------------------------------------------------------
-- FALL 4: Reguläre Verdopplung (P + P = 2P)
-- ----------------------------------------------------------------
-- Logik: x₁ = x₂, aber y₁ ≠ -y₂ (y≠0). Greift im inneren 'else'.
-- Tangentenformel wird genutzt.
#eval EllipticPoint.add_or_double E5 P P
-- ERWARTUNG: point 4 2

-- ----------------------------------------------------------------
-- FALL 5: Reguläre Addition (P + Q)
-- ----------------------------------------------------------------
-- Logik: x₁ ≠ x₂ (0 ≠ 4). Greift im äußeren 'else'.
-- Sekantenformel wird genutzt.
-- P(0,1) + 2P(4,2) = 3P(2,1)
#eval EllipticPoint.add_or_double E5 P P_doubled
-- ERWARTUNG: point 2 1


end TestSuite


namespace Algorithms
open EllipticPoint -- Damit 'add', 'infinity' etc. genutzen werden können

variable {F : Type*} [Field F] [DecidableEq F]

-- 1. Naive Skalarmultiplikation (Referenz)
-- Definition: k * P = P + (k-1)*P
-- Laufzeit: Linear O(k) - Sehr langsam für große Zahlen
-- ----------------------------------------------------------------
def naive_scalar_mult (E : EllipticCurve F) (k : ℕ) (P : EllipticPoint F) : EllipticPoint F :=
  match k with
  | 0 => infinity
  | n + 1 => add_or_double E P (naive_scalar_mult E n P)


-- ----------------------------------------------------------------
-- 2. Double-and-Add (LSB-First Variante)
-- Laufzeit: Logarithmisch O(log k) - Extrem schnell
-- Iteration über die Bits von k (Least Significant Bit first)
-- ----------------------------------------------------------------
def double_and_add (E : EllipticCurve F) (k : ℕ) (P : EllipticPoint F) : EllipticPoint F :=
  -- Hilfsfunktion: Rekursion über die Liste der Bits
  let rec loop (bits : List Bool) (acc : EllipticPoint F) (base : EllipticPoint F) : EllipticPoint F :=
    match bits with
    | [] => acc -- Keine Bits mehr übrig -> Ergebnis zurückgeben
    | b :: bs =>
      -- b ist das aktuelle Bit (true=1, false=0)
      -- bs sind die restlichen Bits

      -- Wenn Bit=1: Addiere Basis zum Akkumulator. Sonst behalte Akkumulator.
      let new_acc := if b then add_or_double E acc base else acc
      -- Verdopple die Basis für die nächste Runde (base = 2 * base)
      let new_base := add_or_double E base base
      -- Rekursiver Aufruf mit restlichen Bits
      loop bs new_acc new_base
  -- Start der Rekursion:
  -- bits = k.bits (z.B. für 13 -> [true, false, true, true])
  -- acc  = infinity (Startwert 0)
  -- base = P (Startwert 1*P)
  loop k.bits infinity P

-- ================================================================
-- PERFORMANCE & KORREKTHEITS-CHECK
-- ================================================================

-- W Kurve E5 und den Punkt P(0,1)
def P_test : EllipticPoint (ZMod 5) := point 0 1

-- 1. Kleiner Test: Stimmen beide Algorithmen bei k=3 überein?
-- 3 * P = P + 2P = (0,1) + (4,2) = (2,1) (TestSuite)
#eval naive_scalar_mult E5 3 P_test
-- Erwartung: point 2 1

#eval double_and_add E5 3 P_test
-- Erwartung: point 2 1

-- 2. Performance Vergleich
-- Berechung 1.000.000 * P

def million := 1000000

-- A) Double-and-Add:
-- Das sollte in < 100ms fertig sein.
#eval double_and_add E5 million P_test
-- Erwartung: kein problem bei berechung

-- B) Naive Methode:
--  '#eval naive_scalar_mult E5 million P_test' -> (Stack Overflow)
-- Testen mit 10000, das geht noch:
#eval naive_scalar_mult E5 10000 P_test

-- Testen mit 1000000, das geht nicht mehr :)
end Algorithms

-- ================================================================
-- TEIL 5: DER FORMALE BEWEIS
-- ================================================================

namespace Proofs
open EllipticPoint
open Algorithms

-- Variablen-Deklaration für den Namespace
variable {F : Type*} [Field F] [DecidableEq F]

-- 1. Die Gruppen-Annahme
class EllipticCurveGroup (E : EllipticCurve F) where
  add_assoc : ∀ P Q R : EllipticPoint F, add_or_double E (add_or_double E P Q) R = add_or_double E P (add_or_double E Q R)
  add_comm  : ∀ P Q : EllipticPoint F, add_or_double E P Q = add_or_double E Q P
  add_zero  : ∀ P : EllipticPoint F, add_or_double E P infinity = P
  zero_add  : ∀ P : EllipticPoint F, add_or_double E infinity P = P

variable {E : EllipticCurve F} [GroupE : EllipticCurveGroup E]

-- 2. Hilfs-Lemmata

-- Lemma: n*P + m*P = (n+m)*P
lemma naive_add (n m : ℕ) (P : EllipticPoint F) :
  add_or_double E (naive_scalar_mult E n P) (naive_scalar_mult E m P) = naive_scalar_mult E (n + m) P :=
by
  induction n with
  | zero =>
    -- Fall n=0: 0 + m*P = m*P
    simp [naive_scalar_mult, EllipticCurveGroup.zero_add]
  | succ n ih =>
    -- HIER WAR DER FEHLER:
    -- Statt 'Nat.add_succ' 'Nat.succ_add' (da n+1 links steht)
    simp only [naive_scalar_mult, Nat.succ_add]
    -- P + (nP + mP) = P + (n+m)P
    rw [EllipticCurveGroup.add_assoc]
    rw [ih]

-- Lemma: 2 * (n*P) = n * (2*P)
lemma naive_mul_two (n : ℕ) (P : EllipticPoint F) :
  naive_scalar_mult E (2 * n) P = naive_scalar_mult E n (add_or_double E P P) :=
by
  induction n with
  | zero => simp [naive_scalar_mult]
  | succ n ih =>
    -- 2*(n+1) = 2n + 2
    rw [Nat.mul_succ]
    -- LHS aufspalten: naive (2n) P + naive 2 P
    rw [← naive_add]
    rw [ih]
    -- naive 2 P ist P + P.  'base' Argument für rechts.
    -- ZU zeigen: naive n (2P) + 2P = naive (n+1) (2P)
    simp only [naive_scalar_mult]
    -- naive n (2P) + 2P = 2P + naive n (2P) (Kommutativität)
    rw [EllipticCurveGroup.add_zero]
    rw [EllipticCurveGroup.add_comm]


-- benötigt Lemma, das sagt: "Wenn wir eine Zahl k in Bits zerlegen
-- und wieder zusammensetzen, kommt k raus."
-- um sich auf Elliptische Kurven zu konzentrieren. TBD Later / Lieber mathlib version
-- hot fix
--lemma fromBits_bits_eq_id (k : ℕ) : fromBits (Nat.bits k) = k := sorry

def fromBits (bits : List Bool) : ℕ :=
  match bits with
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * fromBits bs


lemma fromBits_bits_eq_id (n : ℕ) : fromBits (Nat.bits n) = n := by
  -- Induktion über die binäre Darstellung (binaryRec')
  -- Aus import Data.Nat.Bits.lean
  induction n using Nat.binaryRec' with
  | zero =>
    -- Fall n = 0
    --  zero_bits : bits 0 = []
    rw [Nat.zero_bits]
    -- fromBits [] ist 0
    rfl
  | bit b m h ih =>
    -- Fall n = bit b m (also 2*m + b)
    -- h garantiert die "kanonische" Darstellung (keine führenden Nullen)
    -- 1.  'bits_append_bit'
    rw [Nat.bits_append_bit m b h]
    -- 2. Definition von fromBits anwenden (Rekursionsschritt)
    simp only [fromBits]
    -- 3. Induktionshypothese anwenden (fromBits (bits m) = m)
    rw [ih]
    -- 4. Zeigen, dass (if b then 1 else 0) + 2 * m das Gleiche ist wie bit b m
    cases b
    · -- Fall false: 0 + 2*m = bit false m
      simp [Nat.bit]
    · -- Fall true: 1 + 2*m = bit true m
      simp [Nat.bit, Nat.add_comm]

-- 3. Hauptbeweis (Loop Invariante)


lemma loop_correct (bits : List Bool) (acc base : EllipticPoint F) :
  double_and_add.loop E bits acc base =
  add_or_double E acc (naive_scalar_mult E (fromBits bits) base) :=
by
  induction bits generalizing acc base with
  | nil =>
    simp [double_and_add.loop, fromBits, naive_scalar_mult, EllipticCurveGroup.add_zero]
  | cons b bs ih =>
    simp only [double_and_add.loop, fromBits]
    by_cases h : b = true
    · -- Fall Bit=1
      simp? [h]
      rw [ih]
      -- Aktuelles Ziel (vereinfacht):
      -- (acc + base) + naive n (2P) = acc + naive (1 + 2n) P

      -- 1. Links: 'naive n (2P)' umformen zu 'naive (2n) P'
      --  das Lemma rückwärts (←)
      rw [← naive_mul_two]
      -- 2. Links: Klammern verschieben (Assoziativität)
      -- Aus (acc + base) + Rest wird acc + (base + Rest)
      rw [EllipticCurveGroup.add_assoc]
      -- 3. Rechts: 'naive (1 + 2n) P' aufspalten
      -- naive_add rückwärts: naive (n+m) -> naive n + naive m
      rw [← naive_add]
      -- 4. Rechts: 'naive 1 P' zu 'P' vereinfachen
      simp [naive_scalar_mult, EllipticCurveGroup.add_zero]
      -- Links:  acc + (base + naive (2 * ...) base)
      -- Rechts: acc + (base + naive (2 * ...) base)
    · -- Fall Bit=0
      simp? [h]
      rw [ih]
      -- Aktuelles Ziel:
      -- acc + naive n (2P) = acc + naive (0 + 2n) P

      -- 2. Links: 'naive n (2P)' umformen zu 'naive (2n) P'
      rw [← naive_mul_two]
      -- Beide Seiten sind identisch.

theorem double_and_add_eq_naive (k : ℕ) (P : EllipticPoint F) :
  double_and_add E k P = naive_scalar_mult E k P :=
by
  rw [double_and_add]
  rw [loop_correct]
  rw [EllipticCurveGroup.zero_add] -- acc war am Anfang infinity
  rw [fromBits_bits_eq_id]         --  Hilfsfunktion zurück zu k

end Proofs
