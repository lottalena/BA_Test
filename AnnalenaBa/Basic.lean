import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.Defs    -- Field Division Instanzen
import Mathlib.Data.ZMod.Defs        -- ZMod spezifische Operationen
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Defs
import Mathlib.FieldTheory.Finite.Basic   -- Finite Field Lemmas
import Mathlib.Tactic.FieldSimp         -- field_simp Taktik
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic



-- Primzahl-Instanzen (bereits vorhanden)
instance : Fact (Nat.Prime 5) := { out := Nat.prime_five }
instance : Fact (Nat.Prime 7) := { out := Nat.prime_seven }
instance : Fact (Nat.Prime 11) := { out := Nat.prime_eleven }
instance : Fact (Nat.Prime 13) := by decide
-- funktoniert

#check Nat.Prime 13

-- Test: Welche norm_num Erweiterungen gibt es?
#check @norm_num  -- Zeigt verfügbare Extensionen

-- Test: Direkte Primzahl-Definition
#check Nat.prime_iff  -- Definition von Primzahlen


-- Typ-Aliases
abbrev F5 := ZMod 5
abbrev F7 := ZMod 7
abbrev F11 := ZMod 11
abbrev F13 := ZMod 13

-- Grundlegende Tests
#check F5        -- ZMod 5 : Type
#check F7        -- ZMod 7 : Type

-- Quadrate testen (für y² in elliptischen Kurven):
#eval (2 : F5) ^ 2  -- 4
#eval (3 : F5) ^ 2  -- 4 (gleich wie 2²!)
#eval (4 : F5) ^ 2  -- 1

-- Welche Zahlen sind Quadrate in F5?
-- 0² = 0, 1² = 1, 2² = 4, 3² = 4, 4² = 1
-- Also: Quadrate = {0, 1, 4}, Nicht-Quadrate = {2, 3}


-- Grundrechenformen :
#eval (3 : F5) + (2 : F5)    -- Addition
#eval (3 : F5) * (2 : F5)    -- Multiplikation
#eval (3 : F5) - (2 : F5)    -- Subtraktion
--#eval (3 : F5) / (2 : F5)  -- HDiv nicht gefunden

-- Statt "/" verwenden Sie Inverse:
#eval (3 : F5) * (2 : F5)⁻¹  -- Multiplikation mit Inverses 4

-- Körper-Eigenschaften testen:
example : (0 : F5) + (3 : F5) = 3 := rfl
example : (2 : F5) * (3 : F5) = 1 := rfl  -- 6 ≡ 1 mod 5
-- example : (3 : F5) * (2 : F5)⁻¹ = 4 := rfl
--funktioniert nicht da Lean das Inverse mit rfl nicht vereinfachen kann
-- ZMod hat spezielle Vereinfachungsregeln:
example : (3 : F5) * (2 : F5)⁻¹ = 4 := by
  -- Schritt 1: Zeige dass 2 * 3 = 1 in F5
  have h1 : (2 : F5) * (3 : F5) = 1 := rfl
  -- Schritt 2: Daraus folgt 2⁻¹ = 3
  have h2 : (2 : F5)⁻¹ = 3 := by
    apply inv_eq_of_mul_eq_one_right
    exact h1
  -- Schritt 3: 3 * 3 = 4 in F5
  rw [h2]
  rfl

-- Spezifische Lemmas für F5 (prkatisch und funktional, aber bisschen nervig langfristig)
lemma inv_2_F5 : (2 : F5)⁻¹ = 3 := by
  apply inv_eq_of_mul_eq_one_right; rfl

lemma inv_3_F5 : (3 : F5)⁻¹ = 2 := by
  apply inv_eq_of_mul_eq_one_right; rfl

lemma inv_4_F5 : (4 : F5)⁻¹ = 4 := by
  apply inv_eq_of_mul_eq_one_right; rfl

-- Dann einfach:
example : (3 : F5) * (2 : F5)⁻¹ = 4 := by rw [inv_2_F5]; rfl
-- Funktionierende Division-Funktion

--def field_div (a b : F5) : F5 := a * b⁻¹ -- -> funktioniert dann nur für F5


-- Funktioniert für ALLE endlichen Körper
def field_div {F : Type*} [Field F] (a b : F) : F := a * b⁻¹

-- Tests:
#eval field_div (3 : F5) (2 : F5)    -- Funktioniert
#eval field_div (6 : F11) (7 : F11)   -- Funktioniert auch!
#eval field_div (1 : F7) (3 : F7)    -- Für alle Körper


-- Alternativ also field_div nicht notwendig
#eval (3 : F5) * (2 : F5)⁻¹
#eval (6 : F11) * (7 : F11)⁻¹
#eval (1 : F7) * (3 : F7)⁻¹



-- Verschiedene Inverse-Syntax testen:
#check (2 : F5)⁻¹                    -- Existiert -> 2⁻¹ : F5

-- Mehr Division-Tests:
#eval (1 : F7) * (3 : F7)⁻¹  -- Ergibt 5 (3*5=15≡1 mod 7)
#eval (4 : F5) * (3 : F5)⁻¹  -- Test mit anderen Zahlen -> 3
#eval (6 : F11) * (7 : F11)⁻¹ -- Test in größerem Körper -> 4
#eval (7: F13) * (3 : F13)⁻¹ -- -> 11


-- Testen Sie diese:
#check @ZMod.inv           -- Inverse-Funktion
#check @Inv.inv            -- Allgemeine Inverse
--#check @Field.inv          -- Field-Inverse
#check @Units.inv          -- Units-Inverse

-- ZMod-spezifische Lemmas:
--#check @ZMod.cast_inv      -- Cast-Inverse
#check @ZMod.inv_zero      -- Inverse von 0
--#check @ZMod.mul_inv       -- Multiplikation mit Inverse


-- Test Ecc


-- Diskriminante einer elliptischen Kurve y² = x³ + ax + b
def elliptic_discriminant (a b : F5) : F5 := -16 * (4 * a^3 + 27 * b^2)

-- kleine weißstrauß gleichung


-- Test: y² = x³ + 2x + 3 über F5
#eval elliptic_discriminant (2 : F5) (3 : F5)
-- > 0 siguläre Kurve -> nicht geeignet für ECC
-- Testen von andere Kurven-Parameter:
#eval elliptic_discriminant (1 : F5) (1 : F5)  -- y² = x³ + x + 1
#eval elliptic_discriminant (0 : F5) (1 : F5)  -- y² = x³ + 1
#eval elliptic_discriminant (1 : F5) (0 : F5)  -- y² = x³ + x


-- Punkt-auf-Kurve Test
def point_on_curve (x y a b : F5) : Bool := y^2 == x^3 + a*x + b

-- Tests:
#eval point_on_curve (0 : F5) (0 : F5) (2 : F5) (3 : F5)   -- (0,0) auf y²=x³+2x+3? Nein

-- Definiert die nicht-singuläre Kurve: y² = x³ + 1x + 1
-- Parameter: (x=0, y=1, a=1, b=1)
#eval point_on_curve (0 : F5) (1 : F5) (1 : F5) (1 : F5)
-- Erwartetes Ergebnis: true
