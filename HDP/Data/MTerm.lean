import HDP.Data.Monomial
import Init.Grind.Ring.Field

/-!

  Monomial-coefficient terms. The coefficients are in a `Field`.

-/

open Lean.Grind (Field)

namespace HDP.Data

/--
  A monomial term is a coefficient `coeff` multiplied by a monomial.
-/
structure MTerm (F : Type u) [Field F] where
  coeff : F := 1
  monomial : Monomial := #[]
deriving Inhabited, DecidableEq

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

def lexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.lexOrder t₁.monomial t₂.monomial
def revLexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.revlexOrder t₁.monomial t₂.monomial
def grlexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.grlexOrder t₁.monomial t₂.monomial
def grevlexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.grevlexOrder t₁.monomial t₂.monomial

protected def zero : MTerm F := mk 0 Monomial.unit
instance instZero : Zero (MTerm F) := ⟨MTerm.zero⟩
instance instInhabited : Inhabited (MTerm F) := ⟨0⟩

protected def one : MTerm F := mk 1 Monomial.unit

def normalize (t : MTerm F) : MTerm F :=
  mk t.coeff (Monomial.trim t.monomial)

def toString [ToString F] : MTerm F → String
  | ⟨c, m⟩ =>
  let mStr := m.toString
  if mStr = "0" then
    s!"{c}"
  else
    if c = 1 then
      s!"{m}"
    else if c = (-1 : F) then
      s!"-{m}"
    else
      s!"{c} {m}"

instance instToString (F : Type u) [Field F] [DecidableEq F] [ToString F] : ToString (MTerm F) :=
  ⟨toString⟩

instance instCoeOfNat [NatCast F] : Coe Nat (MTerm F) := ⟨λ n => mk n Monomial.unit⟩
instance instCoeOfInt [IntCast F] : Coe Int (MTerm F) := ⟨λ i => mk i Monomial.unit⟩
instance instCoeOfMonomial : Coe Monomial (MTerm F) := ⟨λ m => normalize (mk 1 m)⟩

def neg (t : MTerm F) : MTerm F :=
  let t := normalize t
  mk (-t.coeff) t.monomial

protected def add (t₁ t₂ : MTerm F) : MTerm F :=
  let t₁ := normalize t₁
  let t₂ := normalize t₂
  let m₁ := t₁.monomial
  let m₂ := t₂.monomial
  if m₁ = m₂ then
    mk (t₁.coeff + t₂.coeff) m₁
  else
    panic! "monomials must be equal"

protected def sub (t₁ t₂ : MTerm F) : MTerm F :=
  let t₁ := normalize t₁
  let t₂ := normalize t₂
  let m₁ := t₁.monomial
  let m₂ := t₂.monomial
  if m₁ = m₂ then
    mk (t₁.coeff - t₂.coeff) m₁
  else
    panic! "monomials must be equal"

protected def mul (t₁ t₂ : MTerm F) : MTerm F :=
  let t₁ := normalize t₁
  let t₂ := normalize t₂
  mk (t₁.coeff * t₂.coeff) (t₁.monomial * t₂.monomial)

instance instNeg : Neg (MTerm F) := ⟨neg⟩
instance instAdd : Add (MTerm F) := ⟨MTerm.add⟩
instance instSub : Sub (MTerm F) := ⟨MTerm.sub⟩
instance instMul : Mul (MTerm F) := ⟨MTerm.mul⟩

-- It is up to the field to implement division by 0
def div? (t₁ t₂ : MTerm F) : Option (MTerm F) :=
  let ⟨c₁, m₁⟩ := normalize t₁
  let ⟨c₂, m₂⟩ := normalize t₂
  if c₂ = 0 then
    none
  else
    match m₁.div? m₂ with
    | none   => none
    | some m => mk (c₁ / c₂) m

/-- Division when you're confident it will work. -/
def div! (t₁ t₂ : MTerm F) : MTerm F :=
  let ⟨c₁, m₁⟩ := normalize t₁
  let ⟨c₂, m₂⟩ := normalize t₂
  mk (c₁ / c₂) (m₁.div! m₂)

end MTerm

end HDP.Data
