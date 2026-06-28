import HDP.Data.Buchberger
import HDP.Data.Poly

open HDP.Data

/-
  Example
-/

-- -x2 * x3 + x1
def p₁ : P[Rat] := ⟨#[MTerm.mk (-1) #[0, 1, 1], MTerm.mk 1 #[1]]⟩
-- x1 * x5 + x4
def p₂ : P[Rat] := ⟨#[MTerm.mk (-1) #[1, 0, 0, 0, 1], MTerm.mk 1 #[0, 0, 0, 1]]⟩
-- x2
def p₃ : P[Rat] := ⟨#[MTerm.mk 1 #[0, 1]]⟩
-- x4
def p : P[Rat] := ⟨#[MTerm.mk 1 #[0, 0, 0, 1]]⟩

-- Expected output:   some #[x5, 1, x3 * x5]
#eval Buchberger.idealMembership p #[p₁, p₂, p₃]



/-
  Example: difference of squares
-/
-- x - y
def x_minus_y : P[Rat] := ⟨#[MTerm.mk 1 #[1], MTerm.mk (-1) #[0, 1]]⟩
#eval x_minus_y
def xx_minus_yy : P[Rat] := ⟨#[MTerm.mk 1 #[2], MTerm.mk (-1) #[0, 2]]⟩
#eval xx_minus_yy

-- Expected: some #[x2 + x1]
#eval Buchberger.idealMembership xx_minus_yy #[x_minus_y]




/-
  Example from Harrison's paper: cancellation property for congruences
-/

-- [ a,  n,  x,  y,  d,  u,  v]
-- [x1, x2, x3, x4, x5, x6, x7]

-- ay − ax − nd
def q₁ : P[Rat] := ⟨#[MTerm.mk 1 #[1, 0, 0, 1], MTerm.mk (-1) #[1, 0, 1], MTerm.mk (-1) #[0, 1, 0, 0, 1]]⟩
#eval q₁
-- au + nv − 1
def q₂ : P[Rat] := ⟨#[MTerm.mk 1 #[1, 0, 0, 0, 0, 1], MTerm.mk 1 #[0, 1, 0, 0, 0, 0, 1], MTerm.mk (-1) #[]]⟩
#eval q₂
-- n
def q₃ : P[Rat] := ⟨#[MTerm.mk 1 #[0, 1]]⟩
#eval q₃
-- y - x
def q : P[Rat] := ⟨#[MTerm.mk 1 #[0, 0, 0, 1]]⟩ - ⟨#[MTerm.mk 1 #[0, 0, 1]]⟩
#eval q

#eval Buchberger.idealMembership q #[q₁, q₂, q₃]
