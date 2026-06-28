import HDP.Data.Poly

open Lean.Grind (Field)

namespace HDP.Data

/--
  Representation (of a polynomial) of the form

    `coeffs[0] * y₁ + ... + coeffs[n-1] * yₙ = const`.

  where `y₁ ... yₙ` are not stored.
-/
structure LinearForm (F : Type u) [Field F] [DecidableEq F] where
  coeffs : Array P[F]   -- p₁ ... pₙ
  const : P[F]          -- a

@[inherit_doc] scoped notation "LF[" F "]" => LinearForm F



namespace LinearForm

variable {F : Type u} [Field F] [DecidableEq F]

def size (lf : LF[F]) : Nat := lf.coeffs.size

private def coeffStrings [ToString F] (coeffs : Array P[F]) : Array String :=
  let rec loop (i : Nat) (acc : Array String) : Array String :=
    if h : i < coeffs.size then
      let p := coeffs[i]
      let acc' :=
        if p = 0 then
          acc
        else
          acc.push s!"({p}) * y{i + 1}"
      loop (i + 1) acc'
    else
      acc
  termination_by coeffs.size - i
  loop 0 #[]

def toString [ToString F] (lf : LF[F]) : String :=
  let lhs := " + ".intercalate (coeffStrings lf.coeffs).toList
  let lhs := if lhs.length = 0 then "0" else lhs
  s!"{lhs} = {lf.const}"

instance instToString [ToString F] : ToString LF[F] := ⟨toString⟩

end LinearForm


namespace Monomial

def eraseVarOnce (m : Monomial) (x : Nat) : Monomial :=
  if h : x < m.size then
    Monomial.trim (m.set x 0)
  else
    Monomial.trim m

end Monomial


namespace Poly

variable {F : Type u} [Field F] [DecidableEq F]

private inductive LinearPart where
  | const
  | linear (idx : Nat) (monomial : Monomial)
  | nonlinear

/--
  Classify a monomial by its occurrence of the variables listed in `ys`.

  + `const`: contains no variable from `ys`;
  + `linear j m`: contains exactly one occurrence of `ys[j]`, with remaining coefficient monomial `m`;
  + `nonlinear`: contains a higher power of one `ys` variable or multiple variables from `ys`.
-/
private def ClassifyLinearPart (m : Monomial) (ys : Array Nat) : LinearPart :=
  let m := Monomial.trim m
  let rec loop (i : Nat) (found : Option (Nat × Nat)) : LinearPart :=
    if h : i < ys.size then
      let y := ys[i]
      let e := m.get y
      if e = 0 then
        loop (i + 1) found
      else if e = 1 then
        match found with
        | none => loop (i + 1) (some (i, y))
        | some _ => .nonlinear
      else
        .nonlinear
    else
      match found with
      | none => .const
      | some (j, y) => .linear j (m.eraseVarOnce y)
  termination_by ys.size - i
  loop 0 none

private def pushCoeffAt (coeffs : Array P[F]) (i : Nat) (t : M[F]) :
    Array P[F] :=
  if h : i < coeffs.size then
    coeffs.set i (coeffs[i].push t)
  else
    coeffs

/--
  Convert a polynomial equation `p = 0` into its linear form

    `coeffs[0] * y₁ + ... + coeffs[n-1] * yₙ = const`.

  If any term is nonlinear in `ys`, return `none`.
-/
def linearizeIn (p : P[F]) (ys : Array Nat) : Option LF[F] :=
  let init : LF[F] := {
    coeffs := Array.replicate ys.size 0,
    const := 0
  }
  let rec loop (i : Nat) (lf : LF[F]) : Option LF[F] :=
    if h : i < p.size then
      let t := MTerm.normalize p[i]
      match ClassifyLinearPart t.monomial ys with
      | .linear j m =>
          let coeffTerm := MTerm.normalize { coeff := t.coeff, monomial := m }
          loop (i + 1) { lf with coeffs := pushCoeffAt lf.coeffs j coeffTerm }
      | .const =>
          loop (i + 1) { lf with const := lf.const.push (-t) }
      | .nonlinear =>
          none
    else
      some
        { coeffs := lf.coeffs.map Poly.canonicalize
          const := Poly.canonicalize lf.const }
  termination_by p.size - i
  loop 0 init

def constantPartIn (p : P[F]) (us : Array Nat) : P[F] :=
  let init : P[F] := 0
  let rec loop (i : Nat) (c : P[F]) : P[F] :=
    if h : i < p.size then
      let t := MTerm.normalize p[i]
      match ClassifyLinearPart t.monomial us with
      | .const => loop (i + 1) (c + t)
      | _ => loop (i + 1) c
    else
      c.canonicalize
  loop 0 init

end Poly
