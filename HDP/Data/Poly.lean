import HDP.Data.MTerm

open Lean.Grind (Field)

namespace HDP.Data

/-- Concrete representation of polynomials. (Array of `MTerm`s.) -/
structure Poly (F : Type u) [Field F] [DecidableEq F] where
  terms : Array (MTerm F)
deriving Inhabited

/-structure PolyRef where
  index : Nat
  history : PolyHistory
deriving Inhabited -/

@[inherit_doc] scoped notation "M[" F "]" => MTerm F
@[inherit_doc] scoped notation "P[" F "]" => Poly F

namespace Poly

variable {F : Type u} [Field F] [DecidableEq F]

/-- Drop all tail 0s in monomials, and drop zero coeff terms -/
def normalizeTerms (p : P[F]) : P[F] :=
  ⟨(p.terms.map MTerm.normalize).filter (fun t => decide (t.coeff ≠ 0))⟩

instance instCoeOfArray : Coe (Array M[F]) P[F] :=
  ⟨fun ts => normalizeTerms ⟨ts⟩⟩

instance instDecidableEq : DecidableEq P[F] := by
  intro p q
  cases p
  cases q
  simp only [mk.injEq]
  infer_instance

def size (p : P[F]) : Nat := p.terms.size

instance instGetElem : GetElem P[F] Nat M[F] (fun p i => i < p.size) where
  getElem p i h := p.terms[i]

def push (p : P[F]) (t : M[F]) : P[F] :=
  let t := MTerm.normalize t
  if t.coeff = 0 then p else ⟨p.terms.push t⟩
def pop (p : P[F]) : P[F] := ⟨p.terms.pop⟩
def back? (p : P[F]) : Option M[F] := p.terms.back?
def qsort (p : P[F]) (lt : M[F] → M[F] → Bool) : P[F] := ⟨p.terms.qsort lt⟩
def toList (p : P[F]) : List M[F] := p.terms.toList

def map (p : P[F]) (f : M[F] → α) : Array α := p.terms.map f

protected def zero : P[F] := ⟨#[]⟩
protected def one : P[F] := ⟨#[MTerm.one]⟩

instance instZero : Zero P[F] := ⟨Poly.zero⟩
instance instInhabited : Inhabited P[F] := ⟨0⟩

def ofMonomial (m : Monomial) : P[F] := ⟨#[MTerm.normalize ⟨1, m⟩]⟩
def ofMTerm (t : MTerm F) : P[F] :=
  let t := MTerm.normalize t
  if t.coeff = 0 then 0 else ⟨#[t]⟩

instance instCoeOfMTerm : Coe M[F] P[F] := ⟨ofMTerm⟩
instance instCoeOfMonomial : Coe Monomial P[F] := ⟨ofMonomial⟩

def toString [ToString F] (p : P[F]) : String :=
  let p := normalizeTerms p
  if p.size = 0 then
    "0"
  else
    let rec loop (i : Nat) (str : String) : String :=
      if h : i < p.size then
        let t := p[i]
        let c := t.coeff
        let m := t.monomial
        if str.length > 0 then
          if t.toString.startsWith "-" then
            loop (i + 1) (str ++ s!" - {MTerm.mk (-c) m}")
          else
            loop (i + 1) (str ++ s!" + {MTerm.mk c m}")
        else
          loop (i + 1) s!"{MTerm.mk c m}"
      else str
    termination_by p.size - i
    loop 0 ""

instance instToString [ToString F] : ToString P[F] := ⟨toString⟩

def leadingTerm (p : P[F]) : M[F] :=
  if h : p.size > 0 then
    MTerm.normalize p[0]
  else
    ⟨0, Monomial.unit⟩

/-- Divide leading coefficient to make it 1 -/
def monic (p : P[F]) : P[F] :=
  let p := normalizeTerms p
  if p.size = 0 then p else
  let leadingCoeff := p.leadingTerm.coeff
  ⟨p.map (λ t => MTerm.normalize ⟨t.coeff / leadingCoeff, t.monomial⟩)⟩

protected def neg (p : P[F]) : P[F] :=
  p.map (λ t => -t)

instance instNeg : Neg P[F] := ⟨Poly.neg⟩

/--
  Adds two polynomials by combining like terms.

  Assumes that the polynomial is sorted in decreasing order under `cmp`.
-/
protected def add (p₁ p₂ : P[F]) (cmp : MOrder := Monomial.grevlexOrder) : P[F] :=
  let numTerms₁ := p₁.size
  let numTerms₂ := p₂.size
  let totalNumTerms := numTerms₁ + numTerms₂
  let rec loop (i j : Nat) (p : P[F]) : P[F] :=
    if i + j < totalNumTerms then
      if hi : i < numTerms₁ then
        if hj : j < numTerms₂ then
          let t₁ := p₁[i]
          let t₂ := p₂[j]
          let c₁ := t₁.coeff
          let c₂ := t₂.coeff
          let m₁ := t₁.monomial
          let m₂ := t₂.monomial
          match cmp m₁ m₂ with
          | .lt => loop i (j + 1) (p.push t₂)    -- Push the larger one
          | .gt => loop (i + 1) j (p.push t₁)    -- Push the smaller one
          | .eq =>
            -- Check if the coefficients cancel
            let c := c₁ + c₂
            if c ≠ 0 then
              loop (i + 1) (j + 1) (p.push (MTerm.mk c m₁))
            else
              loop (i + 1) (j + 1) p
        else
          -- p₂ is done, so push the rest of p₁
          loop (i + 1) j (p.push p₁[i])
      else if hj : j < numTerms₂ then
        -- p₁ is done, so push the rest of p₂
        loop i (j + 1) (p.push p₂[j])
      else
        p
    else
      p
  termination_by totalNumTerms - i - j
  loop 0 0 0

-- NB: This will use the `grevLexOrder` ordering.
--     To supply a different ordering, call `add` directly.
instance instAdd : Add P[F] := ⟨Poly.add⟩

protected def sub (p₁ p₂ : P[F]) (cmp : MOrder := Monomial.grevlexOrder) : P[F] :=
  let numTerms₁ := p₁.size
  let numTerms₂ := p₂.size
  let totalNumTerms := numTerms₁ + numTerms₂
  let rec loop (i j : Nat) (p : P[F]) : P[F] :=
    if i + j < totalNumTerms then
      if hi : i < numTerms₁ then
        if hj : j < numTerms₂ then
          let t₁ := p₁[i]
          let t₂ := p₂[j]
          let c₁ := t₁.coeff
          let c₂ := t₂.coeff
          let m₁ := t₁.monomial
          let m₂ := t₂.monomial
          match cmp m₁ m₂ with
          | .lt => loop i (j + 1) (p.push (-t₂)) -- Push the larger one
          | .gt => loop (i + 1) j (p.push t₁)    -- Push the smaller one
          | .eq =>
            -- Check if the coefficients cancel
            let c := c₁ - c₂
            if c ≠ 0 then
              loop (i + 1) (j + 1) (p.push (MTerm.mk c m₁))
            else
              loop (i + 1) (j + 1) p
        else
          -- p₂ is done, so push the rest of p₁
          loop (i + 1) j (p.push p₁[i])
      else if hj : j < numTerms₂ then
        -- p₁ is done, so push the rest of p₂
        loop i (j + 1) (p.push (-p₂[j]))
      else
        p
    else
      p
  termination_by totalNumTerms - i - j
  loop 0 0 0

-- NB: This will use the `grevLexOrder` ordering.
--     To supply a different ordering, call `add` directly.
instance instSub : Sub P[F] := ⟨Poly.sub⟩

def mul_term_poly (t : M[F]) (p : P[F]) : P[F] :=
  p.map (λ t' => t * t')

def mul_poly_term (p : P[F]) (t : M[F]) : P[F] :=
  mul_term_poly t p

instance instHMulTermPoly : HMul M[F] P[F] P[F] := ⟨mul_term_poly⟩
instance instHMulPolyTerm : HMul P[F] M[F] P[F] := ⟨mul_poly_term⟩

protected def mul (p₁ p₂ : P[F]) (cmp : MOrder := Monomial.grevlexOrder) : P[F] :=
  let prods := p₂.map (λ t₂ => p₁ * t₂)
  prods.foldl (init := 0) (Poly.add · · cmp)

instance instMul : Mul P[F] := ⟨Poly.mul⟩

/-- Raises a polynomial to a natural number power using binary exponentiation. -/
protected def scPow (p : P[F]) : Nat → P[F]
  | 0 => Poly.one
  | 1 => p
  | n =>
    let rec loop (acc base : P[F]) (k : Nat) : P[F] :=
      if k = 0 then acc
      else
        let acc' := if k % 2 = 1 then acc * base else acc
        loop acc' (base * base) (k / 2)
    termination_by k
    loop Poly.one p n

instance instHPow : HPow P[F] Nat P[F] := ⟨Poly.scPow⟩

-- Divides `p₁` by `p₂`. Returns a pair `(q, r)`.
-- If `p₂` is zero, returns `(0, 0)`.
protected partial def div (p₁ p₂ : P[F]) (cmp : MOrder := Monomial.grevlexOrder) : P[F] × P[F] :=
  let lt₂ := p₂.leadingTerm
  if lt₂ = 0 then (0, 0) else

  /-
    Repeatedly loop on the remainder `r` until the leading term of `p₂` (`lt₂`)
    cannot divide the leading term of `r`. Subtract the new term from `r`
    and add the appropriate quotient to `q`.
  -/
  let rec loop (q r : P[F]) : P[F] × P[F] :=
    if r = 0 then (q, 0) else
    let ltr := r.leadingTerm
    match ltr.div? lt₂ with
    | none => (q, r)
    | some qt =>
      let q' := Poly.add q qt cmp
      -- CC: This can probably be optimized(?)
      let r' := Poly.sub r (qt * p₂) cmp
      loop q' r'
  loop 0 p₁

/--
  Divides a polynomial `p` by an array of polynomials `ps`.

  Returns a pair `(qs, r)`, where `qs` is an array of quotients of the same
  size as `ps`, and where `r` is the remainder polynomial, such that

    `p = ps ⬝ qs + r`

  where `·` denotes the dot product under polynomial multiplication.

  The caller must ensure that `ps` does not contain the zero polynomial.

  The division is unique up to the ordering of the polynomials in `ps`.
-/
partial def divPolys (p : P[F]) (ps : Array P[F])
    (cmp : MOrder := Monomial.grevlexOrder) : (Array P[F] × P[F]) :=
  let n := ps.size
  let rec loop (p r : P[F]) (qs : Array P[F])
      (hqs : qs.size = ps.size) : (Array P[F] × P[F]) :=
    if p = 0 then (qs, r) else
    let ltp := p.leadingTerm

    let rec innerLoop (i : Nat) :=
      if hi : i < n then
        -- TODO: ASSUMES NOT ZERO POLY HERE
        let lti := ps[i].leadingTerm
        match ltp.div? lti with
        | none => innerLoop (i + 1)
        | some qt =>
          let qt_mul_pi := qt * ps[i]
          let qs' := qs.set i (Poly.add qs[i] qt cmp)
          let p' := Poly.sub p qt_mul_pi cmp
          loop p' r qs' (by simp [qs', hqs])
      else
        -- No division was found, subtract and return
        let r' := Poly.add r ltp cmp
        let p' := Poly.sub p ltp cmp
        loop p' r' qs hqs

    innerLoop 0

  let qs : Array P[F] := Array.replicate ps.size 0
  have hqs : qs.size = ps.size := by
    simp only [Array.size_replicate, qs]
  loop p 0 qs hqs

/--
  the canonical sorted form of a polynomial:
  sorts terms in decreasing order under `cmp`, merges like monomials
-/
def canonicalize (p : P[F]) (cmp : MOrder := Monomial.grevlexOrder) : P[F] :=
  let p := normalizeTerms p
  -- `Array.qsort lt`: `lt a b = true` ⇒ `a` comes before `b`. We want
  -- larger monomials first, i.e. `a > b ↔ cmp b.mon a.mon = .lt`.
  let sorted := p.qsort (λ a b => cmp b.monomial a.monomial = .lt)
  let rec loop (i : Nat) (acc : P[F]) : P[F] :=
    if h : i < sorted.size then
      let t := sorted[i]
      if t.coeff = 0 then
        loop (i + 1) acc
      else
        match acc.back? with
        | none => loop (i + 1) (acc.push t)
        | some prev =>
          match cmp prev.monomial t.monomial with
          | .eq =>
            let newCoeff := prev.coeff + t.coeff
            let acc' := acc.pop
            if newCoeff = 0 then
              loop (i + 1) acc'
            else
              loop (i + 1) (acc'.push (MTerm.mk newCoeff prev.monomial))
          | _ => loop (i + 1) (acc.push t)
    else
      acc
  termination_by sorted.size - i
  loop 0 0

end Poly

end HDP.Data
