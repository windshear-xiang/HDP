import HDP.Data.Poly

open Lean.Grind (Field)

namespace HDP.Data.Buchberger

inductive PolyHistory (F : Type u) [Field F] [DecidableEq F] where
  | zero
  | basis (idx : Nat)
  | scalarMul (c : F) (p : PolyHistory F)
  | termMul (t : MTerm F) (p : PolyHistory F)
  | addHist (p₁ p₂ : PolyHistory F)
  | subHist (p₁ p₂ : PolyHistory F)
deriving Inhabited

/-- Historied polynomials. -/
structure HPoly (F : Type u) [Field F] [DecidableEq F] where
  poly : Poly F
  history : PolyHistory F
deriving Inhabited

@[inherit_doc] scoped notation "HP[" F "]" => HPoly F

variable {F : Type u} [Field F] [DecidableEq F]

------------------------------------------------------------

namespace PolyHistory

local notation "PH[ " F " ]" => PolyHistory F

instance instZero : Zero PH[F] := ⟨.zero⟩

def toString [ToString F] : PH[F] → String
  | .zero => "0"
  | .basis idx => s!"[{idx}]"
  | .scalarMul c p => s!"({c} * {toString p})"
  | .termMul t p => s!"({t} * {toString p})"
  | .addHist p₁ p₂ => s!"({toString p₁} + {toString p₂})"
  | .subHist p₁ p₂ => s!"({toString p₁} - {toString p₂})"

instance instToString [ToString F] : ToString PH[F] := ⟨toString⟩

def pushNeg : PH[F] → PH[F]
  | .zero => .zero
  | .basis idx => .scalarMul (-1) (.basis idx)
  | .scalarMul c h =>
    if c = -1 then h
    else .scalarMul (-c) h
  | .termMul t h => .termMul (-t) h
  | .addHist h₁ h₂ => .subHist (pushNeg h₁) h₂
  | .subHist h₁ h₂ => .addHist (pushNeg h₁) h₂

protected def add : PH[F] → PH[F] → PH[F]
  | .zero, h₂ => h₂
  | h₁, .zero => h₁
  | h₁, h₂ => .addHist h₁ h₂

instance instAdd : Add PH[F] := ⟨.add⟩

protected def sub : PH[F] → PH[F] → PH[F]
  | .zero, h₂ => .scalarMul (-1) h₂
  | h₁, .zero => h₁
  | h₁, h₂ => .subHist h₁ h₂

instance instSub : Sub PH[F] := ⟨.sub⟩

def scmul : F → PH[F] → PH[F]
  | _, .zero => .zero
  | c, h =>
    if c = 1 then h
    else if c = -1 then pushNeg h
    else .scalarMul c h

instance instScMul : HMul F PH[F] PH[F] := ⟨scmul⟩

end PolyHistory

------------------------------------------------------------

namespace HPoly

def toString [ToString F] (p : HP[F]) : String :=
  let ⟨p, h⟩ := p
  s!"⟪{p}, {h}⟫"
instance instToString [ToString F] : ToString HP[F] := ⟨toString⟩

-- Divides by the leading coefficient across the whole polynomial.
-- This makes the leading coefficient 1.
def monic (p : HP[F]) : HP[F] :=
  let ⟨p, pHist⟩ := p
  if p = 0 then ⟨p, pHist⟩ else
  let leadingCoeff := p.leadingTerm.coeff
  let pDivC := p.map (λ ⟨c, m⟩ =>
    MTerm.mk (c / leadingCoeff) m
  )
  HPoly.mk pDivC ((1 / leadingCoeff) * pHist)

-- Returns `true` if the criterion means that we should check the `(i, j)` pair
-- In other words, if for all `l`, the leading term doesn't divide the `lcm`
def secondCriterion (basis : Array HP[F]) (i j : Nat) (lcm : Monomial)
    (hj : j < basis.size) : Bool :=
  /- Buchberger's second criterion is to run over all pairs (i, l) and (j, l)
     that we have already visited in buchberger's algorithm and check that
     LT(l) does NOT divide LCM(LT(i), LT(j)). -/
  let rec loop (l : Nat) : Bool :=
    if hl : l < j then
      if l = i then
        loop (l + 1)
      else
        let ⟨p, _⟩ := basis[l]
        let ltl := p.leadingTerm.monomial
        match lcm.div? ltl with
        | none => loop (l + 1)
        | some _ => false
    else
      true
  loop 0

/--
  Returns the S-polynomial, if the second criterion is met.
  Otherwise, returns `none`.

  The caller must ensure that neither `basis[i]` nor `basis[j]` is 0.
-/
def sPoly (basis : Array HP[F]) (i j : Nat)
    (hi : i < basis.size) (hj : j < basis.size) (cmp : MOrder) : Option HP[F] :=

  let ⟨f, fHist⟩ := basis[i]
  let ⟨g, gHist⟩ := basis[j]

  let ltf := f.leadingTerm
  let ltg := g.leadingTerm

  match Monomial.lcmIfNotCoprime ltf.monomial ltg.monomial with
  | none => none
  | some lcm =>
    if secondCriterion basis i j lcm hj then
      -- The LCM is always divisible by the leading terms
      let qf := MTerm.div! lcm ltf
      let qg := MTerm.div! lcm ltg

      let left := qf * f
      let leftHist := .termMul qf fHist

      let right := qg * g
      let rightHist := .termMul qg gHist

      let sp := Poly.sub left right cmp
      let hist := leftHist - rightHist
      some <| HPoly.mk sp hist
    else
      none

partial def divPolysUpTo (p : HP[F]) (ps : Array HP[F]) (n : Nat) (hn : n ≤ ps.size)
    (cmp : MOrder := Monomial.grevlexOrder) : (Array HP[F] × HP[F]) :=
  let ⟨pp, pHist⟩ := p
  let rec loop (p r : Poly F) (qs : Array HP[F])
      (hqs : qs.size = ps.size) : (Array HP[F] × HP[F]) :=
    if p = 0 then
      -- Construct the history for the remainder
      --    p = q * (basis) + rem  <===>  rem = p - q * (basis)
      let folded := qs.foldl (init := 0) (fun hist ⟨_, qHist⟩ => hist + qHist)
      let subHist := pHist - folded
      (qs, HPoly.mk r subHist)
    else
    let ltp := p.leadingTerm

    let rec innerLoop (i : Nat) :=
      if hi : i < n then
        -- Assume that none of the `ps` are the zero polynomial
        let ⟨pi, piHist⟩ := ps[i]
        let lti := pi.leadingTerm
        match ltp.div? lti with
        | none => innerLoop (i + 1)
        | some qt =>
          -- Calculate the "quotient part" we subtract from `p`
          let qt_mul_pi := qt * pi
          let qt_mul_pi_hist := .termMul qt piHist

          -- Add the "multiple" part of the quotient to `qs[i]`
          let ⟨qi, qiHist⟩ := qs[i]
          let qi_add_qt := Poly.add qi qt cmp
          let qi_add_qt_hist := qiHist + qt_mul_pi_hist
          let qs' := qs.set i (HPoly.mk qi_add_qt qi_add_qt_hist)
          let p' := Poly.sub p qt_mul_pi
          loop p' r qs' (by simp [qs', hqs])
      else
        -- No division was found, subtract and return
        let r' := Poly.add r ltp cmp
        let p' := Poly.sub p ltp cmp
        loop p' r' qs hqs

    innerLoop 0

  let qs := Array.replicate ps.size (HPoly.mk 0 0)
  have hqs : qs.size = ps.size := by
    simp only [Array.size_replicate, qs]
  loop pp 0 qs hqs

/--
  Divides polynomial `p` by the list `ps`.

  During division, we construct an array of `HP[F]`s, but instead of
  pairing the quotients with their histories, the histories instead
  represent `qi * ps[i]`, and is built as the division continues.

  At the end, the remainder's history is constructed by subtracting
  `p`'s history from the sum of quotient histories. This eliminates
  the need of doing polynomial multiplication.
-/
partial def divPolys (p : HP[F]) (ps : Array HP[F])
    (cmp : MOrder := Monomial.grevlexOrder) : (Array HP[F] × HP[F]) :=
  divPolysUpTo p ps ps.size (Nat.le_refl _) cmp

def constructWitness (n : Nat) (h : PolyHistory F) (cmp : MOrder) : Array P[F] :=
  let zeros : Array P[F] := Array.replicate n 0
  have h_zeros : zeros.size = n := by
    simp only [Array.size_replicate, zeros]
  let one : P[F] := #[MTerm.mk (1 : F) Monomial.unit]

  let rec loop : PolyHistory F → ({ arr : Array P[F] // arr.size = n })
    | .zero => ⟨zeros, h_zeros⟩

    | .basis i =>
      if hi : i < n then
        let w := zeros.set i one
        ⟨w, by simp [w, h_zeros]⟩
      else
        dbg_trace s!"constructWitness: index {i} out of bounds (basis size {n})"
        ⟨zeros, h_zeros⟩

    | .scalarMul c h =>
      match loop h with
      | ⟨w, hw⟩ =>
        let t : M[F] := MTerm.mk c Monomial.unit
        let w' : Array P[F] := w.map (λ p => t * p)
        ⟨w', by simp [w']; exact hw⟩

    | .termMul t h =>
      match loop h with
      | ⟨w, hw⟩ =>
        let w' : Array P[F] := w.map (λ p => t * p)
        ⟨w', by simp [w']; exact hw⟩

    | .addHist h₁ h₂ =>
      let ⟨w₁, hw₁⟩ := loop h₁
      let ⟨w₂, hw₂⟩ := loop h₂
      let w := w₁.zipWith (Poly.add · · cmp) w₂
      ⟨w, by simp [w, hw₁, hw₂]⟩

    | .subHist h₁ h₂ =>
      let ⟨w₁, hw₁⟩ := loop h₁
      let ⟨w₂, hw₂⟩ := loop h₂
      let w := w₁.zipWith (Poly.sub · · cmp) w₂
      ⟨w, by simp [w, hw₁, hw₂]⟩

  loop h

end HPoly

-- Minimize the basis, but keep the history of new derived polynomials
def minimizeBasis (ps : Array HP[F]) : Array HP[F] :=
  let rec loop (i : Nat) (minBasis : Array HP[F]) : Array HP[F] :=
    if hi : i < ps.size then
      let ⟨pi, piHist⟩ := ps[i]
      let lti := pi.leadingTerm

      -- Returns if we should include pi in the basis
      let rec innerLoop (j : Nat) : Bool :=
        if hj : j < ps.size then
          if i = j then innerLoop (i + 1) else
          let ⟨pj, pjHist⟩ := ps[j]
          let ltj := pj.leadingTerm
          -- If pi is divisible by pj, then we can safely drop it
          match lti.div? ltj with
          | none => innerLoop (j + 1)
          | some q => false
        else true

      if innerLoop i then loop (i + 1) (minBasis.push ⟨pi, piHist⟩)
      else                loop (i + 1) minBasis
    else
      minBasis

  loop 0 #[]

partial def buchbergers (ps : Array P[F]) (cmp : MOrder := Monomial.grevlexOrder) :
    Array HP[F] :=
  -- Transform polynomials into history annotated ones
  let hPolys : Array HP[F] :=
    ps.mapIdx (λ i p => HPoly.mk p (.basis i)) |>.map HPoly.monic

  let rec loop (i j checked len : Nat) (hij : i < j)
      (basis : Array HP[F]) (h_len : len ≤ basis.size) :=
    if hi : i < len then
      if hj : j < len then
        match HPoly.sPoly basis i j (by omega) (by omega) cmp with
        | none => loop i (j + 1) checked len (by omega) basis h_len
        | some ⟨s, sHist⟩ =>
          match HPoly.divPolysUpTo ⟨s, sHist⟩ basis len h_len cmp with
          | (qs, ⟨rem, remHist⟩) =>
            if rem ≠ 0 then
              let remMonic := HPoly.monic ⟨rem, remHist⟩
              loop i (j + 1) checked len (by omega) (basis.push remMonic)
                (by simp [Array.size_push]; exact Nat.le_succ_of_le h_len)
            else
              loop i (j + 1) checked len (by omega) basis h_len
      else
        let i' := i + 1
        let j' := max (i' + 1) checked
        loop i' j' checked len (by omega) basis h_len
    else
      if h_len' : len ≥ basis.size then
        basis
      else
        let checked' := len
        let i' := 0
        let j' := max (i' + 1) checked'
        let len' := basis.size
        loop i' j' checked' len' (by omega) basis (Nat.le_refl _)

  let basisRes := loop 0 1 0 0 (by omega) hPolys (Nat.zero_le _)
  minimizeBasis basisRes

/--
  Returns `some qs`, where `qs` are a "linear" combination of the starting
  basis polynomials `ps` that, when added together, equal `p`.

  Computes the ideal from Buchberger's algorithm.
-/
partial def idealMembership (p : P[F]) (ps : Array P[F])
    (cmp : MOrder := Monomial.grevlexOrder) : Option (Array P[F]) :=
  -- canonicalize Polynomials before compute
  let p := Poly.canonicalize p cmp
  let ps := ps.map (Poly.canonicalize · cmp)
  -- compute
  let n := ps.size
  let basis := buchbergers ps
  let (_, ⟨rem, remHist⟩) := HPoly.divPolys (HPoly.mk p (.basis n)) basis cmp
  if rem.size = 0 then
    match remHist with
    | .subHist h₁ h₂ =>
      match h₁ with
      | .basis n =>
        -- Calculate the Array witness in terms of the basis,
        -- which are themselves historied in terms of the original basis polynomials
        some <| HPoly.constructWitness n h₂ cmp
      | _ => panic! "LHS of sub isn't right"
    | _ => panic! "Shape of history is wrong for rem of 0"
  else
    none

end HDP.Data.Buchberger
