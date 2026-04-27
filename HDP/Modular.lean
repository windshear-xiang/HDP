/-

`modular`: A tactic to discharge goals about modular arithmetic.

Authors: Cayden Codel

-/

import Init.Data.Int.Basic
import Std.Data.HashMap

-- import Qq

import Lean.Expr
import Lean.Meta.Canonicalizer
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Rewrite

import Init.Omega.Logic
import HDP.Core

import HDP.Poly
import HDP.Poly.Eval

-- See the following import statement for the `omega` tactic's implementation
--import Lean.Elab.Tactic.Omega

namespace HDP

open Lean Meta Tactic Std Lean.Omega
open Qq

namespace Rat

/-
instance : ToExpr (Fin n) where
  toTypeExpr := .app (mkConst ``Fin) (toExpr n)
  toExpr a :=
    let r := mkRawNatLit a.val
    mkApp3 (.const ``OfNat.ofNat [0]) (.app (mkConst ``Fin) (toExpr n)) r
      (mkApp3 (.const ``Fin.instOfNat []) (toExpr n)
        (.app (.const ``Nat.instNeZeroSucc []) (mkNatLit (n-1))) r)

instance : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := if 0 ≤ i then
    mkNat i.toNat
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``Int []) (.const ``Int.instNegInt [])
      (mkNat (-i).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int []) r
        (.app (.const ``instOfNat []) r) -/

-- 将有理数 `r` 转换为 Lean 的 `Q(ℚ)` 元编程表达式（Expr），
-- 通过 `mkRat` 构造其分子（Int）和分母（Nat）。
def toExpr (r : ℚ) : Q(ℚ) :=
  match r with
  | ⟨n, d, _, _⟩ =>
    let n : Q(ℤ) := q($n)
    let d : Q(ℕ) := q($d)
    mkApp2 (.const ``mkRat []) n d

-- 返回有理数类型 `ℚ` 对应的类型表达式。
def toTypeExpr : Q(Type) :=
  q(Rat)

-- 为 `Rat` 提供 `ToExpr` 实例，使其可在元编程中被转换为 `Expr`。
instance instToExpr : ToExpr Rat := ⟨toExpr, toTypeExpr⟩

end Rat

-- Some necessary theorems

-- 整除关系的等价形式：`a ∣ b` 等价于"存在 c 使得 b = a * c"（正向）。
theorem Int.exists_of_dvd {a b : Int} : a ∣ b → ∃ c, b = a * c := id
-- 整除关系的等价形式（逆向）：由"存在 c 使得 b = a * c"推出 `a ∣ b`。
theorem Int.dvd_of_exists {a b : Int} : (∃ c, b = a * c) → (a ∣ b) := id

-- 等式在取负运算下的同余引理：若 a = b，则 -a = -b。
private theorem neg_congr {R : Type u} [CommRing R] {a b : R} (h : a = b) : -a = -b := by
  rw [h]

-- 二元运算在等式代换下的同余引理：若 a = b 且 c = d，则 op a c = op b d。
private theorem binop_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d) (op : R → R → R)
    : op a c = op b d := by
  rw [h₁, h₂]

-- 加法同余：若 a = b 且 c = d，则 a + c = b + d。
private theorem add_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a + c = b + d :=
  binop_congr h₁ h₂ (· + ·)

-- 减法同余：若 a = b 且 c = d，则 a - c = b - d。
private theorem sub_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a - c = b - d :=
  binop_congr h₁ h₂ (· - ·)

-- 乘法同余：若 a = b 且 c = d，则 a * c = b * d。
private theorem mul_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a * c = b * d :=
  binop_congr h₁ h₂ (· * ·)


namespace Monomial

/--
  Casts a monomial into a single `Expr`.
-/
-- 将单项式 `m`（即变量幂次的数组）转换为 Lean 元编程的 `Q(Monomial)` 表达式。
def toExpr (m : Monomial) : Q(Monomial) :=
  q($m)

-- 返回 `Monomial` 类型本身对应的类型表达式。
def toTypeExpr : Q(Type) :=
  q(Monomial)

-- 为 `Monomial` 提供 `ToExpr` 实例。
instance instToExpr : ToExpr Monomial := ⟨toExpr, toTypeExpr⟩

end Monomial

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

-- 将一个带系数单项式 `t : M[F]`（即 `MTerm F`）转换为元编程 `Expr`，
-- 通过 `MTerm.mk` 构造其系数和单项式部分。
def toExprM [instToExpr : ToExpr F] (t : M[F]) : MetaM Expr :=
  let ⟨c, m⟩ := t
  mkAppM ``MTerm.mk #[instToExpr.toExpr c, m.toExpr]

--def toTypeExpr : Expr :=
--  .const ``MTerm []

end MTerm

namespace Poly

variable {F : Type u} [Field F] [DecidableEq F]

-- 将多项式 `p : P[F]`（即 `Array (MTerm F)`）转换为元编程 `Expr`，
-- 生成一个字面量数组表达式，每个元素由 `MTerm.toExprM` 转换。
def toExprM [instToExpr : ToExpr F] (p : P[F]) : MetaM Expr := do
  let exprs ← p.mapM MTerm.toExprM
  mkArrayLit (instToExpr.toTypeExpr) exprs.toList

-- TODO: Refactor to include `R` later
--def toTypeExpr : Expr :=
--  .const ``Poly []

end Poly

--------------------------------------------------------------------------------


open Lean Meta

-- `gb` 策略的配置选项。
structure GBConfig where
  -- 是否自动展开析取（`Or`）假设，默认启用。
  splitDisjunctions : Bool := true

-- Gröbner 基算法的状态，贯穿整个 `GBM` 单子计算。
structure GBState (F : Type) [Field F] [DecidableEq F] [ToExpr F] where
  -- Field coefficient type (as an `Expr`)
  -- v : Level := 0
  -- F : Q(Type v) := q(ℚ)   -- But this fails
  -- F : Q(Type) := q(ℚ)

  -- Expressions to variable numbers
  -- Really of type `Std.HashMap Q($F) Nat`, but I can't get the hashing to work right
  -- 原子表达式（即环中的变量）到变量编号的映射（哈希表）。
  atoms : Std.HashMap Expr Nat := {}
  -- 按出现顺序排列的原子表达式数组，与变量编号一一对应。
  atomsInOrder : Array Expr := #[]

  -- CC: Ideally we would say `Array Q(Poly $F)`, but this requires
  --     a field to be inferred. Perhaps require a field only for ops?

  -- 从假设中提取的多项式数组（每条假设对应一个多项式）。
  polys : Array P[F] := #[]
  -- 每个多项式对应的 Lean 证明项（`Expr`），证明其等于零。
  polyProofs : Array Expr := #[]

  -- These are the expressions associated with the polynomial representations
  -- in `polys`. They are added in a one-to-one correspondence.
  -- In other `polyExprs` holds the hypotheses that are represented as polys
  -- 与 `polys` 一一对应的原始假设表达式数组。
  polyExprs : Array Expr := #[]

-- Gröbner 基计算的内层单子：携带 `GBState`（状态）和 `GBConfig`（只读配置）的规范化单子。
abbrev GBM' (F : Type) [Field F] [DecidableEq F] [ToExpr F] :=
  StateRefT (GBState F) (ReaderT GBConfig CanonM)

-- Maps to a pair `(p, prf)` where `p` is an `Expr` of type `Poly F` for
-- the field `F` in the state
-- 表达式到"多项式及其证明生成器"的缓存，避免对同一表达式重复转换。
def Cache (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] : Type :=
  Std.HashMap Expr (P[F] × GBM' F Expr)

-- Gröbner 基计算的外层单子：在 `GBM'` 基础上额外携带 `Cache`（转换缓存）。
abbrev GBM (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] :=
  StateRefT (Cache F) (GBM' F)

-- 运行 `GBM` 单子计算，初始状态为空缓存，返回 `MetaM` 结果。
def GBM.run {F : Type} [Field F] [DecidableEq F] [ToExpr F]
    (m : GBM F α) (st : GBState F := {}) (cfg : GBConfig) : MetaM α :=
  m.run' Std.HashMap.empty |>.run' st cfg |>.run'

--abbrev GBProof (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] : Type :=
--  GBM F Expr

-- 当前待求解的约束问题，记录哪些变量编号已被等式约束。
structure Problem where
  --assumptions : Array GBProof := ∅
  --numVars : Nat := 0
  equalities : Std.HashSet Nat := ∅

-- 元级别的待处理问题，包含待处理假设列表、析取列表和已处理集合。
structure MetaProblem where
  problem : Problem := {}
  /-- Pending facts to process -/
  facts : List Expr := []
  /-- Pending disjunctions. We case split these later. -/
  disjunctions : List Expr := []
  /-- Processed facts. We keep these to avoid duplicates. -/
  processedFacts : Std.HashSet Expr := ∅

-- 构造一个空的 `MetaProblem`（无任何约束的平凡问题）。
def MetaProblem.trivial : MetaProblem :=
  { problem := {} }

instance : Inhabited MetaProblem := ⟨MetaProblem.trivial⟩

variable {F : outParam Type} [Field F] [DecidableEq F] [ToExpr F]

-- 读取当前 `GBConfig` 配置（只读访问）。
def cfg : GBM F GBConfig :=
  read

-- 返回域 `F` 的类型表达式（用于构造 `Expr`）。
def fieldTypeExpr : GBM F Q(Type) := do
  return toTypeExpr F

-- 返回当前状态中所有原子（变量）表达式的有序数组。
def atoms : GBM F (Array Expr) := do
  return (← getThe (GBState F)).atomsInOrder

-- 返回当前状态中原子（变量）的数量。
def getNumAtoms : GBM F Nat := do
  return (← getThe (GBState F)).atomsInOrder.size

-- 返回当前状态中已收集的所有多项式。
def getPolys : GBM F (Array P[F]) := do
  return (← getThe (GBState F)).polys

-- 返回当前状态中与多项式一一对应的原始假设表达式数组。
def getPolyExprs : GBM F (Array Expr) := do
  return (← getThe (GBState F)).polyExprs

-- 返回当前已收集的多项式数量。
def getNumPolys : GBM F Nat := do
  return (← getPolys).size

-- 向状态中追加一个多项式 `p`、其证明 `proof` 以及对应的原始表达式 `e`。
def addPoly (p : P[F]) (proof e : Expr) : GBM F Unit := do
  modifyThe (GBState F) (fun s => { s with
    polys := s.polys.push p
    polyProofs := s.polyProofs.push proof
    polyExprs := s.polyExprs.push e
  })

-- 将当前所有原子表达式构造为字面量数组 `Expr`（用于 `Poly.eval` 的求值）。
def atomsAsArrayLitExpr : GBM F Expr := do
  mkArrayLit (← fieldTypeExpr) (← atoms).toList

-- CC: Defined in `OmegaM.lean`. What is the point of this?
/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
-- 构造带期望类型提示的自反等式证明 `(Eq.refl a : a = b)`，
-- 用于在 `a` 和 `b` 定义相等但类型推导需要显式标注时。
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

-- 从已有的等式证明 `proof`（证明 `p.eval atoms = e`）
-- 和目标表达式 `e` 重建一个证明 `e = p.eval atoms`（取对称并传递）。
def reconstructProof (proof : GBM F Expr) (e : Expr) : GBM F Expr := do
  mkEqTrans (← mkEqSymm (← proof)) e

/--
  For a given expression `e`, consults the atoms in the `GBState` to see if
  we have already encountered `e`. If so, return its index.
-/
-- 在状态中查找表达式 `e` 对应的变量编号。若已存在则直接返回，
-- 否则将其注册为新原子（变量），分配新编号并返回。
def lookup (e : Expr) : GBM F Nat := do
  let c ← getThe (GBState F)
  let e ← canon e
  --let F : Q(Type) ← fieldType
  --have e : Q($F) := e
  match c.atoms[e]? with
  | some i => return i
  | none =>
    trace[gb] s!"New atom: {e}"
    let i ← modifyGetThe (GBState F) fun c =>
      let cs := c.atoms.size
      (cs, { c with
        atoms := c.atoms.insert e cs
        atomsInOrder := c.atomsInOrder.push e
      })
    return i

/-def nameInField (constName : Name) (exprs : Array Expr) : GBM F Expr := do
  mkAppM constName exprs -/

-- 构造域 `F` 中的单位元 `1` 对应的 `Expr`，用于构造单项式等表达式。
def oneAsExpr : GBM F Expr := do
  let F : Q(Type) ← fieldTypeExpr
  let _ ← synthInstanceQ q(One $F)
  return q((1 : $F))

-- 将单项式 `m` 构造为系数为 1 的 `MTerm`，返回对应的 `Expr`。
def mtermExpr (m : Q(Monomial)) : GBM F Expr := do
  let one ← oneAsExpr
  mkAppM ``MTerm.mk #[one, m]

-- 构造 `atoms.get! i` 对应的 `Expr`（使用不安全访问，需确保下标合法）。
def asGet!Expr (atoms i : Expr) : GBM F Expr := do
  mkAppM ``Array.get! #[atoms, i]

-- 构造 `atoms.getD i v` 对应的 `Expr`（带默认值 `v` 的安全访问）。
def asGetDExpr (atoms i v : Expr) : GBM F Expr := do
  mkAppM ``Array.getD #[atoms, i, v]

-- 为第 `i` 个原子表达式 `e` 构造等式证明 `e = Poly.eval (eᵢ i) atoms`，
-- 其中 `eᵢ i` 是第 i 个标准基多项式（仅第 i 个变量的一次项）。
def mkEvalAtomEq (e : Expr) (i : Nat) : GBM F Expr := do
  let atoms ← atomsAsArrayLitExpr
  let i := toExpr i
  -- CC: Why do we need a refl proof to start, and then a trans eq proof?
  --     Can't we construct the proof directly?
  -- TODO: The types of `get` and `get!` don't agree

  -- A proof that `e = atoms.getD i 1`,
  -- tagged with the LHS/RHS type under `e` (which should belong to the ring)
  let eq₁ ← mkEqReflWithExpectedType e (← asGetDExpr atoms i (← oneAsExpr))

  -- A proof that `atoms.getD i 1 = Poly.eval ↑(eᵢ i) atoms`
  let eq₂ ← mkEqSymm <| ← mkAppM ``Poly.eval_eᵢ #[i, atoms]

  -- Returns a proof that `e = Poly.eval ↑(eᵢ i) atoms`
  mkEqTrans eq₁ eq₂

-- Returns a pair `(p, prf)` where `p` is an expression containing a `Poly F`
-- in some field, and `prf` is a proof that `e = p.eval atoms`
-- 将表达式 `e` 注册为新原子变量，返回对应的单变量多项式及其求值等式证明。
def mkVarAtom (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  -- Index of atom
  let i : ℕ ← lookup e
  let m := Monomial.eᵢ i
  return (Poly.ofMonomial m, mkEvalAtomEq e i)

-- 由比较函数 `cmp` 生成布尔序：`ord cmp a b = true` 当且仅当 `a > b`。
def ord {α : Type u} (cmp : α → α → Ordering) : α → α → Bool := fun a b =>
  match cmp a b with
  | .gt => true
  | _ => false

-- 构造单参数运算的等式传递证明：
-- 给定 `proof : x = p.eval atoms`，构造 `name(x) = name(p.eval atoms) = e` 的证明。
@[inline, always_inline]
def constructEqTransProof (e : Expr) (name : Name) (proof : GBM F Expr) : GBM F Expr := do
   mkEqTrans
    (← mkAppM name #[← proof])
    (← mkEqSymm e)

-- 构造双参数运算的等式传递证明：
-- 给定两个子证明，利用 `name`（如 `add_congr`）合并后传递到目标等式 `e`。
@[inline, always_inline]
def constructEqTransProof₂ (e : Expr) (name : Name) (proof₁ proof₂ : GBM F Expr) : GBM F Expr := do
  mkEqTrans
    (← mkAppM name #[← proof₁, ← proof₂])
    (← mkEqSymm e)

-- 为二元多项式运算（加/减/乘）构造对应的等式证明生成器。
-- `opStr` 指定运算名（"add"/"sub"/"mul"），利用 `Poly.eval_<op>` 和 `<op>_congr` 引理完成。
@[inline]
def binop_proof (opStr : String) (p₁ p₂ : P[F]) (proof₁ proof₂ : GBM F Expr) : GBM F (GBM F Expr) := do
  -- let op_name : Name := .str ``Poly opStr
  let eval_name : Name := .str ``Poly s!"eval_{opStr}"
  let congr_name : Name := .str .anonymous s!"{opStr}_congr"
  let eval_expr ← mkAppM eval_name #[← p₁.toExprM, ← p₂.toExprM, ← atomsAsArrayLitExpr]
  return constructEqTransProof₂ eval_expr congr_name proof₁ proof₂

mutual

/-

Transform a base expression, from the LHS of `(lhs : Int) = 0`,
into a polynomial.

-/

-- Returns the expression as a polynomial, tagged with its proof
-- 将 Lean 表达式 `e` 转换为多项式并生成其求值等式证明（带缓存优化）。
-- 先查缓存，命中则直接返回；否则调用 `asPolyImpl` 计算后存入缓存。
partial def asPoly (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  let cache ← get
  match cache.get? e with
  | some ⟨poly, proof⟩ =>
    trace[gb] s!"Found in cache: {e}"
    return (poly, proof)
  | none =>
    let ⟨poly, proof⟩ ← asPolyImpl e
    modifyThe (Cache F) fun cache => ( cache.insert e (poly, proof.run' cache) )
    return (poly, proof)

-- `asPoly` 的实际实现，对表达式结构进行模式匹配：
-- - 自由变量（FVar）：若有定义则展开后递归，否则注册为新原子变量；
-- - 加/减/乘：递归转换两个子表达式并合并；
-- - 取负：递归转换后取负；
-- - 其他（包括常量、未知形式）：作为原子变量处理。
partial def asPolyImpl (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  --trace[gb] s!"processing {e}"
  -- `omega` uses `groundInt?` here to shuffle casts and ops around
  if e.isFVar then
    if let some v ← e.fvarId!.getValue? then
      asPoly v
    else
      mkVarAtom e
  else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "add" p₁ p₂ proof₁ proof₂
    return (p₁ + p₂, proof)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "sub" p₁ p₂ proof₁ proof₂
    return (p₁ - p₂, proof)
  | (``Neg.neg, #[_, _, e']) =>
    let (p, proof) ← asPoly e'
    let proof : GBM F Expr := do
      let eval_neg ←
        mkAppM ``Poly.eval_neg #[← p.toExprM, ← atomsAsArrayLitExpr]
      constructEqTransProof eval_neg ``neg_congr proof
    return (-p, proof)
  | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "mul" p₁ p₂ proof₁ proof₂
    return (p₁ * p₂, proof)
  -- Ignore division for now
  -- | (``HDiv.hDiv, #[_, _, _, _, x, y]) => do
  -- Ignore mod fow now
  /-| (``HPow.hPow, #[_, _, _, _, b, exp]) =>
    -- We expect the power to be a `Nat`
    match exp.getAppFnArgs with
    | (``Nat.zero, #[]) => return Poly.one
    | (``Nat.succ, #[n]) =>
      match n.nat? with
      | none => mkVarAtom e
      | some n =>
        -- We won't expand the power, so whatever is inside better be an atom
        let (p, proof) ← mkVarAtom b
        return Monomial.scPow monomial (n + 1)
    | _ => mkVarAtom e -/
  | _ => mkVarAtom e


end /- mutual for `{asPoly, asPolyImpl}` -/

/-def rewrite (lhs rw : Expr) : MetaM (Option Expr) := do
  trace[gb] "rewriting {lhs} via {rw} : {← inferType rw}"
  match (← inferType rw).eq? with
  | some (_, lhs, rhs) => -/

--def processEquality () : MetaM Unit := do

-- Perhaps have a set of constraints based on the types of things?
-- e.g. `Nat` can't have negative values?

-- 将一个等式假设 `e`（类型为 `lhs = 0`）转换为多项式并存入状态。
-- 先用 `asPoly` 得到多项式及其证明，再将证明方向对称后调用 `addPoly`。
def addEquality (e lhs : Expr) : GBM F Unit := do
  let (poly, proof) ← asPoly lhs

  -- Reconstruct proof that `e` can be represented as a `Poly`
  let proof ← reconstructProof proof e

  trace[gb] "Adding poly for {e}"
  addPoly poly proof e

/-- Given a fact `e` with type `¬P`, return a more useful fact by pushing the negation. -/
-- 对类型为 `¬P` 的表达式 `e` 推入否定，将其转换为正向可用的命题：
-- - `¬¬P` → `P`；`¬(P ∧ Q)` → `¬P ∨ ¬Q`；
-- - `¬(P ∨ Q)` → `¬P ∧ ¬Q`；`¬(P ↔ Q)` → `(P ∧ ¬Q) ∨ (¬P ∧ Q)`。
def pushNot (e P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  trace[gb] s!"pushing negation: {P}"
  match P with
  | .forallE _ t b _ => return none
  | .app _ _ =>
    match_expr P with
    | Not P =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P
        (.app (.const ``Classical.propDecidable []) P) e)
    | And P Q =>
      return some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) e)
    | Or P Q =>
      return some (mkApp3 (.const ``and_not_not_of_not_or []) P Q e)
    | Iff P Q =>
      return some (mkApp5 (.const ``Decidable.and_not_or_not_and_of_not_iff []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) e)
    | _ => return none
  | _ => return none

mutual

-- 处理单条假设 `e`，将其分解并提取可用的多项式约束：
-- - `Int` 等式（`x = y`）：化为 `x - y = 0` 后调用 `addEquality`；
-- - 整除（`a ∣ b`）：替换为"存在 c 使 b = a*c"后递归；
-- - 合取（`P ∧ Q`）：拆分为两条假设分别处理；
-- - 存在量词/子类型：提取见证对象的属性后递归；
-- - 析取（`P ∨ Q`）：若配置允许则加入待处理析取列表；
-- - 其他：忽略。
partial def processFact (p : MetaProblem) (e : Expr) : GBM F MetaProblem := do
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "adding fact: {t}"
  match t with
  | .app _ _ =>
    match_expr t with
    | Eq α x y =>
      match_expr α with
      | Int =>
        match y.int? with
        | some 0 => addEquality e x; return p
        | _ => processFact p (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y e)
      | _ => return p
    /-  Replace `(a | b)` with `∃ c, b = a * c`  -/
    | Dvd.dvd α _ a b =>
      match_expr α with
      --| Int => processFact p (mkApp2 (.const ``Int.dvd_def []) s t)
      | Int => processFact p (mkApp3 (.const ``Int.exists_of_dvd []) a b e)
      | _ => return p
    /-  Split products into pieces and recurse on each  -/
    | And t₁ t₂ => do
      let p₁ ← processFact p (mkApp3 (.const ``And.left []) t₁ t₂ e)
      processFact p₁ (mkApp3 (.const ``And.right []) t₁ t₂ e)
    /-  Split existentials and recurse on their property  -/
    | Exists α P =>
      processFact p (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
    /-  Split subtypes and recurse on their property  -/
    | Subtype α P =>
      processFact p (mkApp3 (.const ``Subtype.property [← getLevel α]) α P e)
    | Or _ _ =>
      if (← cfg).splitDisjunctions then
        return { p with disjunctions := p.disjunctions.insert e}
      else
        return p
    | _ =>
      trace[gb] "Application has no matching rule: {t}"
      return p
  | _ =>
    trace[gb] "Expression has no matching rule: {t}"
    return p


end /- mutual for `{processFact}` -/

-- 依次处理 `MetaProblem` 中待处理的假设列表，跳过已处理的重复假设，
-- 直至列表为空，返回最终的 `GBState`（含所有收集到的多项式）。
partial def processFacts (p : MetaProblem) : GBM F (GBState F) := do
  match p.facts with
  | [] =>
    trace[gb] "processed {(← getThe (GBState F)).polys.size} polys"
    getThe (GBState F)
  | e :: es =>
    if p.processedFacts.contains e then
      processFacts { p with facts := es }
    else
      let p ← processFact (e := e) { p with
        facts := es
        processedFacts := p.processedFacts.insert e }
      processFacts p

-- 处理目标表达式 `e`，尝试提取"待证多项式 + 已知多项式组"的结构：
-- - `x = a * c`（其中 `c` 为待构造的存在量变量）：将 `a` 加入多项式组，返回 `(x, 所有多项式, 对应表达式)`；
-- - 整除 `a ∣ b`：展开为存在量化形式后递归；
-- - 存在量词：提取见证属性后递归；
-- - 其他：返回 `none`。
partial def processGoalFact (e : Expr) : GBM F (Option (P[F] × Array P[F] × Array Expr)) := do
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "adding goal fact: {t}"
  match t with
  | .forallE _ x fx _ =>
    trace[gb] "FORALLE {x}, {fx}"
    return none
    --processGoalFact fx
  | .lam _ x fx _ =>
    trace[gb] "LAM {x}, {fx}"
    processGoalFact fx
  | .app _ _ =>
    match_expr t with
    | Eq α x y =>
      match_expr α with
      | Int =>
        -- Assume the existential variable is on the RHS
        match y.getAppFnArgs with
        | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) =>
          -- Assume that `e₂` has the existential variable
          let (xpoly, xproof) ← asPoly x
          let (ypoly, yproof) ← asPoly e₁
          addPoly ypoly (← yproof) e
          return some (xpoly, ← getPolys, ← getPolyExprs)
        | _ => return none
      | _ => return none
    /-  Replace `(a | b)` with `∃ c, b = a * c`  -/
    | Dvd.dvd α _ a b =>
      match_expr α with
      --| Int => processFact p (mkApp2 (.const ``Int.dvd_def []) s t)
      | Int => processGoalFact (mkApp3 (.const ``Int.exists_of_dvd []) a b e)
      | _ => return none
    | Exists α P =>
      -- We extract the multiplier on the existentially quantified variable
      -- TODO: Rearrange LHS and RHS so the ∃ var is on the RHS and is a multiple(?)
      -- Fow now, assume correct sides
      trace[gb] "{P}"
      processGoalFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
      --return none
    | _ => return none
  | _ => return none

-- 对目标 `g` 进行预处理，将整除目标（`a ∣ b`）转换为存在量化目标（`∃ c, b = a * c`），
-- 并递归处理直到无法继续转换为止，返回最终待证目标的 `MVarId`。
partial def processGoal (g : MVarId) : MetaM MVarId := do
  let e ← whnfR (.mvar g)
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "processing goal mvarid {t}"
  match t with
  | .app _ _ =>
    match_expr t with
    | Dvd.dvd α _ s t =>
      match_expr α with
      | Int =>
        -- Apply `Int.exists_of_dvd`
        match ← g.apply (mkApp2 (.const ``Int.dvd_of_exists []) s t) with
        | [g] => processGoal g
        | _ =>
          trace[gb] "Apply failed!"
          return g
      | _ => return g
    | Exists α P => return g
      -- We extract the multiplier on the existentially quantified variable
      -- TODO: Rearrange LHS and RHS so the ∃ var is on the RHS and is a multiple(?)
      -- Fow now, assume correct sides
      --trace[gb] "{P}"
      --processGoalFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
    | _ => return g
  | _ => return g


-- 若 `a = 0`，则对任意 `b` 有 `b * a = 0`（用于构造证明时的辅助引理）。
theorem Int.mul_left_eq_zero_of_eq_zero {a : Int} : a = 0 → ∀ (b : Int), b * a = 0 := by
  rintro rfl b
  rw [Int.mul_zero]

-- 根据已处理目标 `g` 推断应使用的域类型（目前仅返回 `ℚ`）。
-- 若目标是关于 `Nat` 或 `Int` 的存在量词，返回有理数域 `ℚ`；否则尝试推断 `Field` 实例。
def inferFieldFromProcessedGoal (g : MVarId) : MetaM Q(Type) := do
  let e ← whnfR (.mvar g)
  let t ← instantiateMVars (← whnfR (← inferType e))
  match t with
  | .app _ _ =>
    match_expr t with
    | Exists α P =>
      match_expr α with
      | Nat => return q(ℚ)
      | Int => return q(ℚ)
      | _ =>
        -- Try to infer a field instance
        let inst ← synthInstance q(Field $α)
    | _ => return Int
  | _ => return Int



-- Assume `exprs` is an array of expressions of the form `a = 0`.
/-def constructProof (exprs : Array Expr) : PolyHistory → MetaM Expr
  | .zero => mkEqRefl (mkApp (.const ``Int.ofNat []) (.const ``Nat.zero []))
  | .basis i => return exprs.get! i
  | .scalarMul c h => do
    let proof ← constructProof exprs h
    match_expr proof with
    | Eq _ x _ =>
      return mkApp4 (.const ``Int.mul_left_eq_zero_of_eq_zero []) proof x proof (RattoExpr c)
    | _ => return exprs.get! 0
  | .termMul t h => do
    let proof ← constructProof exprs h
    return proof
    --mkEqRefl (mkApp3 (.const ``Int.mul []) (mkApp (.const ``Int.ofNat []) c) prf)
  | _ => return exprs.get! 0
-/
--def prfOf (h : PolyHistory F) (exprs : Array Expr) : Expr := exprs.get! 0

open Elab Tactic

-- 定义 `gb` 策略的语法（关键字 `gb`，无参数）。
syntax (name := gbSyn) "gb" : tactic


-- `gb` 策略的核心实现：
-- 1. 用 `processFacts` 将所有假设转换为多项式并收集到 `GBState`；
-- 2. 用 `processGoal` 将目标化简（如整除 → 存在量词）；
-- 3. 用 `processGoalFact` 提取目标多项式和生成元；
-- 4. 调用 `HPoly.idealMembership` 检验目标多项式是否属于生成元理想；
-- 5. 若成功，则存在线性组合见证（目前仅 trace，尚未构造 Lean 证明项）。
def gbImpl (facts : List Expr) (g : MVarId) : MetaM Unit := do
  trace[gb] "facts: {facts}"
  let st ← GBM.run (processFacts { facts }) (cfg := {})
  trace[gb] "---------------"
  let g ← processGoal g
  let goalExpr ← whnfR (.mvar g)
  match ← GBM.run (@processGoalFact goalExpr) st {} with
  | none => throwError "Goal is not a valid modular arithmetic goal."
    --trace[gb] "Goal is not a valid modular arithmetic goal."
    --return ()
  | some (poly, polys, exprs) => do
    trace[gb] "derived polys: {polys}"
    trace[gb] "derived goal poly: {poly}"
    trace[gb] "derived exprs: {exprs}"
    match HPoly.idealMembership poly polys with
    | none => throwError "Groebner basis membership test failed."
      --trace[gb] "Groebner basis membership test failed."
    | some w =>
      trace[gb] "{w}"
      return ()

-- `gb` 策略的策略层入口：收集当前上下文中所有局部假设，
-- 并调用 `gbImpl` 尝试以 Gröbner 基方法完成目标证明。
def gbTactic : TacticM Unit := do
  --liftMetaTactic fun g => do
  liftMetaFinishingTactic fun g => do
    g.withContext do
      let hyps := (← getLocalHyps).toList
      trace[gb] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
      let _ ← gbImpl hyps g
      return ()

-- 将 `gbSyn` 语法节点绑定到 `gbTactic` 实现（内置策略注册）。
@[builtin_tactic HDP.gbSyn]
def evalGB : Tactic := fun
  | `(tactic| gb) => do
    gbTactic
  | _ => throwUnsupportedSyntax

-- 通过 `elab` 也注册一次 `gb` 关键字（两种注册方式均可触发 `gbTactic`）。
elab "gb" : tactic => gbTactic
-- CC: Place in different file?

set_option trace.omega true
set_option trace.gb true

-- 测试用例：验证 `omega` 可以处理整数传递序关系。
theorem omegaTest : ∀ (a b c : ℤ), a < b → b < c → a < c := by
  omega
  done

-- 测试用例：验证 `gb` 策略可以自动证明整除的传递性（a ∣ b → b ∣ c → a ∣ c）。
theorem test : ∀ (a b c : ℤ), a ∣ b → b ∣ c → a ∣ c := by
  intro a b c ha hb
  gb
  done
