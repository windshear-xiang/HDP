import HDP.Poly.Poly
-- import AutoGB.Upstream.Batteries.Array

namespace HDP.Poly

open Lean.Grind

-- Move these somewhere else later

namespace List

-- CC: TODO these classes can be made more general
-- 将 foldl 乘法的初始值提取到外面：l.foldl (· * f ·) init = init * l.foldl (· * f ·) 1
theorem foldl_mul {R : Type u} [CommSemiring R] (f : β → R) (l : List β) (init : R)
    : l.foldl (· * f ·) init = init * l.foldl (· * f ·) 1 := by
  induction l generalizing init with
  | nil => simp; grind
  | cons r rs ih =>
    simp [ih (init * f r), ih (f r)]
    sorry

-- 将 foldl 加法的初始值提取到外面：l.foldl (· + f ·) init = init + l.foldl (· + f ·) 0
theorem foldl_add {R : Type u} [CommSemiring R] (f : β → R) (l : List β) (init : R)
    : l.foldl (· + f ·) init = init + l.foldl (· + f ·) 0 := by
  induction l generalizing init with
  | nil => simp; grind
  | cons r rs ih =>
    simp [ih (init + f r), ih (f r)]
    sorry

end List

namespace Monomial

variable {R : Type u} [CommRing R]

-- 将单项式 m 在给定原子（变量取值）数组上求值：对每个变量取对应幂次再连乘
protected def eval (m : Monomial) (atoms : Array R) : R :=
  Array.zipWith (· ^ ·) atoms m
    |>.foldl (· * ·) 1

-- `eval_asList`
-- eval 的 List 版本，用于归纳证明
def eval' (m : List Nat) (atoms : List R) :=
  List.zipWith (· ^ ·) atoms m
    |>.foldl (· * ·) 1

-- Array 版 eval 与 List 版 eval' 的一致性
@[simp]
protected theorem eval_eq_eval' (m : Monomial) (atoms : Array R)
    : m.eval atoms = eval' m.toList atoms.toList := by
  have ⟨atoms⟩ := atoms
  have ⟨m⟩ := m
  simp [Monomial.eval, eval']

-- 零单项式（所有指数为 0）的求值结果为乘法单位元 1
@[simp]
theorem eval_zero (atoms : Array R) : Monomial.eval 0 atoms = 1 := by
  have ⟨atoms⟩ := atoms
  simp [eval']

-- 空指数列表对任意原子列表的求值为 1
@[simp]
theorem eval'_nil_left (atoms : List R) : eval' [] atoms = 1 := by
  simp [eval']

-- 任意指数列表对空原子列表的求值为 1
@[simp]
theorem eval'_nil_right (m : List Nat) : eval' m ([] : List R) = 1 := by
  simp [eval']

-- eval' 的递推展开：首项分离，a^e 乘以剩余部分的求值
@[simp]
theorem eval'_cons_cons (a : R) (as : List R) (e : Nat) (m : List Nat)
    : eval' (e :: m) (a :: as) = a ^ e * eval' m as := by
  simp [eval']
  rw [List.foldl_mul]
  sorry


-- eᵢ 0（第 0 个标准基）在以 a 为首的原子列表上求值等于 a
@[simp]
theorem eval_eᵢ_succ_zero (a : R) (atoms : List R)
    : Monomial.eval (Monomial.eᵢ 0) { toList := (a :: atoms) } = a := by
  simp [eval']
  sorry

-- eᵢ (i+1) 在以 a 为首的原子列表上求值，等于 eᵢ i 在尾部列表上的求值（忽略首个变量）
@[simp]
theorem eval_eᵢ_succ_cons (a : R) (atoms : List R) (i : Nat)
    : Monomial.eval (Monomial.eᵢ (i + 1)) { toList := (a :: atoms) }
        = Monomial.eval (Monomial.eᵢ i) { toList := atoms } := by
  simp [eval']
  sorry

-- eᵢ i 在原子数组上的求值等于 atoms[i]，若下标越界则为 1
@[simp]
theorem eval_eᵢ (atoms : Array R) (i : Nat)
    : Monomial.eval (Monomial.eᵢ i) atoms = atoms[i]?.getD 1 := by
  stop
  simp
  have ⟨atoms⟩ := atoms
  induction atoms generalizing i with
  | nil => simp [eval']
  | cons a as ih =>
    match i with
    | 0 => simp [eval']
    | i + 1 => simp [ih]

-- 单项式乘法与求值的兼容性：(m₁ * m₂) 的求值等于各自求值之积
@[simp]
theorem eval_mul (m₁ m₂ : Monomial) (atoms : Array R)
    : Monomial.eval (m₁ * m₂) atoms = m₁.eval atoms * m₂.eval atoms := by
  stop
  have ⟨atoms⟩ := atoms
  have ⟨m₁⟩ := m₁
  have ⟨m₂⟩ := m₂
  simp only [Monomial.eval_eq_eval']
  induction atoms generalizing m₁ m₂ with
  | nil => simp only [eval'_nil_right, mul_one]
  | cons a as ih =>
    match m₁ with
    | .nil => simp only [nil_eq_zero, Monomial.zero_mul, eval'_nil_left, one_mul]
    | .cons e₁ es₁ =>
      match m₂ with
      | .nil => simp
      | .cons e₂ es₂ =>
        simp [ih]
        simp only [← mul_assoc]
        rw [mul_assoc (a ^ e₁), mul_comm _ (a ^ e₂), ← mul_assoc, pow_add]

end Monomial

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

-- 若两个单项式项有相同的单项式部分，则它们的和等于系数相加、单项式不变的项
theorem add_of_eq {t₁ t₂ : M[F]} (h : t₁.monomial = t₂.monomial)
    : t₁ + t₂ = { coeff := t₁.coeff + t₂.coeff, monomial := t₁.monomial } := by
  simp only [HAdd.hAdd, Add.add, MTerm.add, h, ↓reduceIte]

-- 若两个单项式项有相同的单项式部分，则它们的差等于系数相减、单项式不变的项
theorem sub_of_eq {t₁ t₂ : M[F]} (h : t₁.monomial = t₂.monomial)
    : t₁ - t₂ = { coeff := t₁.coeff - t₂.coeff, monomial := t₁.monomial } := by
  simp only [HSub.hSub, Sub.sub, MTerm.sub, h, ↓reduceIte]

--------------------------------------------------------------------------------

-- 将单项式项（系数 × 单项式）在给定原子数组上求值
protected def eval (t : M[F]) (atoms : Array F) : F :=
  t.coeff * t.monomial.eval atoms

-- eval 的 List 版本：系数乘以 Monomial.eval' 的结果
def eval' (c : F) (m : List Nat) (atoms : List F) : F :=
  c * Monomial.eval' m atoms

-- Array 版 MTerm.eval 与 List 版 eval' 的一致性
@[simp]
protected theorem eval_eq_eval' (t : M[F]) (atoms : Array F)
    : t.eval atoms = eval' t.coeff t.monomial.toList atoms.toList := by
  simp [MTerm.eval, eval']

-- 空指数列表时 eval' 直接返回系数
@[simp]
protected theorem eval'_nil_left (c : F) (atoms : List F) : eval' c [] atoms = c := by
  stop
  simp [eval']

-- 空原子列表时 eval' 直接返回系数
@[simp]
protected theorem eval'_nil_right (c : F) (m : List Nat) : eval' c m [] = c := by
  stop
  simp [eval']

end MTerm

namespace Poly

variable {F : Type v} [Field F] [DecidableEq F]

-- TODO: Move these to Poly

-- 零多项式转换为 List 得到空列表
@[simp] theorem toList_zero : Array.toList (0 : P[F]) = [] := rfl

-- 零多项式等于空 Array
theorem zero_eq_nil : (0 : P[F]) = #[] := rfl
-- 空 Array 等于零多项式
@[simp] theorem nil_eq_zero : #[] = (0 : P[F]) := rfl

-- 零多项式的项数为 0
@[simp] theorem size_zero : size (0 : P[F]) = 0 := rfl
-- 内部表示为空列表的多项式项数为 0
@[simp] theorem size_zero' : size ({ toList := [] } : P[F]) = 0 := rfl

-- cons 构造的多项式项数等于尾部项数加 1
@[simp] theorem size_cons (t : M[F]) (ts : List M[F])
    : size ({ toList := t :: ts } : P[F]) = size ({ toList := ts }) + 1 := rfl

-- 多项式加零等于自身（右单位元）
@[simp]
protected theorem add_zero (p : P[F]) : p + 0 = p := by
  have ⟨p⟩ := p
  simp only [HAdd.hAdd, Add.add, Poly.add]
  rw [add.loop]
  simp
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp
    sorry
    done

-- 零加多项式等于自身（左单位元）
@[simp]
protected theorem zero_add (p : P[F]) : 0 + p = p := by
  have ⟨p⟩ := p
  simp only [HAdd.hAdd, Add.add, Poly.add]
  rw [add.loop]
  simp
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp
    sorry
    done

--instance instCommSemiring : CommSemiring P[F] := by sorry

-- 将多项式 p 在给定原子数组上求值：对每一项调用 MTerm.eval 后求和
protected def eval (p : P[F]) (atoms : Array F) : F :=
  p.foldl (init := (0 : F)) (fun acc t => acc + (t.eval atoms))

-- eval 的 List 版本：对 (系数, 指数列表) 对的列表逐项调用 MTerm.eval' 后求和
protected def eval' (p : List (F × List Nat)) (atoms : List F) : F :=
  p.foldl (init := (0 : F)) (fun acc ⟨c, m⟩ => acc + (MTerm.eval' c m atoms))

-- Array 版 Poly.eval 与 List 版 eval' 的一致性：
-- 将多项式的每一项展开为 (系数, 指数列表) 对后，两者结果相同
@[simp]
protected theorem eval_eq_eval' (p : P[F]) (atoms : Array F)
    : p.eval atoms
        = Poly.eval' ((p.toList).map (fun t => (t.coeff, t.monomial.toList))) atoms.toList := by
  stop
  have ⟨p⟩ := p
  have ⟨atoms⟩ := atoms
  simp [Poly.eval, Poly.eval']
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, zero_add, List.map_cons]
    rw [List.foldl_add, ih]
    conv => rhs; rw [List.foldl_add]

-- 空多项式对任意原子列表的求值为 0
@[simp] theorem eval'_nil_left (atoms : List F) : Poly.eval' [] atoms = 0 := rfl

-- 单项式多项式 #[eᵢ i] 的求值等于 atoms[i]（默认值为 1）
@[simp]
theorem eval_eᵢ (i : Nat) (atoms : Array F)
    : Poly.eval #[Monomial.eᵢ i] atoms = atoms.getD i 1 := by
  stop
  simp [Poly.eval', MTerm.eval']
  rw [← Monomial.eval_eq_eval']
  exact Monomial.eval_eᵢ atoms i

-- 多项式加法与求值的兼容性：(p₁ + p₂) 的求值等于各自求值之和
@[simp]
theorem eval_add (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ + p₂).eval atoms = p₁.eval atoms + p₂.eval atoms := by
  stop
  have ⟨p₁⟩ := p₁
  have ⟨p₂⟩ := p₂
  have ⟨atoms⟩ := atoms
  simp [Poly.eval']
  induction p₁ generalizing p₂ with
  | nil => simp
  | cons t ts ih =>
    simp
    conv => rhs; rw [List.foldl_add]
    stop
    done
  done

-- 多项式减法与求值的兼容性：(p₁ - p₂) 的求值等于各自求值之差
@[simp]
theorem eval_sub (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ - p₂).eval atoms = p₁.eval atoms - p₂.eval atoms := by
  stop
  done

-- 多项式取负与求值的兼容性：(-p) 的求值等于求值结果取负
@[simp]
theorem eval_neg (p : P[F]) (atoms : Array F)
    : (-p).eval atoms = -(p.eval atoms) := by
  sorry
  done

-- 单项式项左乘多项式与求值的兼容性：(t * p) 的求值等于 t 的求值乘以 p 的求值
@[simp]
theorem eval_tmul (t : M[F]) (p : P[F]) (atoms : Array F)
    : (t * p).eval atoms = t.eval atoms * p.eval atoms := by
  stop
  done

-- 多项式乘法与求值的兼容性：(p₁ * p₂) 的求值等于各自求值之积
@[simp]
theorem eval_mul (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ * p₂).eval atoms = p₁.eval atoms * p₂.eval atoms := by
  stop
  done

end Poly
