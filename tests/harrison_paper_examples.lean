import HDP.Tactic

set_option trace.hdp true

namespace HarrisonPaperExamples

abbrev coprime (a b : Int) : Prop :=
  ∃ u v : Int, a * u + b * v = 1


/-! 1. Basic examples -/

/-- `a*x ≡ a*y (mod n) ∧ coprime(a,n) → x ≡ y (mod n)`. -/
theorem congruence_cancel_coprime
    (a n x y : Int) :
    (a * y) % n = (a * x) % n →
    coprime a n →
    y % n = x % n := by
  hdp

/-- `d | a ∧ d | b → d | (a - b)`. -/
theorem dvd_sub
    (d a b : Int) :
    d ∣ a → d ∣ b → d ∣ (a - b) := by
  hdp

/-- `a | b → c*a | c*b`. -/
theorem dvd_mul_left
    (a b c : Int) :
    a ∣ b → (c * a) ∣ (c * b) := by
  hdp

/-- Transitivity of divisibility. -/
theorem dvd_trans
    (x y z : Int) :
    x ∣ y → y ∣ z → x ∣ z := by
  hdp

/-- `(x*d) | a → d | a`. -/
theorem dvd_of_mul_dvd
    (x d a : Int) :
    (x * d) ∣ a → d ∣ a := by
  hdp

/-- `a | b ∧ c | d → a*c | b*d`. -/
theorem dvd_mul_mul
    (a b c d : Int) :
    a ∣ b → c ∣ d → (a * c) ∣ (b * d) := by
  hdp

/-- `coprime(d, a) ∧ coprime(d, b) → coprime(d, a*b)`. -/
theorem coprime_mul_right
    (d a b : Int) :
    coprime d a → coprime d b → coprime d (a * b) := by
  hdp

/-- `coprime(d, a*b) → coprime(d, a)`. -/
theorem coprime_of_coprime_mul_right
    (d a b : Int) :
    coprime d (a * b) → coprime d a := by
  hdp

/-- `m | r ∧ n | r ∧ coprime(m,n) → m*n | r`. -/
theorem dvd_mul_of_coprime_dvd
    (m n r : Int) :
    m ∣ r → n ∣ r → coprime m n → (m * n) ∣ r := by
  hdp

/-- Congruence compatible with multiplication. -/
theorem modeq_mul
    (x x' y y' n : Int) :
    x' % n = x % n → y' % n = y % n →
    (x' * y') % n = (x * y) % n := by
  hdp

/-- If `x ≡ y (mod m)` and `n | m`, then `x ≡ y (mod n)`. -/
theorem modeq_of_dvd_modulus
    (x y m n : Int) :
    y % m = x % m → n ∣ m → y % n = x % n := by
  hdp

/-- `coprime(a, b) ∧ x ≡ y (mod a) ∧ x ≡ y (mod b) ⇒ x ≡ y (mod a*b)` -/
theorem modeq_mul_modulus_of_coprime
    (a b x y : Int) :
    coprime a b →
    y % a = x % a →
    y % b = x % b →
    y % (a * b) = x % (a * b) := by
  hdp

/-- `x^2 ≡ y^2 (mod x + y)` -/
theorem square_modeq_sum
    (x y : Int) :
    y^2 % (x + y) = x^2 % (x + y) := by
  hdp

/-- If `x^2 ≡ a` and `y^2 ≡ a` modulo `n`, then `n | (x+y)(x-y)`. -/
theorem square_modeq_dvd_difference
    (x y a n : Int) :
    a % n = x^2 % n →
    a % n = y^2 % n →
    n ∣ ((x + y) * (x - y)) := by
  hdp


/-! 2. Examples involving `↔` -/

/-- `x ≡ y (mod n) → (coprime(n,x) ↔ coprime(n,y))`. -/
theorem modeq_coprime_iff
    (x y n : Int) :
    y % n = x % n →
    (coprime n x ↔ coprime n y) := by
  hdp

/-- `x ≡ 0 (mod n) ↔ n | x`. -/
theorem modeq_zero_iff_dvd
    (x n : Int) :
    0 % n = x % n ↔ n ∣ x := by
  hdp

/-- `x+a ≡ y+a (mod n) ↔ x ≡ y (mod n)`. -/
theorem modeq_add_cancel_iff
    (x y a n : Int) :
    (y + a) % n = (x + a) % n ↔ y % n = x % n := by
  hdp

/-- `coprime(x*y, x^2+y^2) ↔ coprime(x,y)`. -/
theorem coprime_mul_square_sum_iff
    (x y : Int) :
    coprime (x * y) (x * x + y * y) ↔ coprime x y := by
  hdp


/-! 3. Examples involving Negated equation -/

/-- `c ≠ 0 → ((c*a) | (c*b) ↔ a | b)`. -/
theorem dvd_mul_cancel_nonzero
    (a b c : Int) :
    c ≠ 0 → ((c * a) ∣ (c * b) ↔ a ∣ b) := by
  hdp


/-! 4. Existentials in original conclusion -/

/-- If `a` and `n` are coprime, then `a*x ≡ b (mod n)` is solvable. -/
theorem linear_congruence_solvable_coprime
    (a n b : Int) :
    coprime a n → ∃ x : Int, b % n = (a * x) % n := by
  hdp

/-- Binary Chinese Remainder Theorem. -/
theorem binary_crt
    (a b u v : Int) :
    coprime a b →
    ∃ x : Int, u % a = x % a ∧ v % b = x % b := by
  hdp

/-- Ternary Chinese Remainder Theorem. -/
theorem ternary_crt
    (a b c u v w : Int) :
    coprime a b → coprime a c → coprime b c →
    ∃ x : Int, u % a = x % a ∧ v % b = x % b ∧ w % c = x % c := by
  hdp


/-! 5. GCD extension examples -/

/-- GCD condition for solvability of a linear congruence. -/
theorem gcd_dvd_imp_linear_congruence_solvable
    (a n b : Int) :
    (Int.gcd a n : Int) ∣ b → ∃ x : Int, b % n = (a * x) % n := by
  hdp

/-- Converse of the preceding GCD solvability condition. -/
theorem linear_congruence_solvable_imp_gcd_dvd
    (a n b : Int) :
    (∃ x : Int, b % n = (a * x) % n) → (Int.gcd a n : Int) ∣ b := by
  hdp

/-- If `gcd(a,b) ≠ 0`, divide out the gcd and obtain coprime quotients. -/
theorem divide_by_gcd_coprime_quotients
    (a b : Int) :
    Int.gcd a b ≠ 0 →
    ∃ a' b' : Int,
      a = a' * Int.gcd a b ∧
      b = b' * Int.gcd a b ∧
      coprime a' b' := by
  hdp

/-- Generalized binary CRT using `gcd(n1,n2)` rather than assuming coprimality. -/
theorem binary_crt_gcd
    (a1 a2 n1 n2 : Int) :
    a2 % (Int.gcd n1 n2) = a1 % (Int.gcd n1 n2) →
    ∃ x : Int, a1 % n1 = x % n1 ∧ a2 % n2 = x % n2 := by
  hdp


/-! Incompleteness examples: should not pass for this algorithm -/

theorem incomplete_even_quadratic_1 (x : Int) :
    ∃ a : Int, x * x + x = 2 * a := by
  hdp

theorem incomplete_even_quadratic_2 (x y : Int) :
    y = 1 → ∃ a : Int, x * x + x = (y + 1) * a := by
  hdp

theorem incomplete_even_quadratic_3 (x y : Int) :
    ∃ a b : Int, x * x + x = (y + 1) * a + (y - 1) * b := by
  hdp

end HarrisonPaperExamples
