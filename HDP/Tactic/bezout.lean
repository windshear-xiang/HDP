import Init.Data.Int.Gcd

private theorem bezout_step (m q r u v : Int) :
    m * (v - q * u) + (r + m * q) * u = r * u + m * v := by
  calc
    m * (v - q * u) + (r + m * q) * u
        = (m * v - m * (q * u)) + (r * u + (m * q) * u) := by
            rw [Int.mul_sub, Int.add_mul]
    _   = (m * v - (m * q) * u) + (r * u + (m * q) * u) := by
            rw [← Int.mul_assoc m q u]
    _   = r * u + m * v := by
            omega

private theorem nat_bezout_gcd (m n : Nat) :
    ∃ u v : Int, (m : Int) * u + (n : Int) * v = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n =>
      exact ⟨0, 1, by simp⟩
  | H1 m n _hm ih =>
      rcases ih with ⟨u, v, h⟩
      refine ⟨v - ((n / m : Nat) : Int) * u, u, ?_⟩
      rw [Nat.gcd_rec m n]
      rw [← h]
      have hdiv :
          (((n % m : Nat) : Int)
            + (m : Int) * ((n / m : Nat) : Int) = (n : Int)) := by
        have h0 := congrArg (fun t : Nat => (t : Int)) (Nat.mod_add_div n m)
        simpa using h0
      rw [← hdiv]
      exact bezout_step
        (m := (m : Int))
        (q := ((n / m : Nat) : Int))
        (r := ((n % m : Nat) : Int))
        (u := u) (v := v)

theorem bezout_gcd (m n : Int) :
    ∃ u v, m * u + n * v = (Int.gcd m n : Int) := by
  rcases nat_bezout_gcd m.natAbs n.natAbs with ⟨u, v, h⟩
  cases m with
  | ofNat m =>
      cases n with
      | ofNat n =>
          refine ⟨u, v, ?_⟩
          simpa [Int.gcd_eq_natAbs_gcd_natAbs] using h
      | negSucc n =>
          refine ⟨u, -v, ?_⟩
          rw [← Int.neg_ofNat_succ n]
          simpa [Int.gcd_eq_natAbs_gcd_natAbs, Int.neg_mul_neg] using h
  | negSucc m =>
      cases n with
      | ofNat n =>
          refine ⟨-u, v, ?_⟩
          rw [← Int.neg_ofNat_succ m]
          simpa [Int.gcd_eq_natAbs_gcd_natAbs, Int.neg_mul_neg] using h
      | negSucc n =>
          refine ⟨-u, -v, ?_⟩
          rw [← Int.neg_ofNat_succ m, ← Int.neg_ofNat_succ n]
          simpa [Int.gcd_eq_natAbs_gcd_natAbs, Int.neg_mul_neg] using h
