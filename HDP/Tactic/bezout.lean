import Init.Data.Int.Gcd

private theorem nat_bezout_gcd (m n : Nat) :
    ∃ u v : Int, (m : Int) * u + (n : Int) * v = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _ ih =>
      rcases ih with ⟨u, v, h⟩
      refine ⟨v - (n / m : Nat) * u, u, ?_⟩
      rw [Nat.gcd_rec, ← h, Int.natCast_emod, Int.emod_def, Int.natCast_ediv,
        Int.mul_sub, Int.sub_mul, ← Int.mul_assoc]
      omega

theorem bezout_gcd (m n : Int) :
    ∃ u v, m * u + n * v = (Int.gcd m n : Int) := by
  rcases nat_bezout_gcd m.natAbs n.natAbs with ⟨u, v, h⟩
  refine ⟨m.sign * u, n.sign * v, ?_⟩
  simpa [← Int.mul_assoc, Int.gcd_eq_natAbs_gcd_natAbs] using h
