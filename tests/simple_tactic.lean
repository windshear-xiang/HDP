import HDP.Tactic

example (a b : Int) (h : b = a * 2) : ∃ e, a * e = b := by
  hdp

example (a b c : Int) (h1 : b = a * 3) (h2 : c = b * 5) : ∃ e, a * e = c := by
  hdp

example (x y : Int) (h : y = x * x + x) : ∃ e, x * e = y := by
  hdp

example (a b : Int) (h : a*3 = b) : ∃ e, a * e = b * 3 := by
  hdp

example (a b : Int) (h : b = -a) : ∃ e, a * e = b := by
  hdp

example (a b c : Int) (h₁ : b = a * 3) (h₂ : c = b * 5) : a ∣ c := by
  hdp

example (a b c : Int) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  hdp
