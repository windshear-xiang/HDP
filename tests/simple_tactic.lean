import HDP.Tactic

example (a b : Int) (h : b = a * 2) : ∃ e, b = a * e  := by
  hdp

example (a b c : Int) (h1 : b = a * 3) (h2 : c = b * 5) : ∃ e, c = a * e := by
  hdp

example (x y : Int) (h : y = x * x + x) : ∃ e, y = x * e := by
  hdp

example (a b : Int) (h : a*3 = b) : ∃ e, b * 3 = a * e := by
  hdp

example (a b c : Int) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  hdp

example (a b c : Int) (h₁ : b = a * a) (h₂ : c = a * a * a) : b ∣ c := by
  hdp

example (a n x y : Int)
    (h_cong : ∃ d : Int, a * y - a * x = n * d)
    (h_coprime : ∃ u v : Int, a * u + n * v = 1) :
    ∃ e : Int, y - x = n * e := by
  hdp
