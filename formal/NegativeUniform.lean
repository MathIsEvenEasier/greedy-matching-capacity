import UniformCappedLaw

/-! Deliberately false: uniform assignments do not give uniform load
vectors. With two independent choices of two bins, (1,1) has twice
the probability of (2,0). This checks the actual categoricalLoadMass. -/
set_option autoImplicit false
namespace MatchingCapacity

theorem invalid_uniform_load_vectors :
    categoricalLoadMass (uniformRows (ι := Fin 2) 2) ![2, 0] =
      categoricalLoadMass (uniformRows (ι := Fin 2) 2) ![1, 1] := by
  unfold uniformRows
  rw [constantRowLoadMass_factorial _ _ (by decide),
    constantRowLoadMass_factorial _ _ (by decide)]
  norm_num [factorialWeight, Fin.prod_univ_succ]

end MatchingCapacity
