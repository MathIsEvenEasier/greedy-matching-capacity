import CarrierEfron

/-! Exact finite product-law moments and Efron monotonicity in arbitrary
dimension. The raw moment is the product-weight sum over nonnegative
integer lists having the given total. Zero-mass fibers are handled explicitly. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def CoordLE : List ℕ → List ℕ → Prop
  | [], [] => True
  | x :: xs, y :: ys => x ≤ y ∧ CoordLE xs ys
  | _, _ => False

def CoordinateIncreasing (φ : List ℕ → ℚ) : Prop :=
  ∀ xs ys, CoordLE xs ys → φ xs ≤ φ ys

theorem coordLE_refl (xs : List ℕ) : CoordLE xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨le_rfl, ih⟩

def productMoment : List FiniteCarrier → ℕ → (List ℕ → ℚ) → ℚ
  | [], s, φ => if s = 0 then φ [] else 0
  | a :: cs, s, φ => ∑ i ∈ Finset.range (s+1),
      a.weight i * productMoment cs (s-i) (fun xs => φ (i :: xs))

def productMean (cs : List FiniteCarrier) (s : ℕ) (φ : List ℕ → ℚ) : ℚ :=
  productMoment cs s φ / (carrierProduct cs).weight s

theorem productMoment_mono (cs : List FiniteCarrier) (s : ℕ) (φ ψ : List ℕ → ℚ)
    (h : ∀ xs, φ xs ≤ ψ xs) : productMoment cs s φ ≤ productMoment cs s ψ := by
  induction cs generalizing s φ ψ with
  | nil => simp only [productMoment]; split <;> simp_all
  | cons a cs ih =>
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (ih (s-i) _ _ (fun xs => h (i :: xs))) (a.nonneg i)

theorem productMean_mono_function (cs : List FiniteCarrier) (s : ℕ) (φ ψ : List ℕ → ℚ)
    (h : ∀ xs, φ xs ≤ ψ xs) : productMean cs s φ ≤ productMean cs s ψ := by
  exact div_le_div_of_nonneg_right (productMoment_mono cs s φ ψ h) ((carrierProduct cs).nonneg s)

theorem productMoment_zero_large (cs : List FiniteCarrier) (s : ℕ)
    (φ : List ℕ → ℚ) (hs : totalCap cs < s) : productMoment cs s φ = 0 := by
  induction cs generalizing s φ with
  | nil => simp only [totalCap, List.map_nil, List.sum_nil] at hs; simp [productMoment, Nat.ne_of_gt hs]
  | cons a cs ih =>
    change a.cap + totalCap cs < s at hs
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ≤ a.cap
    · rw [ih (s-i) (fun xs => φ (i :: xs)) (by omega), mul_zero]
    · rw [a.zero_outside i (by omega), zero_mul]

theorem productMoment_one (cs : List FiniteCarrier) (s : ℕ) :
    productMoment cs s (fun _ => 1) = (carrierProduct cs).weight s := by
  induction cs generalizing s with
  | nil =>
    by_cases hs : s = 0
    · subst s; norm_num [productMoment, carrierProduct, factorialCarrier, integerCarrier, cappedCarrier, factorialWeight]
    · simp [productMoment, carrierProduct, factorialCarrier, integerCarrier, cappedCarrier, hs]
  | cons a cs ih =>
    change (∑ i ∈ Finset.range (s+1), a.weight i * productMoment cs (s-i) (fun _ => 1)) =
      finiteConv a.cap a.weight (carrierProduct cs).weight s
    rw [conv_eq_layer a (carrierProduct cs) s]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : ((s-i : ℕ) : ℤ) = (s : ℤ)-i := by omega
    rw [ih, he]
    rfl

theorem productMean_split (a : FiniteCarrier) (cs : List FiniteCarrier) (s : ℕ)
    (φ : List ℕ → ℚ) (hs : s ≤ totalCap (a :: cs)) :
    productMean (a :: cs) s φ =
      twoExpectation a.weight (carrierProduct cs).weight s
        (fun i t => productMean cs t (fun xs => φ (i :: xs))) := by
  change s ≤ a.cap + totalCap cs at hs
  let b := carrierProduct cs
  have hZ : 0 < cumMass (sumLayer a.weight b.weight s) (s+1) :=
    carrier_layer_mass_pos a b s (by simpa only [b, carrierProduct_cap] using hs)
  change (∑ i ∈ Finset.range (s+1), a.weight i * productMoment cs (s-i) (fun xs => φ (i :: xs))) /
      finiteConv a.cap a.weight b.weight s = _
  rw [conv_eq_layer a b s, Finset.sum_div]
  unfold twoExpectation
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have he : ((s-i : ℕ) : ℤ) = (s : ℤ)-i := by omega
  by_cases ht : s-i ≤ totalCap cs
  · have hb : 0 < b.weight ((s : ℤ)-i) := (b.positive_iff _).mpr (by
      dsimp [b]; rw [carrierProduct_cap]; omega)
    simp only [normalized, sumLayer, productMean, he]
    change a.weight i * productMoment cs (s-i) (fun xs => φ (i :: xs)) / _ =
      (a.weight i * b.weight ((s : ℤ)-i) / _) *
        (productMoment cs (s-i) (fun xs => φ (i :: xs)) / b.weight ((s : ℤ)-i))
    dsimp only [b] at hZ hb ⊢
    field_simp [ne_of_gt hZ, ne_of_gt hb]
  · have hm := productMoment_zero_large cs (s-i) (fun xs => φ (i :: xs)) (by omega)
    simp only [normalized, sumLayer, productMean, he, hm, mul_zero, zero_div]

theorem productMean_split_clamped (a : FiniteCarrier) (cs : List FiniteCarrier) (s : ℕ)
    (φ : List ℕ → ℚ) (hs : s ≤ totalCap (a :: cs)) :
    productMean (a :: cs) s φ =
      twoExpectation a.weight (carrierProduct cs).weight s
        (fun i t => productMean cs (min t (totalCap cs)) (fun xs => φ (i :: xs))) := by
  rw [productMean_split a cs s φ hs]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases ht : s-i ≤ totalCap cs
  · simp only [Nat.min_eq_left ht]
  · have hz : (carrierProduct cs).weight ((s : ℤ)-i) = 0 :=
      (carrierProduct cs).zero_outside _ (by rw [carrierProduct_cap]; omega)
    simp [normalized, sumLayer, hz]

theorem product_efron_monotone (cs : List FiniteCarrier) (s t : ℕ)
    (hst : s ≤ t) (ht : t ≤ totalCap cs) (φ : List ℕ → ℚ)
    (hφ : CoordinateIncreasing φ) : productMean cs s φ ≤ productMean cs t φ := by
  induction cs generalizing s t φ with
  | nil => have he : s = t := by simp only [totalCap, List.map_nil, List.sum_nil] at ht; omega
           rw [he]
  | cons a cs ih =>
    change t ≤ a.cap + totalCap cs at ht
    rw [productMean_split_clamped a cs s φ (hst.trans ht), productMean_split_clamped a cs t φ ht]
    apply carrier_efron_monotone a (carrierProduct cs) s t hst
      (by simpa only [carrierProduct_cap] using ht)
    intro i j k l hik hjl
    apply le_trans (productMean_mono_function cs (min j (totalCap cs)) _ _ (by
      intro xs
      exact hφ (i :: xs) (k :: xs) ⟨hik, coordLE_refl xs⟩))
    apply ih (min j (totalCap cs)) (min l (totalCap cs))
      (min_le_min hjl le_rfl) (min_le_right _ _)
    intro xs ys hxy
    exact hφ (k :: xs) (k :: ys) ⟨le_rfl, hxy⟩

theorem capped_product_efron (qs : List ℕ) (s t : ℕ) (hst : s ≤ t) (ht : t ≤ qs.sum)
    (φ : List ℕ → ℚ) (hφ : CoordinateIncreasing φ) :
    productMean (qs.map factorialCarrier) s φ ≤ productMean (qs.map factorialCarrier) t φ := by
  apply product_efron_monotone _ s t hst _ φ hφ
  simpa only [totalCap_factorial] using ht

end MatchingCapacity
