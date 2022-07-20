import data.polynomial

@[mono]
lemma monotone_polynomial_nat (p : polynomial ℕ) : monotone (λ n : ℕ, p.eval n) :=
begin
  induction p using polynomial.induction_on' with p q h₀ h₁ n a,
  { simp, apply monotone.add; assumption, },
  simp, apply monotone.const_mul _ (zero_le a),
  { intros x y hxy, apply pow_le_pow_of_le_left (zero_le x) hxy, }, 
end
