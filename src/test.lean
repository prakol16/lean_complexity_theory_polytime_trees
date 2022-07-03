import polycodable
import data.set.basic
import data.bool.basic

variables {α β : Type*} [polycodable α] [polycodable β]
open polycodable (encode)

example : polydecidable_aux (λ x, x ∈ set.range (λ y : α × β, (encode y.1).node (encode y.2))) :=
begin
  rw polydecidable_aux_iff,
  rw polydecidable.of_eq (λ x, x ≠ ptree.nil ∧ x.left ∈ set.range (@encode α _) ∧ x.right ∈ set.range (@encode β _)),
  swap, { intro x, split,
    { rintro ⟨y, hy⟩, simp at hy, subst hy, simp only [ptree.left,
 set.mem_range_self,
 ne.def,
 not_false_iff,
 and_self,
 ptree.right.equations._eqn_2], }, 
    rintro ⟨nnil, ⟨ly, hly⟩, ⟨ry, hry⟩⟩,
    have : x = ptree.node (encode ly) (encode ry), { cases x, contradiction, simp [hly, hry], }, subst this,
    use (ly, ry),  },
  exact polydecidable.children (mem_poly α) (mem_poly β),
end