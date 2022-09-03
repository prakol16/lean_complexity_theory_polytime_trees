import topology.tactic
import topology.instances.real



example {X : Type*} [topological_space X] : continuous (@id X) :=
by { continuity, }

example : continuous (λ (x : ℝ), -x) :=
by { exact continuous_id'.neg, }


