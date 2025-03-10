theorem neg_impl : (P -> Q) -> (¬ Q -> ¬ P) := by
  intros HPQ HnQ HP
  apply HnQ
  apply HPQ
  apply HP

