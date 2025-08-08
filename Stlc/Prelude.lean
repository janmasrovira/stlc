namespace List

@[simp]
def Product (tys : List (Type u)) : Type u :=
  match tys with
  | []      => ULift Unit
  | t :: ts => t × Product ts

end List
