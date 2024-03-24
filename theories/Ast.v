Section Ast.

Inductive sort : Type :=
| sSucc : sort -> sort
| sPi : sort -> sort -> sort
| sSig : sort -> sort -> sort
.

Inductive term : Type :=
| tRel (n : nat)
| tSort (s : sort)
| tProd (A B : term)
| tLambda (t : term)
| tApp (u v : term)
| tSum (A B : term)
| tPair (u v : term)
| tPi1 (p : term)
| tPi2 (p : term)
.
End Ast.

Declare Scope t_scope.
Notation "'*' s" := (tSort s) (at level 8, format "'*' s") : t_scope.
Notation "'^' n" := (tRel n) (at level 8, format "'^' n") : t_scope.
Notation "'∑' A ',' B" := (tSum A B) (at level 11, A at next level, right associativity, format "'∑' A ','  B") : t_scope.
Notation "'∏' A ',' B" := (tProd A B) (at level 11, A at next level, right associativity, format "'∏' A ','  B") : t_scope.
Notation "'λ,' t" := (tLambda t) (at level 11, right associativity, format "'λ,'  t") : t_scope.
Notation "u '@' v" := (tApp u v) (at level 11, no associativity, format "u  '@'  v") : t_scope.
Notation "'⟨' u ',' v '⟩'" := (tPair u v) (at level 9, no associativity, format "'⟨' u ','  v '⟩'") : t_scope.
Notation "'π₁' x" := (tPi1 x) (at level 9, right associativity, format "'π₁'  x") : t_scope.
Notation "'π₂' x" := (tPi2 x) (at level 9, right associativity, format "'π₂'  x") : t_scope.
