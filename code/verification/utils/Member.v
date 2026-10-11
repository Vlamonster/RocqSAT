(* Membership of an element in a collection. *)
Class Member (A B: Type) := member: A -> B -> Prop.

Declare Scope member_scope.
Infix "∈" := member (at level 70): member_scope.
Open Scope member_scope.
