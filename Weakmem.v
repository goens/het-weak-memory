Require Import String.
Require Import List.

Declare Scope mem_scope.
Open Scope mem_scope.

Variable instruction : Type.
Variable address : instruction -> nat.
Variable thread : instruction -> nat.
Structure event := {
    identifier : string;
    location : nat;
    instr : instruction;
  }.

Definition event_relation := event -> event -> Prop.
Inductive transitive_closure (r : event_relation) : event_relation :=
  | tran_step x y z : r x y -> transitive_closure r y z -> transitive_closure r x z.
Inductive refl_transitive_closure (r : event_relation) : event_relation :=
  | refl x : refl_transitive_closure r x x
  | refl_tran_step x y z : r x y -> refl_transitive_closure r y z -> refl_transitive_closure r x z.
Definition seq_comp (r s : event_relation) : event_relation :=
  fun x y => exists z, r x z /\ s z y.
Definition rel_union (r s : event_relation) : event_relation :=
  fun x y => r x y \/ s x y.
Definition rel_inverse (r : event_relation) : event_relation :=
  fun x y => r y x.

Definition irreflexive (r : event_relation) := forall e, not (r e e).
Definition acyclic (r : event_relation) := irreflexive (transitive_closure r).

Notation "'[' r ']+'" := (transitive_closure r) (at level 20).
Notation "'[' r ']*'" := (refl_transitive_closure r) (at level 20).
Notation "'[' r ; s ']'" := (seq_comp r s) (at level 20, left associativity).
Notation "r ∪ s " := (rel_union r s) (at level 25, left associativity).
Notation "e ∈ l" := (List.In e l) (at level 80, right associativity).

Structure execution := {
    events : list event;
    po : event_relation;
    rf : event_relation;
    co : event_relation;
    identifiers_unique : forall (e e' : event), e ∈ events -> e' ∈ events -> e <> e' -> e.(identifier) <> e'.(identifier);
    locations_unique : forall (e e' : event), e ∈ events -> e' ∈ events -> e.(location) = e'.(location) -> e.(instr) = e'.(instr);
    (* could the above maybe have different arguments? *)
    (* missing axioms? *)
  }.

Structure architecture := {
    ppo : list event -> event_relation;
    fences : list event -> event_relation;
    prop : list event -> event_relation;
  }.


Definition fr (ex : execution) : event_relation := [rel_inverse ex.(rf) ; ex.(co)].
Definition com (ex : execution) : event_relation := ex.(co) ∪ ex.(rf) ∪ (fr ex).
Definition po_loc (ex : execution) : event_relation := fun x y => ex.(po) x y /\ (address x.(instr) = address y.(instr)).
Definition fre (ex : execution) : event_relation := fun x y => (fr ex) x y /\ (thread x.(instr) <> thread y.(instr)).
Definition rfe (ex : execution) : event_relation := fun x y => ex.(rf) x y /\ (thread x.(instr) <> thread y.(instr)).
Definition hb (ex : execution) (arch : architecture) := arch.(ppo) ex.(events) ∪ arch.(fences) ex.(events) ∪ rfe ex.
Definition sc_per_location (ex : execution) := acyclic (po_loc ex ∪ com ex).
Definition no_thin_air (arch : architecture) (ex : execution) := acyclic (hb ex arch).
Definition observation (arch : architecture) (ex : execution) :=
  let fre_prop := [fre ex ; arch.(prop) ex.(events)] in
  let hbstar := [hb ex arch]* in
  let rel := [ fre_prop ; hbstar] in
  irreflexive rel.
Definition propagation (arch : architecture) (ex : execution) := acyclic (ex.(co) ∪ arch.(prop) ex.(events)).

Definition weak_memory_model (arch : architecture) := forall (ex : execution),
    sc_per_location ex /\ no_thin_air arch ex /\ observation arch ex /\ propagation arch ex.


