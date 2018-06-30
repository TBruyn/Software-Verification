Require Export stlc.Maps.

Inductive type : Type := 
  | tvar  : string -> type 
  | tarr : type -> type -> type.

Inductive term : Type :=
  | var : string -> term
  | app : term -> term -> term
  | lam : string -> type -> term -> term.

Definition ctx := partial_map type.

(* Exercise 2.1 *)

Definition X_Y_X (X:string) (Y:string) : type := 
  tarr (tvar X) (tarr (tvar Y) (tvar X)).

Definition XX_XX (X:string) : type := 
  tarr (tarr (tvar X) (tvar X)) (tarr (tvar X) (tvar X)).

(* Exercise 2.2 *)

Definition lxly_x (X:string) (Y:string) : term :=
  lam "x" (tvar X) (lam "y" (tvar Y) (var "x")).

Definition lflx_ffx (X:string) : term :=
  lam "f" (tarr (tvar X) (tvar X)) 
      (lam  "x" (tvar X) 
            (app  (var "f") 
                  (app  (var "f") 
                        (var "x")))).

(* Exercise 2.3 *)

Inductive typed : ctx -> term -> type -> Prop :=
  | var_typed : forall E x A,
      E x = Some A ->
      typed E (var x) A
  | app_typed : forall A B E M N,
      typed E M (tarr A B) ->
      typed E N A -> 
      typed E (app M N) B
  | lam_typed : forall E x A B M,
      typed (update E x A) M B -> 
      typed E (lam x A M) (tarr A B).

(* Exercise 2.4 *)

Lemma test : typed  empty
                    (lxly_x "X" "Y") 
                    (X_Y_X "X" "Y").
Proof.
unfold lxly_x. unfold X_Y_X.
apply lam_typed. 
apply lam_typed. 
apply var_typed.
reflexivity.
Qed.

(* Exercise 2.5 *)

(*  To build a typechecker, we first need to define 
    a helper function for type equality and prove that
    it actually defines equality. *)
Fixpoint beq_type (A B:type) : bool :=
  match A,B with
  | tvar a, tvar b => beq_string a b
  | tarr A1 A2, tarr B1 B2 =>
      andb (beq_type A1 B1) (beq_type A2 B2)
  | _,_ => 
      false
  end.

Lemma beq_type_refl : forall A,
  beq_type A A = true.
Proof.
  intros A1. induction A1; simpl.
  apply beq_string_true_iff. reflexivity.
  rewrite IHA1_1. rewrite IHA1_2. reflexivity.  Qed.

Lemma beq_type_eq : forall A B,
  beq_type A B = true -> A = B.
Proof.
  intros A. induction A; intros A Hbeq; destruct A; inversion Hbeq.
  - apply beq_string_true_iff in H0. rewrite H0. reflexivity.
  - apply andb_prop in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHA1 in Hbeq1. apply IHA2 in Hbeq2. subst... reflexivity. Qed.

Fixpoint typecheck (E:ctx) (t:term) : option type :=
  match t with
  | var x     => E x
  | app M N   => match typecheck E M, typecheck E N with
                 | Some (tarr A B),Some A1 =>
                    if beq_type A A1 then Some B else None
                 | _,_ => None
                    end
  | lam x A M => match typecheck (update E x A) M with
                 | Some B => Some (tarr A B)
                 | _ => None
                 end
  end.

(* Exercise 2.6 *)

(* 
The typing judgement [typed] will tell us for a given
context, term and type whether the term is of that type.
The type checker [typecheck] will tell us for a given
context and term what the type is (or it will return
nothing if there is no type).
 *)

(* Exercise 2.7 *)

Example pos_typecheck_1 : 
typecheck empty (lxly_x "X" "Y") = Some (X_Y_X "X" "Y").
Proof. reflexivity. Qed.

Example pos_typecheck_2 : 
typecheck empty (lflx_ffx "X") = Some (XX_XX "X").
Proof. reflexivity. Qed.

Definition lx_xx (X: string) := 
  lam "x" (tvar X) (app (var "x") (var "x")).

Example neg_typecheck_1 : 
typecheck empty (lx_xx "X") = None.
Proof. reflexivity. Qed.

Definition lflx_xf (X: string) :=
  lam "f" (tarr (tvar X) (tvar X)) 
      (lam "x" (tvar X) 
           (app (var "x") (var "f")) ).

Example neg_typecheck_2 :
typecheck empty (lflx_xf "X") = None.
Proof. reflexivity. Qed.

(* Exercise 2.8 *)

Lemma typecheck_complete : forall E t A,
  typed E t A ->
  typecheck E t = Some A.
Proof.
intros E t A H.
induction H.
- apply H.
- simpl.
  rewrite IHtyped1. rewrite IHtyped2.
  rewrite beq_type_refl.
  reflexivity.
- simpl.
  rewrite IHtyped. reflexivity.
Qed.

Ltac solve_by_invert :=
  match goal with 
  | H : ?T 
  |- _ => match type of T with 
          | Prop => solve [inversion H]
          end
  end.

Lemma typecheck_sound : forall E t A,
  typecheck E t = Some A -> typed E t A.
Proof.
  intros E t. generalize dependent E.
  induction t; intros E T Htc; inversion Htc.
  - apply var_typed. apply H0.
  - remember (typecheck E t1) as TO1.
    remember (typecheck E t2) as TO2.
    destruct TO1 as [A|]; try solve_by_invert;
    destruct A as [|A1 A2]; try solve_by_invert.
    destruct TO2 as [B|]; try solve_by_invert.
    remember (beq_type A1 B) as b.
    destruct b; try solve_by_invert.
    symmetry in Heqb. apply beq_type_eq in Heqb.
    inversion H0; subst... 
    apply app_typed with (A := B) (B := T).
    symmetry in HeqTO1.
    apply IHt1 in HeqTO1. apply HeqTO1.
    symmetry in HeqTO2.
    apply IHt2 in HeqTO2. apply HeqTO2.
  - remember (update E s t) as G'.
    remember (typecheck G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0. apply lam_typed. rewrite <- HeqG'.
    apply IHt. rewrite HeqTO2. reflexivity. Qed.











