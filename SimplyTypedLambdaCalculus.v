Require Export stlc.Maps.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Inductive type :=
| tvar : string -> type
| tarr : type -> type -> type.

Inductive term :=
| var : string -> term
| app : term -> term -> term
| lam : string -> type -> term -> term .

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

Definition ctx := partial_map type.

(* Exercise 2.3 *)

Inductive typed : ctx -> term -> type -> Prop :=
  | var_typed : forall E x A, 
    E x = Some A -> 
    typed E (var x) A

  | app_typed : forall E M N A B,
    typed E M (tarr A B) ->
    typed E N A ->
    typed E (app M N) B

  | lam_typed : forall E x M A B,
    typed (E & { x --> Some A}) M B ->
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

Fixpoint beq_type (A:type) (B:type) :=
  match A, B with
  | tvar a, tvar b =>
      beq_string a b
  | tarr A1 A2, tarr B1 B2 =>
      beq_type A1 B1 && beq_type A2 B2
  | _,_ =>
      false
end.

Lemma beq_type_eq : forall A B,
beq_type A B = true -> A = B.
Proof.
intros A.
induction A; intros B Hbeq; 
destruct B; inversion Hbeq.
- apply beq_string_true_iff in Hbeq. 
  rewrite Hbeq. reflexivity.
- apply andb_prop in H0. 
  destruct H0 as [Hbeq1 Hbeq2].
  apply IHA1 in Hbeq1.
  apply IHA2 in Hbeq2.
  rewrite Hbeq1. rewrite Hbeq2.
  reflexivity.
Qed.

Lemma beq_type_refl : forall (A: type),
beq_type A A = true.
Proof.
induction A.
+ simpl. rewrite <- beq_string_refl. reflexivity.
+ simpl. rewrite IHA1. rewrite IHA2. reflexivity.
Qed.

Fixpoint beq_term (M: term) (N: term) :=
  match M, N with
  | var m, var n => 
      beq_string m n
  | app M1 M2, app N1 N2 => 
      beq_term M1 N1 && beq_term M2 N2
  | lam x A m, lam y B n => 
      beq_string x y && beq_type A B && beq_term m n
  | _,_ => false
  end.

(* Exercise 2.5 *)

Fixpoint typecheck (E : ctx) (t : term) : option type :=
  match t with
  | var x => E x
  | app M N => 
    match (typecheck E M), (typecheck E N) with
    | Some (tarr A B), Some C => 
        if beq_type A C then Some B 
                        else None
    | _,_ => None
    end
  | lam x A M => 
    match (typecheck (E&{x-->Some A}) M) with
    | Some B => Some (tarr A B)
    | _      => None
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

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Lemma typecheck_sound : forall E t A,
  typecheck E t = Some A ->
  typed E t A.
Proof.
intros E t.
induction t; intros B Htc. inversion Htc.
- apply var_typed. apply H0.
- simpl typecheck in Htc. simpl (typecheck E t1) in Htc.

unfold typecheck in Htc.
remember (typecheck E t1) as TO1.
  remember (typecheck E t2) as TO2.
  destruct TO1 as [T1|].
  + destruct T1 as [|TA TB].
    *
  +
  destruct TO2 as [T2|]; try solve_by_invert.
  destruct (beq_type T11 T2) eqn: Heqb;
  try solve_by_invert.

  apply beq_type_eq in Heqb.
  apply app_typed; subst..
-
  

destruct (typecheck E t1) as [T1|].
  destruct T1 as [|TA TB].
  + apply (Some (tvar s) = Some (tvar s)) in IHt1.
  + destruct (typecheck E t2) as [T2|].
  destruct (beq_type TA T2) eqn: Heqa.
  * apply beq_type_eq in Heqa.
    rewrite <- Heqa in IHt2.
    {destruct (beq_type TB B) eqn: Heqb.
    - apply beq_type_eq in Heqb.
      rewrite Heqb in IHt1.
      apply app_typed with (A := TA).
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    - Search solve_by_invert.
Search "iff".
    }
    apply app_typed (A := TA) (B := TB).
  *
  assert (Some T1 = Some T1) as HtypT1.
  reflexivity.
  apply IHt1 in HtypT1.
  destruct T1 as [|TA TB].
  + admit.
  + apply app_typed 
    with (E := E) (M := t1) (N := t2) 
    (A := TA) (B := B).
    * 
  + inversion app.

Admitted.

(*
Fixpoint typecheck (E : ctx) (t : term) : option type :=
  match t with
  | var x => E x
  | app M N => 
    match (typecheck E M), (typecheck E N) with
    | Some (tarr A B), Some C => 
        if beq_type A C then Some B 
                        else None
    | _,_ => None
    end
  | lam x A M => 
    match (typecheck (E&{x-->Some A}) M) with
    | Some B => Some (tarr A B)
    | _      => None
    end
  end.

Inductive typed : ctx -> term -> type -> Prop :=
  | var_typed : forall E x A, 
    E x = Some A -> 
    typed E (var x) A
  | app_typed : forall E M N A B,
    typed E M (tarr A B) ->
    typed E N A ->
    typed E (app M N) B
  | lam_typed : forall E x M A B,
    typed (E & { x --> Some A}) M B ->
    typed E (lam x A M) (tarr A B).

Inductive type :=
| tvar : string -> type
| tarr : type -> type -> type.

Inductive term :=
| var : string -> term
| app : term -> term -> term
| lam : string -> type -> term -> term .

  
    inversion IHt1. with (A := T1).
 try solve by inversion;
    destruct T1 as [|T11 T12]; try solve by inversion.

apply app_typed.
eval typecheck in Htc.
apply app_typed with (A := typecheck E t1).
- eval typecheck in IHt1.

apply app_typed with (A := . destruct typed. destruct typecheck in IHt1.
  
- remember (typecheck E t1) as TO1.
  remember (typecheck E t2) as TO2.
  destruct TO1 as [T1|]; try solve by inversion;
  destruct T1 as [|T11 T12]; try solve by inversion.
 destruct typecheck in IHt1. inversion IHt1.
+ inversion IHt1.

-
    



-d apply H in IHt1.

 induction typecheck.
 destruct app in H. simpl H. rewrite H in IHt1.
- apply H in IHt1. simpl typecheck in H.
- apply app_typed.
ast
Lemma typecheck_sound : forall E t A,
  typecheck E t = Some A ->
  typed E t A.
Proof with eauto.
intros E t.
induction t; intros B Htc. inversion Htc.
- apply var_typed. apply H0.
- remember (typecheck E t1) as TO1.
  remember (typecheck E t2) as TO2.
  destruct TO1 as [T1|].
  assert (Some T1 = Some T1) as HtypT1.
  reflexivity.
  apply IHt1 in HtypT1.
  destruct T1 as [|TA TB].
  + admit.
  + apply app_typed 
    with (E := E) (M := t1) (N := t2) 
    (A := TA) (B := B).
    * 
  + inversion app.

Admitted.

*)


