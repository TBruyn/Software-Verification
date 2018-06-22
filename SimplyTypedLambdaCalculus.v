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
  match A with
  | tvar a   => match B with
                | tvar b => beq_string a b
                | _      => false
                end
  | tarr C D => match B with
                | tarr E F => (beq_type C E) 
                              && (beq_type E F)
                | _        => false
                end
  end.

Fixpoint beq_term (M: term) (N: term) :=
  match M with
  | var m => match N with
             | var n => beq_string m n
             | _     => false
            end
  | app M1 M2 => match N with
              | app N1 N2 => (beq_term M1 N1) 
                             && (beq_term M2 N2)
              | _         => false
              end
  | lam x A m => match N with
                  | lam y B n => (beq_string x y)
                                 && (beq_type A B)
                                 && (beq_term m n)
                  | _ => false
                  end
end.

(* Exercise 2.5 *)

Fixpoint typecheck (E : ctx) (t : term) : option type :=
  match t with
  | var x => E x
  | app M N => 
    match (typecheck E M) with
    | Some (tarr A B) => 
      match (typecheck E N) with
      | Some C  => if (beq_type A C) then Some B 
                                     else None
      | _       => None
      end
    | _ => None
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

lemma typecheck1 : typecheck empty 

Inductive type :=
| tvar : string -> type
| tarr : type -> type -> type.

Inductive term :=
| var : string -> term
| app : term -> term -> term
| lam : string -> type -> term -> term .




