Require Export stlc.Maps.

Inductive ty : Type := 
  | TVar  : string -> ty 
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : string -> tm
  | tapp : tm -> tm -> tm
  | tabs : string -> ty -> tm -> tm.

Definition context := partial_map ty.

Definition extend {A:Type} (Gamma : partial_map A) (x:string) (T : A) :=
  fun x' => if beq_string x x' then Some T else Gamma x'.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tvar x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 -> 
      has_type Gamma (tabs x T11 t12) (TArrow T11 T12)
  | T_App : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (TArrow T11 T12) -> 
      has_type Gamma t2 T11 -> 
      has_type Gamma (tapp t1 t2) T12.

Fixpoint beq_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | TVar a, TVar b => beq_string a b
  | TArrow T11 T12, TArrow T21 T22 =>
      andb (beq_ty T11 T21) (beq_ty T12 T22)
  | _,_ => 
      false
  end.

Lemma beq_ty_refl : forall T1,
  beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    apply beq_string_true_iff. reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma beq_ty__eq : forall T1 T2,
  beq_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - apply beq_string_true_iff in H0. rewrite H0. reflexivity.
  - apply andb_prop in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst... reflexivity. Qed.

Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
  match t with
  | tvar x => Gamma x
  | tabs x T11 t12 => match type_check (extend Gamma x T11) t12 with
                          | Some T12 => Some (TArrow T11 T12)
                          | _ => None
                        end
  | tapp t1 t2 => match type_check Gamma t1, type_check Gamma t2 with
                      | Some (TArrow T11 T12),Some T2 =>
                        if beq_ty T11 T2 then Some T12 else None
                      | _,_ => None
                    end
  end.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if beq_string x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if beq_string x x' then t1 else (subst x s t1)) 
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  end.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - apply T_Var. apply H0.
  - remember (type_check Gamma t1) as TO1.
    remember (type_check Gamma t2) as TO2.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert.
    destruct TO2 as [T2|]; try solve_by_invert.
    remember (beq_ty T11 T2) as b.
    destruct b; try solve_by_invert.
    symmetry in Heqb. apply beq_ty__eq in Heqb.
    inversion H0; subst... 
    apply T_App with (T11 := T2) (T12 := T).
    symmetry in HeqTO1.
    apply IHt1 in HeqTO1. apply HeqTO1.
    symmetry in HeqTO2.
    apply IHt2 in HeqTO2. apply HeqTO2.
  - remember (extend Gamma s t) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0. apply T_Abs. rewrite <- HeqG'.
    apply IHt. rewrite HeqTO2. reflexivity. Qed.


Lemma typecheck_complete : forall E t A,
  has_type E t A ->
  type_check E t = Some A.
Proof.
intros E t A H.
induction H.
- apply H.
- simpl.
  rewrite IHtyped1. rewrite IHtyped2.
  rewrite beq_ty_refl.
  reflexivity.
- simpl.
  rewrite IHtyped. reflexivity.
Qed.











