Require Import Bool SetoidList.
Require Import OUVerT.orderedtypes OUVerT.compile.

(* This file describes some abstract decision procedures over lists
    along with reflection lemmas describing the relation between
    a given decision procedure and corresponding propositions.
*)

(* This describes a decision procedure for determining if a
    given list contains no pairs of elements satisfying the
    abstract relation R_prop.

   In the current application, R_prop is an equivalence relation
    and thus, we name the procedure NoDup_dec, as it determines
    if there are any duplicated elements in the list modulo
    the equivalence relation.
*)
Section NoDup_dec.
  Variable (A : Type).
  Variable (R_prop : A -> A -> Prop).
  Variable (R_bool : A -> A -> bool).
  Variable (R_refl : forall a1 a2,
                      reflect (R_prop a1 a2) (R_bool a1 a2)).

  Fixpoint R_InA_bool (a : A) (l : list A) : bool :=
  match l with
  | nil => false
  | cons a' l' =>
      if R_bool a a'
        then true
        else R_InA_bool a l'
  end.

  Lemma R_InA_refl :
    forall a l,
      reflect (InA R_prop a l) (R_InA_bool a l).
  Proof.
    intros.
    induction l.
    + constructor. intros H_contra. inversion H_contra.
    + simpl. specialize (R_refl a a0). inversion R_refl.
      - constructor. left. auto.
      - inversion IHl; constructor. right; auto.
        intros H_contra. inversion H_contra; subst; auto.
  Qed.

  Fixpoint R_NoDupA_bool (l : list A) : bool :=
  match l with
  | nil => true
  | cons a l' =>
      if R_InA_bool a l'
        then false
        else R_NoDupA_bool l'
  end.

  Lemma R_NoDupA_refl : 
    forall l,
      reflect (NoDupA R_prop l) (R_NoDupA_bool l).
  Proof.
    induction l.
    - do 2 constructor.
    - simpl. generalize (R_InA_refl a l). intros.
      inversion H.
      * constructor. intros H_contra.
        inversion H_contra; congruence.
      * inversion IHl; constructor.
        constructor; auto.
        intros H_contra. inversion H_contra.
        congruence.
  Qed.
End NoDup_dec.

(* Given an enumerable type, a list and a relation between
    elements of the enumerable type and the underlying type of
    the list, this describes a decision procedure for determining
    if for element of the type there exists some member of the list
    such that the relation holds between the two.
*)
Section complete_InRel_bool.
  Variables A B : Type.
  Variable AB_R : A -> B -> Prop.
  Variable AB_b : A -> B -> bool.
  Variable AB_refl : forall a b, reflect (AB_R a b) (AB_b a b).

  (* Checks if there exists some b in l such that (AB_b a b = true). *)
  Fixpoint InRel_bool (a : A) (l : list B) : bool :=
  match l with
  | nil => false
  | cons b l' => if AB_b a b
                  then true 
                  else InRel_bool a l'
  end.

  Definition InRel_Prop (a : A) (l : list B) :=
    exists x, AB_R a x /\ List.In x l.

  Lemma InRel_refl a l :
    reflect (InRel_Prop a l) (InRel_bool a l).
  Proof.
    intros. induction l; simpl.
    - constructor. intros H_contra.
      inversion H_contra. inversion H.
      inversion H1.
    - generalize (AB_refl a a0); intros.
      inversion H.
      * constructor. exists a0; split; try left; auto.
      * inversion IHl; constructor.
        destruct H3. exists x. split; firstorder.
        intros H_contra. inversion H_contra. inversion H4.
        inversion H6. apply H1; subst. firstorder.
        apply H3. firstorder.
  Qed.
  
  Fixpoint InRel_list_bool (lA : list A) (lB : list B) : bool :=
  match lA with
  | nil => true
  | cons a lA' => if InRel_bool a lB
                  then InRel_list_bool lA' lB
                  else false
  end.
  
  Definition InRel_list_Prop (lA : list A) (lB : list B) : Prop :=
    forall a, List.In a lA -> InRel_Prop a lB.

  Lemma InRel_list_refl (lA : list A) (lB : list B) :
    reflect (InRel_list_Prop lA lB) (InRel_list_bool lA lB).
  Proof.
    generalize dependent lB. induction lA; intros; simpl.
    - constructor. intros a H. inversion H.
    - generalize (InRel_refl a lB); intros.
      inversion H. unfold InRel_Prop in H1.
      specialize (IHlA lB). inversion IHlA; constructor.
      * intros a' H4. inversion H4; subst.
        apply H1. apply H3. auto.
      * intros H_contra. apply H3.
        intros a' H_contra'.
        apply H_contra. right. auto.
      * constructor. intros H_contra.
        apply H1. apply H_contra. left. auto.
  Qed.

  Variable EnumA : Enumerable A.
  Variable EnumA_ok : @Enum_ok _ EnumA.

  Definition InRel_list_complete (l : list B) : Prop :=
    forall a, exists b, AB_R a b /\ List.In b l.

  Definition InRel_list_complete_bool (l : list B) : bool :=
    InRel_list_bool EnumA l.

  Lemma InRel_list_complete_refl (l : list B) :
    reflect (InRel_list_complete l) (InRel_list_complete_bool l).
  Proof.
    generalize (InRel_list_refl EnumA l); intros.
    unfold InRel_list_complete_bool.
    inversion H; simpl; constructor.
    - intros a. specialize (H1 a).
      assert (InRel_Prop a l). apply H1.
      inversion EnumA_ok. apply enum_total.
      inversion H2. exists x. firstorder.
    - intros H_contra. apply H1.
      intros a H2. specialize (H_contra a).
      inversion H_contra. exists x. firstorder.
  Qed.
End complete_InRel_bool.