Require Import BinNat NArith.
Require Import MWU.weightsextract MWU.list_procedures.
Require Import ProofIrrelevance.
Require Import OUVerT.orderedtypes OUVerT.compile.
Require Import String.
Require Extraction.
Require Import ExtrOcamlZBigInt ExtrOcamlString.

(**
    Program parameters-- due to how modules work in Coq
      it's impossible to leave some of these abstract.
      For others, it's easiest to get extraction up and
      running by manipulating them at this point
**)
  (* Number of strategies *)
  Definition num_strategies := 10.
  (* learning parameter *)

  Definition three : Z := Zpos 3.

  Definition eta := dyadic.Dmake (three) (3%positive).

  Definition num_rounds := N.of_nat 80.

  (* Change this to change the identifier of the input/output channels *)
  Definition inputChanName : string :=
    "./clientInput".
  Definition outputChanName : string :=
    "./clientOutput".

  Module strategies_bound : BOUND.
    Definition n := num_strategies.
    Lemma n_gt0 : is_true (ssrnat.leq 1 n).
    Proof. auto. Qed.
  End strategies_bound.

  Module MProps := MyOrdNatDepProps strategies_bound.
  Module M := MProps.M.


  (* The state of the client oracle *)
  Definition oracleState : Type := (list (M.t * dyadic.D) * unit).
  (* Initiation of the oracle state *)
  Definition bogus_result : oracleState := (nil, tt).

  (* Communication between the client and enviornment
      is abstracted away at the Coq level. However, at
      extraction the exact method of communication needs
      to instantiated. We do this here to make it easy
      to adjust.

     The following terms need extraction directives. These
      can be adjusted to change how networking is handled.
      At the moment, the extracted code uses named pipes
      to pass information to and from a process acting
      as a shim between the client and an arbitrary program
      acting as the enivronment.
  *)

  (* The following are axiomatized *)

    (** Input/output channel types *)
  Axiom inChan : Type.
  Axiom outChan : Type.
    (** Functions for generating a channel from a string *)
  Axiom open_in : string -> inChan.
  Axiom open_out : string -> outChan.
    (** Functions for sending and receiving info over channels *)
  Axiom inChan_recv : inChan -> list (M.t * dyadic.D).
  Axiom outChan_send : outChan -> list (M.t * dyadic.D) -> unit.

  (* These are the Ocaml instantiations of these networking primitives *)
  Extract Constant inChan => "in_channel".
  Extract Constant outChan => "out_channel".

  Extract Constant open_in =>
    "let charlToString l : string =
        String.concat """" (List.map (String.make 1) l) in
          (fun x -> open_in (charlToString x))".
  Extract Constant open_out =>
    "let charlToString l : string =
        String.concat """" (List.map (String.make 1) l) in
          (fun x -> open_out (charlToString x))".

  Extract Constant inChan_recv =>
    "fun chan -> Marshal.from_channel chan".

  Extract Constant outChan_send =>
    "fun chan data -> Marshal.to_channel chan data []; flush chan".


  Definition Chan : Type := inChan * outChan.
  Definition openChan : string -> string -> Chan :=
    fun inS outS => (open_in inS, open_out outS).

  Definition defaultChan :=
    openChan inputChanName outputChanName.

  Definition prerecv_recv : Chan -> oracleState :=
    fun x => (inChan_recv (fst x), tt).


  (* The exact typing for send should be reworked in
      weightsextract.v to make this more modular. *)
  Definition send : oracleState -> list (M.t * dyadic.D) -> (Chan * oracleState) :=
    fun st data =>
      (defaultChan, ((fst st), (outChan_send (snd defaultChan) data))).

(* Here we begin building the client oracle to be used by MW *)
(* A ClientOracle consists of the following:
    A : Type
      -- The type of strategies played by the agent
    T : Type
      -- The type of the client oracle's internal state
    oracle_init_state : T
      -- Some initialization for the oracle's internal state
    oracle_chanty : Type
      -- The type of the communication channel used by the oracle
    oracle_bogus_chan : Type
      -- An inhabitant of the oracle_chanty, communication is actually
          processed through this channel
    orcale_prerecv : T -> oracle_chanty -> bool * T
      -- This function ensures that the input received on
          the input channel is well-formed. In this implementation,
          this function receives information through the input channel,
          checks to make sure it is well-formed. Provied it is, the
          function returns (true, s') where s' ultimately
          becomes the new ClientOracle state. Otherwise, it returns
          (false, _) and the program fails.
    oracle_recv : T -> oracle_chanty -> list (A* dyadic.D) * T
      -- This function is intended to actually handle the receipt of the
          input through the input channel. In this implementation,
          the function simply returns the oracle's state (the message
          has already been caught and checked by oracle_prerecv).

    oracle_presend : T -> list (A * dyadic.D) -> bool
      -- This function is intended to check that the infomration that
          is produced for output by the oracle meets the proper
          preconditions. The type constraints on the output suffice
          for this implementation, and this function vacuously
          returns true.

    oracle_send : T -> list (A * dyyadic.D) -> oracle_chanty * T
      -- The function responsible for sending the distribution
          to the environment.

    oracle_recv_ok, oracle_recv_no_dup : ... -> Prop
      -- Constraints on the behavior of the oracle_prerecv function.

*)

(**
    Here we build the function which checks the
      output of prerecv_recv to make sure it satisfies
      the constraints of oracle_recv_ok and oracle_recv_no_dup
**)

(* A function which compares the values of two elements of M.t *)
Definition Mt_eqb (p q : M.t) : bool :=
  (BinNatDef.N.eqb (M.val p) (M.val q)).

Definition Mt_eqb_pair (A : Type) (p q : M.t * A) : bool :=
  Mt_eqb (fst p) (fst q).

Lemma Mt_refl :
  forall p q, Bool.reflect (eq p q)(Mt_eqb p q).
Proof.
  intros. unfold Mt_eqb.
  generalize (N.eqb_spec (M.val p) (M.val q)).
  intros. inversion H; constructor.
  destruct p, q; simpl in *. subst. f_equal.
  apply proof_irrelevance.
  intros H_contra. congruence.
Qed.

Lemma Mt_refl_pair :
    forall (A : Type) (p q : M.t * A),
      Bool.reflect (eq (fst p) (fst q)) (Mt_eqb_pair _ p q).
Proof.
  intros. (unfold Mt_eqb_pair).
  apply Mt_refl.
Qed.

(* returns a bool indicating if two strategy * weight pairs
    share a strategy label *)
Definition uniqR_bool (p q : M.t * dyadic.D) : bool :=
  Mt_eqb (fst p) (fst q).

(* returns a bool indicating if each strategy * weight pair
    has a unique strategy label *)
Definition prerecv_chk_nodup :  list (M.t * dyadic.D) -> bool :=
  (R_NoDupA_bool _ uniqR_bool).

(* Check to ensure that a strategy * weight pair is in the
    correct range *)
Definition in_range_bool (n : M.t)(p : M.t * dyadic.D) : bool :=
  (Mt_eqb n (fst p)) &&
  (dyadic.Dle_bool (dyadic.Dopp dyadic.D1) (snd p)) &&
  (dyadic.Dle_bool (snd p) (dyadic.D1)).

Definition in_range_Prop (n : M.t) (p : M.t * dyadic.D) : Prop :=
  n = (fst p) /\
  (dyadic.Dle (dyadic.Dopp dyadic.D1) (snd p)) /\
  (dyadic.Dle (snd p) (dyadic.D1)).

Lemma in_range_refl :
  forall n p,
    Bool.reflect (in_range_Prop n p) (in_range_bool n p).
Proof.
  intros.
  unfold in_range_bool.
  case_eq (Mt_eqb n (fst p)); intros.
  case_eq (dyadic.Dle_bool (dyadic.Dopp dyadic.D1) (snd p)); intros.
  case_eq (dyadic.Dle_bool (snd p) dyadic.D1); intros.
  all:simpl; constructor; unfold in_range_Prop.
  + split.
    - destruct (Mt_refl n (fst p)); auto. congruence.
    split; apply dyadic.Dle_bool_iff; auto.
  all: intros H_contra; destruct H_contra as [HC1 [HC2 HC3]].
  + apply dyadic.Dle_bool_iff in HC3. congruence.
  + apply dyadic.Dle_bool_iff in HC2. congruence.
  + destruct (Mt_refl n (fst p)); auto.
Qed.

(* returns a bool indicating if every strategy is paired with a
    a weight in the correct range *)
Definition prerecv_chk_complete_in_range_bool :=
  InRel_list_complete_bool _ _ in_range_bool M.enumerable.

(*
  Our prerecv function simply calls the
    prerecv_recv function and validates its return
    using the prerecv_chk_complete and prerecv_chk_nodup
    functions defined above
*)
Definition prerecv : oracleState -> Chan -> bool * oracleState :=
  fun r c =>
    let message := prerecv_recv c in
      (andb (prerecv_chk_complete_in_range_bool (fst message))
            (prerecv_chk_nodup (fst message)),
        message).

Definition recv :
  oracleState -> Chan -> list (M.t * dyadic.D) * oracleState :=
fun s chan => ((fst s), s).

Definition presend : oracleState -> list (M.t * dyadic.D) -> bool :=
  fun _ _ => true.

Definition myOracle_recv_ok :
  forall st ch st',
    prerecv st ch = (true, st') ->
      forall a,
        exists d,
          ssrbool.and3 (List.In (a, d) (fst (prerecv_recv ch)))
          (dyadic.Dle (dyadic.Dopp dyadic.D1) d)
          (dyadic.Dle d dyadic.D1).
Proof.
  intros. unfold prerecv in H.
  inversion H; subst.
  rewrite Bool.andb_true_iff in H1.
  destruct H1.
  unfold prerecv_chk_complete_in_range_bool in H.
  erewrite <- Bool.reflect_iff in H0.
  2: {
    apply InRel_list_complete_refl.
    intros. apply in_range_refl.
      apply MProps.enum_ok.
  }
  specialize (H0 a).
  destruct H0 as [b [H0 H2]].
  exists (snd b); constructor;
  unfold in_range_Prop in H0;
  destruct H0 as [H' [H4 H3]]; auto;
  subst; replace b with (fst b, snd b) in H1; try auto;
  destruct b; simpl; auto.
Qed.

Lemma myOracle_recv_no_dup :
  forall st ch st',
    prerecv st ch = (true, st') ->
      SetoidList.NoDupA (fun p q : M.t * dyadic.D => fst p = fst q)
        (fst (prerecv_recv ch)).
Proof.
  intros.
  unfold prerecv in H. inversion H.
  rewrite Bool.andb_true_iff in H1.
  destruct H1.
  unfold prerecv_chk_nodup in H1.
  erewrite <- Bool.reflect_iff in H1.
  2: {
    apply R_NoDupA_refl.
    unfold uniqR_bool.
    apply Mt_refl_pair.
  }
  auto.
Qed.

(** Consider moving me to OUVerT.listlemmas **)

Lemma NoDup_rel_inhab_implies_eq :
  forall A (a1 a2 : A) l (R : A -> A -> Prop) (Rsymm : forall x y, R x y -> R y x),
    SetoidList.NoDupA R l ->
    List.In a1 l ->
    List.In a2 l ->
    R a1 a2 ->
      a1 = a2.
Proof.
  intros. generalize dependent l.
  intros l H.
  induction H; intros.
  - inversion H0.
  destruct H1; subst.
  {
    destruct H3; subst; auto.
    apply False_rec. apply H.
    apply SetoidList.InA_alt.
    eexists; split; eauto.
  }
  {
    destruct H3; subst.
    apply False_rec. apply H.
    apply SetoidList.InA_alt.
    eexists; split; eauto.
    apply IHNoDupA; auto.
  }
Qed.

(** Consider moving me to OUVerT.dyadic **)
Lemma D_to_Q_preserves_order :
  forall x y,
    dyadic.Dle x y ->
    QArith_base.Qle (dyadic.D_to_Q x) (dyadic.D_to_Q y).
Proof.
  intros. unfold dyadic.Dle in H. auto.
Qed.

(*
  With everything built previously, we can construct
    an instance of the ClientOracle.
*)

Program Instance myOracle : ClientOracle :=
  (@mkOracle M.t
        oracleState
        bogus_result
        Chan
        defaultChan
        prerecv
        recv
        presend
        send
        _
        _
        ).
  Next Obligation.
    eapply (myOracle_recv_ok st ch).
    unfold prerecv. f_equal. simpl. auto.
  Qed.
  Next Obligation.
    eapply (myOracle_recv_no_dup st).
    unfold prerecv. rewrite <- H1. reflexivity.
  Qed.

Module MWUextract := MWU M.
Module MWUProof := MWUProof M MWUextract.



Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Definition ordinalOf_n : Type := 'I_(strategies_bound.n).

Program Definition injectToOrdinal : M.t -> ordinalOf_n :=
  fun x => @Ordinal _ (BinNatDef.N.to_nat (M.val x)) _.
Next Obligation.
  destruct x; simpl. auto.
Defined.

Program Definition injectToMod : ordinalOf_n -> M.t :=
  fun x => (@M.mk (BinNatDef.N.of_nat (nat_of_ord x)) _).
Next Obligation.
  destruct x. rewrite Nat2N.id. auto.
Defined.

Lemma valSuffEq :
  forall x y, M.val x = M.val y -> x = y.
Proof.
  move => x y pf.
  destruct x. simpl in pf.
  generalize pf0. rewrite pf.
  destruct y; simpl; move => pf2.
  f_equal. apply proof_irrelevance.
Qed.

Lemma injectsCancel : cancel injectToOrdinal injectToMod.
Proof.
  intros x. apply valSuffEq.
  unfold injectToMod, injectToOrdinal; simpl.
  rewrite N2Nat.id. auto.
Qed.

Definition eqMix : Equality.mixin_of MWUextract.A.t.
Proof.
  apply (@EqMixin _ (fun x y => BinNat.N.eqb (M.val x) (M.val y))).
  intros x y.
  move: (N.eqb_spec (M.val x) (M.val y)) => H.
  inversion H; constructor; clear H0 H.
  2:{ destruct x, y; subst. congruence. }
  destruct x. simpl in H1. move: pf. rewrite H1.
  intros. destruct y; simpl; f_equal.
  apply proof_irrelevance.
Qed.
Canonical myEqType := Eval hnf in EqType MWUextract.A.t eqMix.

Definition choiceMix : choiceMixin myEqType :=
@CanChoiceMixin [choiceType of 'I_(strategies_bound.n)] _ _ _ injectsCancel.
Canonical myChoiceType := Eval hnf in ChoiceType MWUextract.A.t choiceMix.


Definition count_mixin : Countable.mixin_of myChoiceType :=
    @CanCountMixin [countType of 'I_(strategies_bound.n)] _ _ _ injectsCancel.
Canonical myCountType := Eval hnf in CountType MWUextract.A.t count_mixin.

Program Definition fin_mixin : Finite.mixin_of myCountType :=
  @CanFinMixin myCountType _ _ _ injectsCancel.
Canonical myFinType := Eval hnf in FinType MWUextract.A.t fin_mixin.

Definition myOracleProp_recv :
  oracleState -> Chan ->
  {ffun myFinType -> rat} ->
  oracleState -> Prop := fun st ch f st'  =>
    forall a, (`|f a| <= 1)%R.


Definition myOracleProp_send :
  oracleState ->
  dist.dist myFinType rat_realFieldType ->
  Chan -> oracleState -> Prop := fun _ _ _ _ => True.

Program Instance anotherOracle : weightslang.ClientOracle
   (MWUProof.t (eq_mixin:=eqMix) (choice_mixin:=choiceMix) fin_mixin)
   oracleState oracle_chanty :=
@weightslang.mkOracle
  myFinType oracleState
  Chan myOracleProp_recv
  myOracleProp_send _.

Definition match_states_myOracles :
  oracleState ->
  MWUProof.oracle_cT ->
    Prop := eq.

(** Next two proofs might be in OUVerT.listlemmas **)
Lemma findA_implies_exists_mem :
  forall A B f (l : list (A*B)) b,
    SetoidList.findA f l = Some b ->
    exists a, List.In (a, b) l.
Proof.
  induction l.
  intros. inversion H.
  intros. simpl in H.
  destruct a.
  case_eq (f a) => H1; rewrite H1 in H.
  - exists a. left; f_equal. inversion H. auto.
  - apply IHl in H. destruct H as [a' H].
  exists a'. right; auto.
Qed.

Lemma relMorphNoDupA :
  forall A (R1 R2 : A -> A -> Prop) l,
    SetoidList.NoDupA R1 l ->
    (forall a1 a2, R2 a1 a2 -> R1 a1 a2) ->
    SetoidList.NoDupA R2 l.
Proof.
  intros.
  induction H. auto.
  constructor. intros H2.
  apply SetoidList.InA_alt in H2.
  apply H.
  apply SetoidList.InA_alt.
  inversion H2. inversion H3. exists x0. split.
  apply H0. auto. auto. auto.
Qed.



Definition init_oracle_st : oracleState :=
  @oracle_init_state MWUextract.A.t myOracle.


Program Instance myMatch :
  @MWUProof.match_oracles eqMix choiceMix fin_mixin _ myOracle oracleState _ match_states_myOracles.
Next Obligation.
  rewrite /match_states_myOracles /myOracleProp_recv.
  exists (prerecv_recv ch); split; auto.
  simpl in H1. move => a.
  move: (H1 a) => H0.
  destruct H0 as [q [H0 H0']].
  eapply MWUProof.match_maps_lem with (q := q).
  apply H1. auto.
  rewrite MWUextract.MProps.of_list_1b in H0.
  apply findA_implies_exists_mem in H0.
  destruct H0 as (a', H0).
  rewrite strings.print_Dvector_id in H0.
  assert (prerecv init_oracle_st ch = (true, (prerecv init_oracle_st ch).2)).
  { unfold prerecv. rewrite H3. simpl. auto. }
  move: (myOracle_recv_ok init_oracle_st ch _ H2 a') => H4.
  move: (myOracle_recv_no_dup _ _ _ H2) => H5.
  destruct H4 as [q' H4].
  destruct H4.
  assert ((a',q) = (a',q')).
  { eapply NoDup_rel_inhab_implies_eq.
    - 2: apply H5.
    - intros. simpl in *. auto.
    - apply H0.
    - apply H4.
    - simpl; auto.
  }
  inversion H8; subst.
  unfold dyadic.Dle in H6, H7.
  split.
  2:{ eapply QArith_base.Qle_trans. apply H7.
      apply QArith_base.Qle_lteq. right.
      constructor.
  }
  eapply QArith_base.Qle_trans.
  2: apply H6.
  unfold dyadic.D0, QArith_base.Qle; simpl.
  apply BinInt.Z.le_refl.
  rewrite strings.print_Dvector_id.
  assert (prerecv init_oracle_st ch = (true, (prerecv init_oracle_st ch).2)).
  { unfold prerecv. rewrite H3. simpl. auto. }
  move: (myOracle_recv_no_dup _ _ _ H0) => H5.
  unfold MWUextract.M.eq_key, MWUextract.M.Raw.Proofs.PX.eqk.
  unfold MWUextract.M.key.
  unfold prerecv_recv in H5. simpl in H5.
  eapply (relMorphNoDupA _ _ _ _ H5).
  intros. rewrite M.eqP. auto.
Qed.
Next Obligation.
  unfold myOracleProp_send.
  unfold match_states_myOracles.
  eexists.
  split; try eauto.
Qed.

Definition a0 : @MWUProof.t eqMix choiceMix fin_mixin.
Proof.
  apply (@M.mk (N.of_nat 0)).
  rewrite Nat2N.id. apply strategies_bound.n_gt0.
Defined.

(** Move me to OUVerT.listlemmas **)
Lemma NoDupAsNoDupA :
  forall A (l : list A),
    List.NoDup l <-> SetoidList.NoDupA eq l.
Proof.
  intros.
  induction l.
  - split; intros; constructor.
  - split; intros;
    inversion H; subst; constructor;
    try intros Hcontra;
    try apply H2; try apply IHl; auto.
    apply SetoidList.InA_alt in Hcontra.
    destruct Hcontra as [y [Hcontra Hcontra']].
    subst; auto.
    apply SetoidList.InA_alt. exists a; split; auto.
Qed.


Instance refineClassInstance :
  @RefineTypeAxiomClass (@MWUProof.t eqMix choiceMix fin_mixin) M.enumerable.
Proof.
  constructor. intros x.
  rewrite mem_enum.
  replace (x \in enumerate @MWUProof.t eqMix choiceMix fin_mixin) with true.
  auto. simpl. symmetry.
  replace ((x \in enumerate MWUextract.A.t) = true) with
    (is_true (x \in enumerate MWUextract.A.t)).
  2: auto.
  rewrite listlemmas.list_in_iff.
  move: (MProps.enum_ok_obligation_2 x) => Hin. apply Hin.
  apply listlemmas.nodup_uniq.
  simpl.
  apply NoDupAsNoDupA.
  exact MProps.enumerate_t_nodup.
Qed.


Lemma etaOk : MWUProof.epsOk (numerics.Q_to_rat (dyadic.DO_to_Q eta)).
Proof.
  constructor.
Qed.

Definition initMatch :
  match_states_myOracles init_oracle_st
      (@oracle_init_state MWUextract.A.t myOracle).
Proof.
  unfold match_states_myOracles.
  constructor.
Qed.

Definition roundsPf : 0 < num_rounds.
Proof. auto. Qed.


Import Reals.
Import dyadic numerics weightslang.
Import MWUProof.

Lemma mwu_proof :
  forall finState,
    MWUextract.interp
      (mult_weights
         (MWUProof.t (eq_mixin:=eqMix) (choice_mixin:=choiceMix) fin_mixin)
         num_rounds) (MWUextract.init_cstate eta) =
    Some finState ->
    exists
      s' : state
             (MWUProof.t (eq_mixin:=eqMix) (choice_mixin:=choiceMix) fin_mixin)
             oracleState oracle_chanty,
      MWUProof.match_states (eq_mixin:=eqMix) (choice_mixin:=choiceMix)
        (fin_mixin:=fin_mixin) match_states_myOracles s' finState /\
      ((state_expCost1 (all_costs0 s') s' - OPTR a0 s') / Tx num_rounds <=
       rat_to_R (Q_to_rat (D_to_Q eta)) +
       ln
         (rat_to_R
            #|MWUProof.t (eq_mixin:=eqMix) (choice_mixin:=choiceMix) fin_mixin|%:R) /
       (rat_to_R (Q_to_rat (D_to_Q eta)) * Tx num_rounds))%R.
Proof.
  intros.
  eapply MWUProof.interp_mult_weights_epsilon_no_regret
    with (enumerable_instance := M.enumerable)
         (showable_instance := M.showable)
         (init_oracle_st := init_oracle_st).
  4: apply initMatch.
  1: apply myMatch.
  1: apply refineClassInstance.
  1: apply etaOk.
  1: apply roundsPf.
  auto.
Qed.

(* These are some basic extraction directives to
    reduce Coq types to their corresponding OCaml types *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive bool => "bool" ["true" "false"].

Definition extractedMW :=
  (MWUextract.mwu eta num_rounds).


Extraction Language OCaml.


Extraction "./runtime/extractedMWU" extractedMW.
Extraction "./examples/classifier/extractedMWU" extractedMW.
