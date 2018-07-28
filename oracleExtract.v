Require Import BinNat.
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
  Definition eta : dyadic.D :=
    dyadic.Dmake BinIntDef.Z.one (4%positive).
  Definition num_rounds : N.t := N.of_nat 10.

  (* Change this to change the identifier of the input/output channels *)
  Definition inputChanName : string := 
    "./clientInput".
  Definition outputChanName : string :=
    "./clientOutput".

  Module strategies_bound : BOUND.
    Definition n := 10.
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
        _ _
        ).
  Next Obligation.
    rewrite Bool.andb_true_iff in H1.
    destruct H1.
    unfold prerecv_chk_complete_in_range_bool in H.
    erewrite <- Bool.reflect_iff in H.
    2: {
      apply InRel_list_complete_refl.
      intros. apply in_range_refl.
        apply MProps.enum_ok.
    }
    specialize (H a).
    destruct H as [b [H H1]].
    exists (snd b); constructor;
    unfold in_range_Prop in H;
    destruct H as [H [H2 H3]]; auto.
    subst. replace b with (fst b, snd b) in H1; try auto.
    destruct b; simpl; auto.
  Qed.
  Next Obligation.
    rewrite Bool.andb_true_iff in H1.
    destruct H1.
    unfold prerecv_chk_nodup in H0.
    erewrite <- Bool.reflect_iff in H0.
    2: {
      apply R_NoDupA_refl.
      unfold uniqR_bool. 
      apply Mt_refl_pair.
    }
    auto.
  Qed.

Module MWUextract := MWU M.

(* These are some baasic extraction directives to
    reduce Coq types to their corresponding OCaml types *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive bool => "bool" ["true" "false"].

Definition extractedMW :=
  (MWUextract.mwu eta num_rounds).


Extraction Language OCaml.
Extraction "./_build/extractedMWU" extractedMW.
