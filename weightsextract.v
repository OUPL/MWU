Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.
Require Import ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Reals.

Require Import OUVerT.strings OUVerT.compile OUVerT.dist
        OUVerT.numerics OUVerT.dyadic OUVerT.orderedtypes.
Require Import MWU.weights MWU.weightslang.


(** Move me to a numerics file **)
Lemma reduceReduce q : Qred (D_to_Q (Dred q)) = Qred (D_to_Q q).
Proof.
  rewrite (Qred_complete (D_to_Q q) (D_to_Q (Dred q))) => //.
  by rewrite Dred_correct.
Qed.

(** Here's a description of the compilation algorithm: 

  Source Language
  Binary Arithmetic Operations
    b ::= + | - | *
  Expressions
    e ::= q            (* rationals *)
        | -e           (* arithmetic negation *)
        | weight a     (* weight of action [a] *)
        | cost a       (* cost of action [a] *)
        | eps          (* the epsilon parameter *)
        | e b e        (* binary operations *)
  Commands
    c ::= skip
        | update f     (* update weights by (f : A -> e) *) 
        | recv         (* receive a cost vector from the environment *)
        | send         (* send an action ~ w / (\sum_(a : A) w a) *)
        | c1; c2       
        | iter n c     (* iterate c n-times *)

  Target Language (over game type A):
    The same as the source language, but with new semantics operating
    over compilable states. 
      s := { (* Compilable: *)
             cur_costs : M.t A Q     (* the current cost vector, mapping actions to costs *)   
           ; prev_costs : seq (M.t A Q)
           ; weights : M.t A Q       (* the weights table, mapping actions to weights *)
           ; eps : Q                 (* the parameter \epsilon *)

             (* Logical: *)
           ; outputs : seq (dist A rat_realFieldType) }.
    
    We make a few assumptions about the game type A, in order to use 
    actions as keys in the maps [cur_costs] and [weights]. In particular,  
    that it has an order that satisfies: OrderedType.OrderedType.   
 *)

Definition zero : Q := 0.
Definition one : Q := 1.
Definition two : Q := Qmake 2 1.
    
(* The package provided by the client network oracle to MWU *)
Class ClientOracle {A} :=
  mkOracle { T : Type (* oracle private state *)
           ; oracle_init_state : T
           ; oracle_chanty : Type
           ; oracle_bogus_chan : oracle_chanty
           ; oracle_prerecv : T -> oracle_chanty -> bool * T
           ; oracle_recv : T -> oracle_chanty -> (list (A*D) * T)
           ; oracle_presend : T -> list (A*D) -> bool
           ; oracle_send : T -> list (A*D) -> (oracle_chanty * T)
           ; oracle_recv_ok : forall st ch st',
               oracle_prerecv st ch = (true, st') ->
               forall a,
               exists d,
                 [/\ In (a,d) (oracle_recv st' ch).1
                   , Dle (-D1) d & Dle d D1]
           ; oracle_recv_nodup : forall st ch st',
               oracle_prerecv st ch = (true, st') ->
               NoDupA (fun p q => p.1 = q.1) (oracle_recv st' ch).1
           }.

(** * Program *)

Module MWUPre (A : MyOrderedType).
  Module A' := OrderedType_of_MyOrderedType A.
  Module M := Make A'.
  Module MFacts := Facts M.
  Module MProps := Properties M.

  Definition cGamma (weights : M.t D) : Q :=
    D_to_Q (M.fold (fun a q acc => Dadd q acc) weights (DD (Dmake 0 1))).

  Section mwu.
    Variable num_players : nat.
    Context `{Showable A.t}.
    Context `{Enumerable A.t}.    
    (** Assume an oracle over the provided GameType *)
    Context `{oracle : ClientOracle A.t}.

    Record cstate : Type :=
      mkCState
        { SCosts : M.t D (* the current cost vector *)
        ; SPrevCosts : list (M.t D)
        ; SWeights : M.t D
        ; SEpsilon : D (* epsilon -- a parameter *)
        (* the history of the generated distributions over actions *)                     
        ; SOutputs : list (A.t -> Q)
        ; SChan : oracle_chanty
        ; SOracleSt : T }.

    (** Send weights to the network. *)
    Definition mwu_send (m : M.t D) (oracle_st : T) : (oracle_chanty * T) :=
      oracle_send oracle_st (M.elements m).

    (* Receive a cost vector (a map) from the network. *)
    Definition mwu_recv : oracle_chanty -> T -> (M.t D * T) :=
      fun ch => fun st =>
        let (l, st') := oracle_recv st ch in
        let l':= print_Dvector l l in
        (MProps.of_list l', st').

    Definition eval_binopc (b : binop) (v1 v2 : D) : D :=
      match b with
      | BPlus => Dadd v1 v2
      | BMinus => Dsub v1 v2                      
      | BMult => Dmult v1 v2
      end.
    
    Fixpoint evalc (e : expr A.t) (s : cstate) : option D :=
      match e with
      | EVal v =>
        match v with
        | QVal q => Some q
        end
      | EOpp e' =>
        match evalc e' s with
        | Some v' => Some (Dopp v')
        | None => None
        end
      | EWeight a => M.find a (SWeights s)
      | ECost a => M.find a (SCosts s)
      | EEps => Some (SEpsilon s)
      | EBinop b e1 e2 =>
        let: v1 := evalc e1 s in
        let: v2 := evalc e2 s in
        match v1, v2 with
        | Some v1', Some v2' => Some (eval_binopc b v1' v2')
        | _, _ => None
        end
      end.

    (*NOTE: This code is much complicated by the fact that [evalc] can
    fail -- otherwise, we could just use [M.mapi].*)
    Definition update_weights
               (f : A.t -> expr A.t) (s : cstate)
      : option (M.t D) :=
      M.fold
        (fun a _ acc =>
           match acc with
           | None => None
           | Some acc' =>
             match evalc (f a) s with
             | None => None
             | Some q =>
               if Dlt_bool D0 q then Some (M.add a (Dred q) acc')
               else None
             end
           end)
        (SWeights s)
        (Some (M.empty D)).

    Definition weights_distr (weights : M.t D) : A.t -> Q := 
      fun a : A.t =>
        match M.find a weights with
        | None => 0
        | Some d => D_to_Q d / cGamma weights
        end.
    
    Fixpoint interp (c : com A.t) (s : cstate) : option cstate :=
      match c with
      | CSkip => Some s
      | CUpdate f =>
        let w := update_weights f s
        in match w with
           | None => None
           | Some w' => 
             Some (mkCState
                     (SCosts s)
                     (SPrevCosts s)
                     w'
                     (SEpsilon s)
                     (SOutputs s)
                     (SChan s)
                     (SOracleSt s))
           end
      | CRecv =>
        let (b, st') := oracle_prerecv (SOracleSt s) (SChan s) in
        if b then                               
          let (c, st'') := mwu_recv (SChan s) st'
          in Some (mkCState
                     c
                     (SCosts s :: SPrevCosts s)
                     (SWeights s)
                     (SEpsilon s)
                     (SOutputs s)
                     (SChan s)
                     st'')
        else None
      | CSend =>
        if oracle_presend (SOracleSt s) (M.elements (SWeights s))
        then 
          let (ch, st') := mwu_send (SWeights s) (SOracleSt s) in
          let d := weights_distr (SWeights s)
          in Some (mkCState
                     (SCosts s)
                     (SPrevCosts s)
                     (SWeights s)
                     (SEpsilon s)
                     (d :: SOutputs s)
                     ch
                     st')
        else None
      | CSeq c1 c2 =>
        match interp c1 s with
        | None => None
        | Some s' => interp c2 s'
        end
      | CIter n c =>
        (*NOTE: We could further short-circuit this iteration -- in practice, 
        it shouldn't matter for performance since [interp] should never
        fail on MWU, starting in appropriate initial state.*)
        N.iter
          n
          (fun s =>
             match s with
             | None => None
             | Some s' => interp c s'
             end)
          (Some s)
      end.

    Section init.
      Context `{Enumerable A.t}.

      Definition init_map : M.t D :=
        MProps.of_list (List.map (fun a => (a, D1)) (enumerate A.t)).

      Definition init_cstate (epsQ : D) :=
        @mkCState
          init_map (** The initial cost function is never used -- 
                     we only include it because the type [state] forces 
                     an [SCost] projection. *)
          [::]
          init_map
          epsQ
          [::]
          oracle_bogus_chan
          oracle_init_state.
    End init.

    (* Context `{Enumerable A.t}. *)
    Definition mwu (eps : D) (nx : N.t) : option cstate :=
      interp (mult_weights A.t nx) (init_cstate eps).
  End mwu.
End MWUPre.

(* Note [MWU_Type]: 
   ~~~~~~~~~~~~~~~~
   The following module type is used in: 
     - wenetwork.v
     - we2wl.v 
   to unify the module instantiations of MWU built in the MWUProof 
   functor (below) and the WE_NodePkg functor (defined in we2wl.v). *)

Module Type MWU_Type.
  Declare Module A : MyOrderedType.
  Module MWUPre := MWUPre A.
  Include MWUPre.
End MWU_Type.
  
Module MWU (A : MyOrderedType) <: MWU_Type.
  Module A := A.
  Module MWUPre := MWUPre A. Include MWUPre.
End MWU.  

Module MWUProof (T : MyOrderedType) (MWU : MWU_Type with Module A := T).
  Module A := T.
  Module M := MWU.M.
  Module MFacts := Facts M.
  Module MProps := Properties M.
  
  Import MWU.

  Section OrderedFinType_Section.
    Variables
      (eq_mixin : Equality.mixin_of A.t)
      (choice_mixin : choiceMixin (EqType A.t eq_mixin))
      (fin_mixin : Finite.mixin_of (ChoiceType (EqType A.t eq_mixin) choice_mixin)).
      
  Definition t : finType :=
    FinType (ChoiceType (EqType A.t eq_mixin) choice_mixin) fin_mixin.
  
  Lemma InA_ext A (P Q : A -> A -> Prop) l x :
    (forall a b, P a b <-> Q a b) ->
    InA P x l <-> InA Q x l.
  Proof.
    move => H; elim: l.
    { split; inversion 1. }
    move => a l IH; split; inversion 1; subst.
    { by constructor; rewrite -H. }
    { by apply: InA_cons_tl; rewrite -IH. }
    { by constructor; rewrite H. }
    by apply: InA_cons_tl; rewrite IH.
  Qed.
  
  Lemma NoDupA_ext A (P Q : A -> A -> Prop) l :
    (forall a b, P a b <-> Q a b) ->
    NoDupA P l <-> NoDupA Q l.
  Proof.
    elim: l => // a l IH H; split; inversion 1; subst.
    { constructor.
      move => H5; apply: H3; rewrite InA_ext => //.
      apply: H5.
      by rewrite -IH. }
    constructor => //.
    move => H5; apply: H3; rewrite InA_ext => //.
    apply: H5.
    by move => ax b; rewrite -H.
    rewrite IH => //.
  Qed.

  Section mwuProof.
    Variable num_players : nat.
    Context `{showable_instance : Showable A.t}.
    Context `{enumerable_instance : Enumerable A.t}.    
    (** Assume an oracle over the provided GameType *)
    Context `{coracle : ClientOracle A.t}.
    (** An alias used below: *)
    Definition oracle_cT : Type := (T (ClientOracle := coracle)).
    
    Lemma recv_ok :
      forall st ch st', oracle_prerecv st ch = (true, st') -> 
      forall a,
      exists d,
        [/\ M.find a (mwu_recv ch st').1 = Some d
          , Dle_bool (-D1) d & Dle_bool d D1].
    Proof.
      rewrite /mwu_recv.
      move => st ch st' Hpre a'.
      have H: NoDupA (M.eq_key (elt:=D)) (oracle_recv st' ch).1.
      { generalize (oracle_recv_nodup (ClientOracle:=coracle) Hpre) => H.
        rewrite NoDupA_ext; first by apply: H.
        rewrite /M.eq_key /M.Raw.Proofs.PX.eqk => a b.
          by rewrite -A.eqP. }
      move: a' => a.      
      case: (oracle_recv_ok Hpre a) => q []H2 H3.      
      exists q; split => //.
      2: { by rewrite <-Dle_bool_iff in H3; rewrite H3. }
      2: { by rewrite <-Dle_bool_iff in p; rewrite p. }
      destruct (oracle_recv st' ch).
      rewrite MProps.of_list_1b => //.
      move: H H2 {H3 p}; rewrite print_Dvector_id;
       generalize (oracle_recv (ClientOracle:=coracle) st ch) a q.
      move=> _ /=. move: l.
      elim => // [][]a' q' l' IH a0 q0; inversion 1; subst; case.
      { case => -> -> /=.
        have ->: MProps.F.eqb a0 a0 = true.
        { rewrite /MProps.F.eqb.
          case: (MProps.F.eq_dec a0 a0) => //.
            by rewrite -A.eqP. }
          by []. }
      simpl.
      case H4: (MProps.F.eqb a0 a').
      { move => H5.
        rewrite /MProps.F.eqb in H4.
        move: H4.
        case: (MProps.F.eq_dec a0 a') => //.
        rewrite -A.eqP => Hx; subst a'.
        clear - H2 H5.
        elim: l' H2 H5 => // a1 l IH H6 H7.
        destruct H7.
        { inversion H; subst. clear H0.
          elimtype False.
          apply: H6.
          by left; rewrite /M.eq_key /M.Raw.Proofs.PX.eqk /= -A.eqP. }
        move => _; apply: IH => //.
        by move => H7; apply: H6; right. }
      by move => H5; apply: (IH _ _ H3 H5).
      by rewrite print_Dvector_id.
    Qed.

  Definition match_maps
             (s : {ffun t -> rat})
             (m : M.t D) : Prop :=
    forall a,
    exists q, M.find a m = Some q /\ Qred (D_to_Q q) = rat_to_Q (s a).
  
  Definition match_costs
             (s : {c : {ffun t -> rat} & forall a : t, (`|c a| <= 1)%R})
             (m : M.t D) : Prop :=
    match_maps (projT1 s) m.
  
  Inductive match_costs_seq :
    seq {c : {ffun t -> rat} & forall a : t, (`|c a| <= 1)%R} ->
    list (M.t D) ->
    Prop :=
  | match_costs_nil :
      match_costs_seq nil nil
  | match_costs_cons :
      forall s ss m mm,
        match_costs s m ->
        match_costs_seq ss mm ->
        match_costs_seq [:: s & ss] [:: m & mm].

  Inductive match_distrs :
    seq (dist t rat_realFieldType) ->
    seq (t -> Q) ->
    Prop :=
  | match_distrs_nil :
      match_distrs nil nil
  | match_distrs_cons :
      forall d f l l',
        pmf d = finfun (fun a => Q_to_rat (f a)) ->
        match_distrs l l' ->
        match_distrs [:: d & l] [:: f & l'].

  (** The high-level oracle *)
  Context oracle_T  `{oracle: weightslang.ClientOracle t oracle_T oracle_chanty}.
  Notation "'state' t" := (@state t oracle_T oracle_chanty) (at level 50).

  (** and its match relation *)
  Variable match_oracle_states : oracle_T -> oracle_cT -> Prop.

  (** The oracular compilation interface *)
  Class match_oracles : Prop :=
    mkMatchOracles {
      match_oracle_recv : forall (ct ct' : oracle_cT) (t : oracle_T) s ch,
        match_oracle_states t ct ->
        oracle_prerecv ct ch = (true, ct') ->  
        let: (m, ct'') := mwu_recv ch ct' in
        match_maps s m -> 
        exists t',
        [/\ weightslang.oracle_recv t ch s t'
          & match_oracle_states t' ct'']

    ; match_oracle_send :
        forall (ct : oracle_cT) (tx : oracle_T) m
               (s : {ffun t -> rat}) (s_ok : forall a : t, (0 < s a)%R)
               a0 eps (eps_ok : (0 < eps <= 1 / 2%:R)%R),
        match_oracle_states tx ct ->
        match_maps s m ->
        oracle_presend ct (MProps.to_list m) = true ->
        let: (ch, ct') := mwu_send m ct in
        let: d := p_aux_dist a0 eps_ok s_ok (cs:=[::]) (CMAX_nil (A:=t)) in
        exists t',
        [/\ weightslang.oracle_send tx d ch t'
          & match_oracle_states t' ct' ]
    }.

  Context (Hmatch_ora : match_oracles).
  
  Inductive match_states : state t -> cstate -> Prop :=
  | mkMatchStates :
      forall s m s_ok ss mm w w_ok wc eps eps_ok epsc outs outs' ch
             oracle_st coracle_st,
        match_maps s m ->
        match_costs_seq ss mm ->
        match_maps w wc ->
        rat_to_Q eps = Qred (D_to_Q epsc) ->
        match_distrs outs outs' ->
        match_oracle_states oracle_st coracle_st ->
        match_states
          (@mkState _ _ _ s s_ok ss w w_ok eps eps_ok outs ch oracle_st)
          (@mkCState _ m mm wc epsc outs' ch coracle_st).

  Definition eval_binopc (b : binop) (v1 v2 : D) :=
    match b with
    | BPlus => Dadd v1 v2
    | BMinus => Dsub v1 v2
    | BMult => Dmult v1 v2
    end.
  
  Fixpoint evalc (e : expr t) (s : cstate) : option D :=
    match e with
    | EVal v =>
      match v with
      | QVal q => Some q
      end
    | EOpp e' =>
      match evalc e' s with
      | Some v' => Some (Dopp v')
      | None => None
      end
    | EWeight a => M.find a (SWeights s)
    | ECost a => M.find a (SCosts s)
    | EEps => Some (SEpsilon
                      (oracle:=coracle)
                      s)
    | EBinop b e1 e2 =>
      let: v1 := evalc e1 s in
      let: v2 := evalc e2 s in
      match v1, v2 with
      | Some v1', Some v2' => Some (eval_binopc b v1' v2')
      | _, _ => None
      end
    end.

  Fixpoint cGamma'_aux (l : list (M.key * D)) :=
    match l with
    | nil => D0
    | a :: l' => Dadd a.2 (cGamma'_aux l')
    end.

  Lemma cGamma_cGamma'_aux l :
    fold_right
      (fun y : M.key * D => [eta Dadd y.2])
      D0
      l =
    cGamma'_aux l.
  Proof. elim: l => // a l IH /=; rewrite IH. Qed.

  Definition cGamma' m :=
    D_to_Q (cGamma'_aux (List.rev (M.elements m))).
  
  Lemma cGamma_cGamma' m :
    cGamma m = cGamma' m.
  Proof. by rewrite /cGamma /cGamma' M.fold_1 -fold_left_rev_right. Qed.
  
  Definition gamma' (l : seq t) (s : {ffun t -> rat}) : rat :=
    \sum_(a <- l) (s a)%R.

  Lemma gamma'_cons x l s :
    (gamma' (x :: l) s = s x + gamma' l s)%R.
  Proof. by rewrite /gamma' big_cons. Qed.

  Lemma gamma_gamma' w : gamma' (index_enum t) w = gamma w.
  Proof. by []. Qed.
    
  Lemma match_maps_gamma_cGamma'_aux
        (s : {ffun t -> rat})
        (l : list (M.key * D)) :
    (forall a q, In (a, q) l -> rat_to_Q (s a) = Qred (D_to_Q q)) ->
    gamma' (List.map (fun x => x.1) l) s = Q_to_rat (D_to_Q (cGamma'_aux l)).
  Proof.
    elim: l s => //.
    { move => s /= IH; rewrite /gamma' /= big_nil.
      rewrite DO_to_Q0' /Q_to_rat /= fracqE /=.
      by rewrite GRing.mul0r. }
    case => a q l IH s /= H.
    symmetry.
    apply: rat_to_QK2.
    rewrite gamma'_cons Dadd_ok IH.
    { have ->: s a = Q_to_rat (D_to_Q q).
      { move: (H _ _ (or_introl erefl)) => H2.
        rewrite (rat_to_QK2 (r:=s a)) => //.
        by rewrite -(Qred_correct (D_to_Q q)) H2. }
      rewrite rat_to_Q_plus 2!rat_to_QK1.
      by rewrite 2!Qred_correct. }
    move => ax qx H2.
    by apply: (H _ _ (or_intror H2)).
  Qed.

  Lemma InA_notin a (l : seq t) : ~InA A.eq a l -> a \notin l.
  Proof.
    elim: l a => // a l IH ax H; rewrite /in_mem /=; apply/negP; case/orP.
    { by move/eqP => H2; subst ax; apply: H; left; rewrite -A.eqP. }
    move => H2; apply: H; right.
    case: (InA_dec A.eq_dec ax l) => // H3; move: (IH _ H3).
    by rewrite /in_mem /= H2.
  Qed.

  Lemma notin_InA a (l : seq t) : a \notin l -> ~InA A.eq a l.
  Proof.
    elim: l a => //.
    { move => a _; inversion 1. }
    move => a l IH ax H; rewrite /in_mem /=; inversion 1; subst.
    { move: H2; rewrite -A.eqP => H3; subst ax; clear H0.
      by rewrite in_cons in H; move: (negP H); apply; apply/orP; left. }
    apply: IH; last by apply: H2.
    by move: (negP H) => H3; apply/negP => H4; apply: H3; apply/orP; right.
  Qed.
  
  Lemma InA_not_InA_eq x y (l : seq t) : InA A.eq x l -> ~InA A.eq y l -> x<>y.
  Proof.
    elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H.
    { move => H2 H3; subst y.
        by apply: H2; left. }
    move => H2 H3; subst x.
    by apply: H2; right.
  Qed.

  Lemma InA_map A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) x l (f : A -> B) :
    (forall x y, Aeq x y -> Beq (f x) (f y)) ->
    InA Aeq x l ->
    InA Beq (f x) (List.map f l).
  Proof.
    move => H; elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H0.
    { by left; apply: H. }
      by simpl; right; apply: (IH H2).
  Qed.

  Lemma InA_map' A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) x l (f : A -> B) :
    (forall x y, Beq (f x) (f y) -> Aeq x y) ->
    InA Beq (f x) (List.map f l) ->
    InA Aeq x l.
  Proof.
    move => H; elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H0.
    { by left; apply: H. }
      by simpl; right; apply: (IH H2).
  Qed.
  
  Lemma NoDupA_map A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) l (f : A -> B) :
    (forall x y, Beq (f x) (f y) -> Aeq x y) ->
    NoDupA Aeq l ->
    NoDupA Beq (List.map f l).
  Proof.
    move => H; induction 1; first by constructor.
    simpl; constructor => // H2; apply: H0.
    by apply: (InA_map' H).
  Qed.
      
  Lemma match_maps_find1 T (x : t) m q :
    M.find (elt:=T) x m = Some q ->
    (count_mem x) (List.map [eta fst] (List.rev (M.elements (elt:=T) m))) = 1%N.
  Proof.
    move: (M.elements_3w m); move/NoDupA_rev => H H2.
    have H3: InA A.eq x (List.map [eta fst] (List.rev (M.elements (elt:=T) m))).
    { have H3: M.find (elt:=T) x m <> None.
      { move => H3; rewrite H3 in H2; congruence. }
      clear H2; move: H3; rewrite -MProps.F.in_find_iff MProps.F.elements_in_iff.
      case => e; move: (M.elements _) => l; clear H => H.
      have ->: x = fst (x, e) by [].
      have H2: InA (M.eq_key_elt (elt:=T)) (x, e) (List.rev l).
      { by rewrite InA_rev. }
      have H3: forall x y : M.key * T, M.eq_key_elt x y -> A.eq x.1 y.1.
      { by case => x1 x2; case => y1 y2; case. }
      by apply (InA_map H3 H2). }
    have H4: NoDupA A.eq (List.map [eta fst] (List.rev (M.elements (elt:=T) m))).
    { move: (H2); rewrite -MProps.F.find_mapsto_iff MProps.F.elements_mapsto_iff => H4.
      clear - H; apply: (NoDupA_map _ H); case => x1 x2; case => y1 y2 //. }
    clear H.
    move: H3 H4; move: (List.map _ _) => l.
    clear H2 m q.
    elim: l => //.
    { inversion 1. }
    move => a l' IH; inversion 1; subst.
    { clear H3.
      inversion 1; subst.
      simpl.
      move: H0; rewrite -A.eqP => ->.
      have [a' Hx]: exists a' : t, a = a'.
      { by exists a. }
      have [l'' Hl]: exists l'' : seq t, l' = l''.
      { by exists l'. }
      subst a l'.
      have ->: (count_mem a') l'' = 0%N.
      { have H5: a' \notin l'' by apply: InA_notin.
        apply: (count_memPn H5). }
      by rewrite addn0 eq_refl. }
    inversion 1; subst => /=.
    have [a' Hx]: exists a' : t, a = a'. { by exists a. }
    have [l'' Hl]: exists l'' : seq t, l' = l''. { by exists l'. } subst a l'.
    have ->: a' == x = false.
    { move: (InA_not_InA_eq H0 H2) => H6.
      case H7: (a' == x) => //.
      move: (eqP H7) => H8; subst x; contradiction. }
    rewrite IH => //.
  Qed.
  
  Lemma match_maps_enum_count_mem s m :
    match_maps s m ->
    forall x : t,
    (count_mem x) (index_enum t) =
    (count_mem x) (List.map [eta fst] (List.rev (M.elements (elt:=D) m))).
  Proof.
    move => H x; case: (H x) => q []H1 H2; move {H}; rewrite (@enumP t x).
    by rewrite (match_maps_find1 H1).
  Qed.
  
  Lemma match_maps_enum_perm_eq s m :
    match_maps s m ->
    perm_eq (index_enum t)
            (List.map [eta fst] (List.rev (M.elements m))).
  Proof.
    move => H; rewrite /perm_eq; apply/allP => x.
    by rewrite mem_cat; case/orP => /= H2;
       apply/eqP; apply: match_maps_enum_count_mem.
  Qed.
  
  Lemma match_maps_gamma'_elements s m :
    match_maps s m ->
    gamma' (index_enum t) s =
    gamma' (List.map [eta fst] (List.rev (M.elements m))) s.
  Proof.
    rewrite /gamma' /match_maps => H; apply: eq_big_perm.
    by apply: (match_maps_enum_perm_eq H).
  Qed.
    
  Lemma match_maps_gamma_cGamma s m :
    match_maps s m ->
    gamma s = Q_to_rat (cGamma m).
  Proof.
    rewrite cGamma_cGamma' -(gamma_gamma' s).
    move => H; rewrite -(match_maps_gamma_cGamma'_aux (s:=s)).
    { apply: match_maps_gamma'_elements => //. }
    move => a q H2.
    case: (H a) => q' []H3 H4.
    have H5: In (a,q) (M.elements m).
    { by rewrite in_rev. }
    clear H2; have ->: q = q'.
    { move: H3; rewrite -MProps.F.find_mapsto_iff => H3.
      have H6: InA (M.eq_key_elt (elt:=D)) (a, q) (M.elements m).
      { apply: In_InA => //. }
      move: H6; rewrite -MProps.F.elements_mapsto_iff => H6.
      apply: MProps.F.MapsTo_fun; first by apply: H6.
      apply: H3. }
    by rewrite H4.
  Qed.

  Fixpoint update_weights'_aux
             (f : t -> expr t) (s : cstate) w l
    : option (M.t D) :=
    match l with
    | nil => Some w
    | a :: l' =>
      match evalc (f a) s with
      | None => None
      | Some q =>
        if Dlt_bool D0 q then 
          match (update_weights'_aux f s w l') with
             | None => None
             | Some m => Some (M.add a (Dred q) m)
          end
        else None
      end
    end.

  Lemma update_weights'_aux_app f s w l1 l2 :
    update_weights'_aux f s w (l1 ++ l2) =
    match update_weights'_aux f s w l2 with
    | None => None
    | Some w' => update_weights'_aux f s w' l1
    end.
  Proof.
    elim: l1 l2 w => //=.
    { move => l2 w; case: (update_weights'_aux _ _ _ _) => //. }
    move => a l IH l2 w; move: IH.
    case H2: (update_weights'_aux _ _ _ l2) => [w'|].
    { move => IH.
      case: (evalc (f a) s) => // x.
      case: (Dlt_bool D0 x) => //.
      by rewrite IH H2. }
    move => ->; rewrite H2.
    case: (evalc (f a) s) => //.
    move => a0; case: (Dlt_bool D0 a0) => //.
  Qed.
  
  Definition update_weights'
             (f : t -> expr t) (s : cstate)
    : option (M.t D) :=
    update_weights'_aux f s (M.empty D)
      (List.map (fun x => x.1) (List.rev (M.elements (SWeights s)))).

  Lemma update_weights'_aux_inv f s m l m' :
    update_weights'_aux f s m l = Some m' ->
    forall a,
      In a l ->
      exists q,
        [/\ M.find a m' = Some (Dred q)
          , evalc (f a) s = Some q
          & Dlt D0 q].
  Proof.
    elim: l m m' => // a l IH m m' /=.
    case H: (evalc _ _) => // [q].
    case H2: (Dlt_bool D0 q) => //.
    case H3: (update_weights'_aux _ _ _ _) => // [m''] H4 a' H5.
    case: H5.
    { move => H6; subst a'; inversion H4; subst.
      rewrite MProps.F.add_eq_o.
      { exists q.
        split => //.
        by rewrite -Dlt_bool_iff. }
      rewrite /A.eq.
      by rewrite -A.eqP.
    }
    move => H5.
    case: (IH _ _ H3 _ H5) => q' []H6 H7 H8.
    case: (A.eq_dec a a').
    { rewrite -A.eqP => H9. subst a'.
      exists q; split => //.
      inversion H4; subst.
      rewrite MProps.F.add_eq_o; last by rewrite /A.eq -A.eqP.
      by [].
      by rewrite -Dlt_bool_iff.  
    }
    move => H9.
    exists q'.
    split => //.
    inversion H4; subst.
    rewrite MProps.F.add_neq_o => //.
  Qed.

  Lemma update_weights'_inv1 f s m :
    (forall a, exists q, M.find a (SWeights s) = Some q) ->
    update_weights' f s = Some m ->
    forall a,
    exists q,
      [/\ M.find a m = Some (Dred q)
        , evalc (f a) s = Some q
        & Dlt D0 q].
  Proof.
    rewrite /update_weights' => H H2 a.
    have H3: In a (List.map [eta fst] (List.rev (M.elements (SWeights s)))).
    { clear - H.
      case: (H a) => q H2.
      have H3: M.find a (SWeights s) <> None.
      { move => H4; rewrite H4 in H2; congruence. }
      move: H3; rewrite -MProps.F.in_find_iff MProps.F.elements_in_iff.
      case => q'; move: (M.elements _) => l.
      elim: l => //=.
      { inversion 1. }
      case => []a' b l IH /=.
      inversion 1; subst.
      { destruct H1; simpl in *; subst.
        move: H0; rewrite /A.eq -A.eqP => H3; subst a'.
        have ->: a = (a, b).1 by [].
        apply: in_map.
        apply: in_or_app.
        right.
        left => //. }
      move: (IH H1).
      rewrite in_map_iff; case; case => a'' b' /=; case => -> H3.
      have ->: a = (a, b').1 by [].
      apply: in_map.
        by apply: in_or_app; left. }
    apply: (update_weights'_aux_inv H2 H3).
  Qed.

  Lemma update_weights_weights'_aux f s l w :
    fold_right
     (fun (y : M.key * D) (x : option (M.t D)) =>
      match x with
      | Some acc' =>
          match evalc (f y.1) s with
          | Some q =>
            if Dlt_bool D0 q then  Some (M.add y.1 (Dred q) acc')
            else None
          | None => None
          end
      | None => None
      end) (Some w) l =
    update_weights'_aux f s w (List.map [eta fst] l).
  Proof.
    move: w; elim: l => // [][]a b l IH.
    move => w /=; rewrite IH.
    case: (update_weights'_aux _ _ _ _) => //.
    case: (evalc _ _) => // q''.
    case: (Dlt_bool D0 q'') => //.
  Qed.
    
  Lemma update_weights_weights' f s :
    update_weights f s = update_weights' f s.
  Proof.
    rewrite /update_weights /update_weights' M.fold_1 -fold_left_rev_right.
    apply: update_weights_weights'_aux.
  Qed.
    
  Lemma update_weights_inv1 f s m :
    (forall a, exists q, M.find a (SWeights s) = Some q) ->
    update_weights f s = Some m ->
    forall a,
    exists q,
      [/\ M.find a m = Some (Dred q)
        , evalc (f a) s = Some q
        & Dlt D0 q].
  Proof.
    rewrite update_weights_weights'.
    apply: update_weights'_inv1.
  Qed.

  Lemma match_eval f (r : state t) (s : cstate) q :
    match_maps (weightslang.SWeights r) (SWeights s) ->
    match_maps (weightslang.SCosts r) (SCosts s) ->
    rat_to_Q (weightslang.SEpsilon r) = Qred (D_to_Q (SEpsilon s)) ->
    forall a : t,
      evalc (f a) s = Some q ->
      Qred (D_to_Q q) = rat_to_Q (eval (f a) r).
  Proof.
    move => H Hx Hy a; move: (f a) => e.
    elim: e q.
    { move => v q /=.
      case: v => // q'.
      inversion 1; subst.
        by rewrite rat_to_QK1. }
    { move => e IH q.
      unfold evalc; fold evalc.
      case H2: (evalc e s) => // [q']; inversion 1; subst.
      rewrite Dopp_ok Qred_opp IH => //.
      by rewrite rat_to_Qopp. }
    { move => a' q H2.
      simpl in H2.
      case: (H a') => q' []H3 H4.
      rewrite H3 in H2; inversion H2; subst. clear H2.
      by rewrite H4. }
    { move => a' q H2.
      simpl in H2.
      case: (Hx a') => q' []H3 H4.
      rewrite H3 in H2; inversion H2; subst. clear H2.
      by rewrite H4. }
    { move => q /=; inversion 1; subst.
      by rewrite Hy. }
    move => b e1 IH1 e2 IH2 q.
    rewrite /evalc -/evalc.
    case H1: (evalc e1 s) => // [v1].
    case H2: (evalc e2 s) => // [v2].
    inversion 1; subst. clear H0.
    (*case analysis on the binary operations*)
    case: b; rewrite /eval_binopc /eval_binop.
    { rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_plus.
      rewrite -(IH1 _ H1).
      rewrite -(IH2 _ H2).
      by rewrite 2!Qred_correct Dadd_ok. }
    { rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_plus.
      rewrite -(IH1 _ H1).
      rewrite rat_to_Qopp.
      rewrite -(IH2 _ H2).
      by rewrite 2!Qred_correct Dadd_ok Dopp_ok. }
    rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_mul.
    rewrite -(IH1 _ H1).
    rewrite -(IH2 _ H2).
    by rewrite 2!Qred_correct Dmult_ok.
  Qed.
  
  Lemma update_weights_inv2 (f : t -> expr t) r s m :
    match_states r s ->
    update_weights f s = Some m ->
    forall a : t,
    exists q,
      [/\ M.find a m = Some (Dred q)
        , evalc (f a) s = Some q
        , Qred (D_to_Q q) = rat_to_Q (eval (f a) r)
        & Qlt 0 (D_to_Q q)].
  Proof.
    move => H H2 a.
    move: (@update_weights_inv1 f s m) => Hinv1.
    move: (@match_eval f r s) => Hmatch.
    case: s H H2 Hinv1 Hmatch; intros.
    inversion H; subst.
    have H3: forall a, exists q, M.find a SWeights0 = Some q.
    { move => a'; case: (H11 a') => q []H3 H4; exists q => //. }
    case: (Hinv1 H3 H2 a) => q []H1 H4 H5.
    exists q; split => //.
    apply: Hmatch => //.
    rewrite /Dlt in H5.
    clear - H5. move: H5.
    by rewrite D_to_Q0.
  Qed.
  
  Lemma match_maps_update_weights (f : t -> expr t) r s m :
    match_states r s ->
    update_weights f s = Some m ->
    match_maps [ffun a => eval (f a) r] m /\
    (forall a, 0 < eval (f a) r)%R.
  Proof.
    move => H H2; split => a; case: (update_weights_inv2 H H2 a) => q.
    { case => H3 H4 H5 H6.
      exists (Dred q); split => //.
      rewrite reduceReduce.
      by rewrite H5 ffunE. }
    case => H3 H4 H5 H6.
    have H7: 0 < Qred (D_to_Q q) by rewrite Qred_correct.
    rewrite H5 in H7; clear - H7.
    have H6: 0 = inject_Z 0 by [].
    rewrite H6 -rat_to_Q0 in H7.
    by apply: rat_to_Q_lt'.
  Qed.

  Variable a0 : t.


  Lemma interp_step_plus :
    forall (s : state t) (tx tx' : cstate) (c : com t),
      interp c tx = Some tx' ->
      match_states s tx ->
      exists c' s',
        final_com c' /\
        ((c=CSkip /\ s=s') \/ step_plus a0 c s c' s') /\
        match_states s' tx'.
  Proof.
    intros s t t' c H; revert s t t' H; induction c; simpl.
    { intros s t t'; inversion 1; subst.
      intros H2.
      exists CSkip, s.
      split; [solve[constructor; auto]|].
      split; auto. }
    { intros s t t' H H2.
      move: (@match_maps_update_weights e s t) H.
      case: (update_weights e t) => // m; move/(_ m) => H3.
      inversion 1; subst; clear H.
      generalize H2 => H2'.
      inversion H2; subst; simpl in *; clear H2.
      move: (H3 H2' erefl) => H5x; clear H3.
      exists CSkip.
      eexists.
      split => //.
      split.
      { right.
        constructor.
        constructor. }
      simpl.
      move: H6 => Hora.
      case: H5x => H5x H6.
      constructor => //.
      Unshelve.
      move: H6 => Hora.
      by case: H5x => H5x H6 a; move: (H6 a); rewrite ffunE. }
    { intros s tx t'; inversion 1; subst. clear H.
      intros H2.
      remember (oracle_prerecv (SOracleSt tx) (SChan tx)) as p.
      destruct p as [b c'].
      set c := mwu_recv (SChan tx) c'.
      set f :=
        finfun
          (fun a : t =>
             match M.find a c.1 with
             | None => 0%R (*bogus*)
             | Some q => Q_to_rat (Qred (D_to_Q q))
             end).
      have pf: forall a, (`|f a| <= 1)%R.
      { move => a.
        rewrite /f ffunE /c'.
        move: Heqp H1.
        case: b => Heqp H1 //.
        symmetry in Heqp.
        move: (recv_ok Heqp a) => Hpre.
        destruct Hpre as [d Hpre]; inversion Hpre.
        rewrite /c. rewrite H.
        rewrite -Q_to_rat1 (ler_norml _ _).
        apply /andP; split.
        { rewrite -Q_to_rat_opp.
          apply: Q_to_rat_le.
          move: (Qred_correct (D_to_Q d)) ->.
          apply: Qle_bool_imp_le.
          by move: H0; rewrite /Dle_bool Dopp_ok D_to_Q1. }
        apply: Q_to_rat_le.
        move: (Qred_correct (D_to_Q d)) ->.
        apply: Qle_bool_imp_le.
        by move: H3; rewrite /Dle_bool D_to_Q1. }
      exists CSkip.
      have Hora: match_oracle_states (weightslang.SOracleSt s) (SOracleSt tx).
      { by case: H2. }
      move: H1 Heqp.
      case: b => //.
      case Hrecv': (mwu_recv (SChan tx) c') => [m tx'] HSomeEq Hpre.
      symmetry in Hpre.
      have Hmaps: match_maps f m.
      { rewrite /match_maps/f => a; rewrite ffunE.
        case: (recv_ok Hpre a) => q []Hx Hy Hz.
        rewrite Hrecv' /= in Hx.
        rewrite /c Hx Hrecv' Hx.
        exists q; split => //.
        by rewrite rat_to_QK1 Qred_idem. }
      generalize (match_oracle_recv f Hora Hpre); rewrite Hrecv'.
      move/(_ Hmaps); case => sx' []Hrecv Hora_states.
      exists
        (@mkState
           _
           _
           _
           f
           pf
           (existT
              _
              (weightslang.SCosts s)
              (weightslang.SCostsOk s) :: weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)
           (weightslang.SEpsilonOk s)
           (weightslang.SOutputs s)
           (weightslang.SChan s)
           sx').
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor.
        have ->: weightslang.SChan s = SChan tx.
        { by case: H2. }
        by []. }
      inversion H2; subst. simpl in *.
      inversion HSomeEq; subst.
      constructor; try solve[auto | constructor; auto]. }
    { intros s tx; inversion 1; subst; clear H.
      intros H2.
      exists CSkip.
      have Hora: match_oracle_states (weightslang.SOracleSt s) (SOracleSt tx).
      { by case: H2. }
      have Hmaps: match_maps (weightslang.SWeights s) (SWeights tx).
      { by case: H2. }
      move: H1; case Hpre: (oracle_presend _ _); try solve[inversion 1].
      generalize (match_oracle_send
                    (weightslang.SWeightsOk s)
                    a0
                    (weightslang.SEpsilonOk s)
                    Hora
                    Hmaps
                    Hpre).
      case Hsend': (mwu_send _ _) => [ch tx'].
      case => sx' [] Hsend Hora'.
      exists
        (@mkState
           _
           _
           _
           (weightslang.SCosts s)
           (weightslang.SCostsOk s)
           (weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)
           (weightslang.SEpsilonOk s)
           (p_aux_dist
              a0
              (weightslang.SEpsilonOk s)
              (weightslang.SWeightsOk s)
              (@CMAX_nil t)
              :: weightslang.SOutputs s)
           ch
           sx').
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor => //. }
      inversion H2; subst. simpl in *.
      move: H1 H3 H4 H5 => Hchst H1 Heps H4.
      have H3:
        pmf (p_aux_dist (A:=t) a0 (eps:=eps) eps_ok
                        (w:=w) w_ok (cs:=[::])
                        (CMAX_nil (A:=t))) =
        finfun (fun a : t => Q_to_rat (weights_distr wc a)).
      { rewrite /p_aux_dist.
        simpl.
        move: H4 => H4x.
        have Hx:
             [ffun a : t => match M.find (elt:=D) a wc with
                        | Some q => (Q_to_rat (D_to_Q q) / Q_to_rat (cGamma wc))%R
                        | None => 0%R
                        end] = p_aux (A:=t) eps [::] w.
        { rewrite /p_aux; apply/ffunP => a; rewrite 2!ffunE.
          move: (match_maps_gamma_cGamma H1) => H1'.
          rewrite /match_maps in H1; case: (H1 a) => y []H3 H4. clear H1.
          rewrite H3 /= H1'; f_equal. clear - H4.
          rewrite rat_to_Q_red in H4.
          have H5: Qeq (D_to_Q y) (rat_to_Q (w a)).
          { by rewrite -(Qred_correct (D_to_Q y)) -(Qred_correct (rat_to_Q (w a))) H4. }
            by apply: rat_to_QK2. }
        rewrite -Hx.
        apply/ffunP => x; rewrite 2!ffunE /weights_distr.
        case Hy: (M.find _ _) => // [q].
        by rewrite Q_to_rat_div. }
      inversion Hchst; subst.
      constructor; auto.
      constructor; auto. }
    { move => s t t'.
      case H: (interp c1 t) => [t''|].
      { move => H2 H3.
        case: (IHc1 _ _ _ H H3) => cx []tx []H4 []H5 H6.
        case: (IHc2 _ _ _ H2 H6) => cy []ty []H7 []H8 H9.
        case: H5.
        { case => -> ->.
          case: H8.
          { case => -> ->.
            exists cy, ty.
            split; auto.
            split; auto.
            right; auto.
            constructor.
            inversion H7; subst.
            apply: SSeq1. }
          move => H10.
          exists cy, ty.
          split; auto.
          split; auto.
          right; auto.
          apply: step_trans.
          constructor.
          apply: H10. }
        move => H10.
        case: H8.
        { case => -> H11. subst ty.
          exists CSkip, tx.
          split; first by constructor.
          split; auto.
          right.
          apply: step_plus_trans.
          apply: step_plus_seq.
          apply: H10.
          inversion H4; subst.
          constructor.
          constructor. }
        move => H11.
        exists cy, ty.
        split => //.
        split => //.
        right.
        apply: step_plus_trans.
        apply: step_plus_seq.
        apply: H10.
        inversion H4; subst.
        apply: step_trans.
        constructor.
        inversion H7; subst.
        apply: H11. }
      inversion 1. }
    move => s tx0 t'.
    rewrite N2Nat.inj_iter.
    move H: (N.to_nat t0) => n.
    move: s tx0 t0 t' H; elim: n.
    { move => s t0 t t' H; inversion 1; subst. clear H0 => H2.
      exists CSkip, s; split => //.
      split => //.
      right.
      constructor.
      have H3: t = Coq.Numbers.BinNums.N0.
      { case: t H => //= p H.
        move: (PosN0 p).
          by rewrite H. }
      rewrite H3.
      constructor. }
    move => n IH s t0 t t' H H2 H3.
    have [x [H4 H5]]: exists x, [/\ t = N.succ x & N.to_nat x = n].
    { clear - H.
      exists (N.pred t).
      rewrite N.succ_pred.
      { split => //.
          by rewrite N2Nat.inj_pred H. }
      move => H2; rewrite H2 /= in H; discriminate. }
    subst t n. clear H.
    move: H2 => /=.
    case H4: (Nat.iter (N.to_nat x)
                       (fun s0 : option cstate =>
                          match s0 with
                          | Some s' => interp c s'
                          | None => None
                          end) (Some t0)) => [tx|].
    { move => H5.
      case: (IH _ _ _ _ erefl H4 H3) => c0 []s0 []H6 []H7 H8.
      case: (IHc _ _ _ H5 H8) => cx []sx []H9 []H10 H11.
      case: H7.
      { case.
        inversion 1. }
      move => H12.
      case: H10.
      { case => H13 H14. subst c s0.
        exists c0, sx.
        split => //.
        split => //.
        right.
        apply: step_trans.
        { apply SIterS.
          rewrite nat_of_bin_to_nat.
            by rewrite N2Nat.inj_succ. }
        apply: step_trans.
        constructor.
        rewrite N.pred_succ.
        apply: H12. }
      move => H13.
      exists cx, sx.
      split => //.
      split => //.
      right.
      apply: step_trans.
      constructor.
      { by rewrite nat_of_bin_to_nat N2Nat.inj_succ. }
      rewrite N.pred_succ.
      apply: step_plus_iter_flip => //.
      inversion H6; subst.
      apply: H12.
      apply: H13. }
    inversion 1.
  Qed.

  Lemma findA_map1_Some1 a (l : list t) :
    a \in l ->
    findA (MProps.F.eqb a) (List.map (pair^~ D1) l) = Some D1.
  Proof.
    elim: l a => // a l IH a1; case/orP.
    { move/eqP => ->.
      rewrite /MProps.F.eqb /= /M.E.eq_dec /A'.eq_dec.
      rewrite /A.eq_dec.
      case: (A.eq_dec _ _) => // [H]; elimtype False; apply: H.
      by rewrite -A.eqP. }
    move => H; simpl; case H3: (MProps.F.eqb a1 a) => //.
    by apply: IH.
  Qed.

  Lemma uniq_NoDupA (l : seq t) :
    uniq l ->
    NoDupA A.eq l.
  Proof.
    elim: l => // a l IH; case/andP => H H1; constructor.
    { by move => H2; apply: (notin_InA H). }
    by apply: IH.
  Qed.
  
  Section mwuproof.
    Context {EnumerationOK : @RefineTypeAxiomClass t _}.
    
  Lemma match_maps_init
    : match_maps (init_weights t) init_map.
  Proof.
    move => a; rewrite /init_weights /init_costs /init_map.
    generalize (enumerateP t) => [][]H Huniq; move: (H a) => H2.
    move: (enumP (T:=t) a) => H3.
    exists D1; rewrite MProps.of_list_1b.
    { split.
      { apply: findA_map1_Some1; rewrite H2 mem_enum => //. }
      by rewrite ffunE. }
    have H4: forall x y,
        M.eq_key (elt:=D) ((pair^~ D1) x) ((pair^~ D1) y) -> A.eq x y.
    { by []. }
    apply: (@NoDupA_map _ _ _ (M.eq_key (elt:=D)) _ _ H4).
    by apply: uniq_NoDupA.
  Qed.

  Lemma match_states_init
        (eps : D) eps_ok
        (init_oracle_st : oracle_T)
        (Hmatch_ora_states : match_oracle_states init_oracle_st oracle_init_state)
    : match_states
        (@init_state
           t oracle_T oracle_chanty (Q_to_rat (D_to_Q eps)) eps_ok
           oracle_bogus_chan init_oracle_st)
        (init_cstate eps).
  Proof.
    constructor.
    { apply: match_maps_init. }
    { constructor. }
    { apply: match_maps_init. }
    { rewrite rat_to_Q_red rat_to_QK1.
      by rewrite Qred_idem. }
    { constructor. }
    apply: Hmatch_ora_states.
  Qed.

  (*This is a technical lemma about the interpretation of the specific  *)
  (*     program [mult_weights t nx].*)
  Lemma size_costs_interp_mult_weights
        (nx : N.t) eps tx
        (init_oracle_st : oracle_cT)
    : (0 < nx)%N ->
      interp (mult_weights t nx) (init_cstate eps) = Some tx ->
      (0 < size (SPrevCosts tx))%N.
  Proof.
    rewrite /init_cstate /=; case: (update_weights _ _) => //= a.
    case: (oracle_presend _ _) => //.
    destruct (mwu_send a) eqn:Hsend.
    case Hnx: nx => /= [//|p]; rewrite Pos2Nat.inj_iter => H.
    have [n ->]: exists n, Pos.to_nat p = S n.
    { apply: Pos2Nat.is_succ. }
    simpl.
    case: (nat_rect _ _) => // [s1].
    destruct (oracle_prerecv _ _) eqn:Hpresend => //.
    move: Hpresend. case : b => Hpresend //.
    destruct (mwu_recv (SChan s1)) eqn:Hrecv => /=.
    case: (update_weights _ _) => //= a1.
    destruct (oracle_presend _ _) eqn:Hpresend1 => //.
    destruct (mwu_send a1) eqn:Hsenda1.
    inversion 1; subst => /=.
    case: (SPrevCosts _) => //.
  Qed.
  
  (*[Reals] introduces its own scope [R], so this definition goes first.*)
  Definition epsOk (eps : rat) : Prop := (0 < eps <= 1 / 2%:R)%R.
  
  Import Reals.
  
  Lemma interp_mult_weights_epsilon_no_regret :
    forall (nx : N) (t' : cstate) (eps : D) (eps_ok : epsOk (Q_to_rat (D_to_Q eps)))
           (init_oracle_st : oracle_T)
           (Hmatch_ora_states : match_oracle_states init_oracle_st oracle_init_state),
      let: epsR := rat_to_R (Q_to_rat (D_to_Q eps)) in
      (0 < nx)%N ->
      interp (mult_weights t nx) (init_cstate eps) = Some t' ->
      exists s',
        match_states s' t' /\
        ((state_expCost1 (all_costs0 s') s' - OPTR a0 s') / Tx nx <=
         epsR + Rpower.ln (rat_to_R #|t|%:R) / (epsR * Tx nx))%R.
  Proof.
    move => nx t' eps epsOk init_oracle_st Hmatch_ora_st Hnx H.
    case: (interp_step_plus H (match_states_init epsOk Hmatch_ora_st)) => c' []s'.
    case => H2 [] []; first by case; inversion 1.
    move => H3 H4; exists s'; split => //.
    move: (size_costs_interp_mult_weights oracle_init_state Hnx H) => H5.
    have H6: size (SPrevCosts t') = size (all_costs' s').
    { inversion H4; subst; simpl in *. clear - H1.
      rewrite /all_costs' /all_costs0 /all_costs.
      rewrite /weightslang.SCosts /SCostsOk /weightslang.SPrevCosts.
      rewrite size_map size_removelast /=.
      clear - H1. induction H1 => //.
      by rewrite /= IHmatch_costs_seq. }
    have H7: (0 < size (all_costs' s'))%N.
    { by rewrite -H6. }
    inversion H2; subst.
    apply: mult_weights_epsilon_no_regret_noprime => //.
    eauto.
  Qed.


  Lemma match_maps_lem s m : 
    match_maps s m -> 
    forall a q, M.find a m = Some q -> Qopp 1 <= D_to_Q q <= 1 ->
    ler (normr (s a)) (GRing.one rat_numDomainType).
  Proof.
  rewrite /match_maps => H a q H0.
  case: (H a) => q' [H1 H2].
  rewrite H0 in H1; inversion H1; subst; clear H1.
  case => H3 H4.
  rewrite -rat_to_QK1 in H2.
  apply rat_to_Q_inj in H2.
  rewrite -H2 -Q_to_rat1.
  rewrite real_ler_norml.
  2: { rewrite /in_mem; simpl. apply ler_total. }
  rewrite -Q_to_rat_opp.
  apply /andP; split.
  apply: Q_to_rat_le => //.
  apply: Q_to_rat_le => //.
  Qed.

  End mwuproof.
  End mwuProof.
  End OrderedFinType_Section.
(*   Print Assumptions interp_mult_weights_epsilon_no_regret. *)End MWUProof.
