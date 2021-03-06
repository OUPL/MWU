Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith Reals Rpower Ranalysis Fourier.
Require Import Coq.Logic.ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.


Import GRing.Theory Num.Def Num.Theory.
Require Import Lra.

Require Import OUVerT.extrema OUVerT.dist OUVerT.numerics OUVerT.bigops.

(** [NOTE on refs] Section and lemma names below (e.g., R177) 
    refer to sections/lemmas in Roughgarden's "Twenty Lectures 
    in Algorithmic Game Theory" (Cambridge 2016). *)

Section weights.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A is inhabited*)
  Variable eps : rat.
  Variable eps_range : 0 < eps <= 1/2%:R.
    
  Definition weights := {ffun A -> rat}.
  Definition init_weights : weights := finfun (fun _ => 1%:R).
  Definition costs := {ffun A -> rat}. 

  Lemma init_weights_gt0 :
    forall a : A, 0 < init_weights a.
  Proof. by move=> a; rewrite /init_weights ffunE. Qed.
  
  Definition update_weights (w : weights) (c : costs) : weights :=
    finfun (fun a : A => w a * (1 - eps * c a)).

  Lemma update_weights_gt0 (w : weights) (c : costs) :
    (forall a : A, `|c a| <= 1) -> 
    (forall a : A, 0 < w a) ->
    forall a : A, 0 < update_weights w c a.
  Proof.
    move=> H0 H a.
    rewrite /update_weights ffunE.
    apply: mulr_gt0=> //.
    rewrite subr_gt0.
    case: (andP eps_range)=> H1 H2.
    rewrite mulrC.
    case H3: (c a == 0).
    { move: (eqP H3)=> ->; rewrite mul0r=> //. }
    case H4: (c a < 0).
    { have H5: c a * eps < 0.
      { rewrite mulrC pmulr_rlt0 => //. }
      by apply: (ltr_le_trans H5). }
    have H5: 0 < c a.
    { have H6: (c a != 0) by apply/negP; rewrite H3.
      by case: (ltr_total H6); rewrite H4. }
    have H6: (c a * eps < c a).
    { rewrite gtr_pmulr => //.
      apply: (ler_lt_trans H2)=> //. }
    move: (H0 a)=> H7; apply: (ltr_le_trans H6).
    by rewrite ler_norml in H7; case: (andP H7).
  Qed.    

  (** The cost functions [cs] are given in reverse chronological order.
      That is, 
        [cs = c_T :: c_(T-1) :: ... :: c_1].
      This simplifies reasoning: [weights_of] is now fold-right
      rather than fold-left. *)
  Fixpoint weights_of (cs : seq costs) (w : weights) : weights :=
    if cs is [:: c & cs'] then
      update_weights (weights_of cs' w) c
    else w.

  Lemma weights_of_ind
        (cs : seq costs)
        (w : weights)
        (P : seq costs -> weights -> Prop) :
    P [::] w ->
    (forall w' c cs',
        P cs' w' ->
        P [:: c & cs'] (update_weights w' c)) ->
    P cs (weights_of cs w).
  Proof.
    move=> H IH; elim: cs=> //.
    move=> c cs' H0 /=.
    by apply: IH.
  Qed.    

  Lemma weights_of_eq (cs : seq costs) :
    weights_of cs init_weights =
    finfun (fun a => \prod_(c <- cs) (1 - eps*(c a))).
  Proof.
    elim: cs.
    { simpl.
      rewrite /init_weights.
      apply/ffunP=> x.
      by rewrite !ffunE big_nil.
    }
    move=> a l H /=.
    rewrite /update_weights; apply/ffunP=> x; rewrite H !ffunE.
    by rewrite big_cons mulrC.
  Qed.    

  (** Here's an alternative version: fold-left-style [weights_of]: *)
  Fixpoint weights_of_left (cs : seq costs) (w : weights) : weights :=
    if cs is [:: c & cs'] then
      weights_of_left cs' (update_weights w c)
    else w.

  Lemma weights_of_app cs1 cs2 w :
    weights_of (cs1 ++ cs2) w =
    weights_of cs1 (weights_of cs2 w).
  Proof. by elim: cs1 cs2 w => // c cs1 IH cs2 w /=; rewrite IH. Qed.

  Lemma weights_of_rightleft cs w :
    weights_of (rev cs) w = weights_of_left cs w.
  Proof.
    elim: cs w => // c cs' IH w /=; rewrite -IH.
    by rewrite rev_cons -cats1 weights_of_app.
  Qed.  
  
  Lemma weights_of_gt0 (cs : seq costs) (w : weights) :
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) ->     
    (forall a : A, 0 < w a) -> 
    forall a : A, 0 < weights_of cs w a.
  Proof.
    apply weights_of_ind=> //.
    move=> w' c cs' IH H0 H1 a.
    apply: update_weights_gt0=> //.
    by apply: H0; rewrite /in_mem /=; apply/orP; left.
    apply: IH=> // c0 Hin a1.
    by apply: H0; rewrite /in_mem /=; apply/orP; right.
  Qed.   

  Lemma sum_gt0 (w : weights) :
    (forall a : A, 0 < w a) ->
    0 < \sum_(a : A) w a.
  Proof.
    move=> H0.
    have H: 0 <= \sum_(a : A) w a.
    { by apply/sumr_ge0=> i _; apply/ltrW. }
    rewrite ltr_def; apply/andP; split=> //.
    apply/eqP=> H1.
    have H2: forall i : A, true -> 0 <= w i.
    { by move=> i _; apply/ltrW. }
    move: (psumr_eq0P (P:=xpredT)(F:=w) H2 H1).
    move: (H0 a0)=> H4.
    by move/(_ a0 erefl)=> H3; rewrite H3 in H4.
  Qed.
  
  Lemma sum_weights_of_gt0 (cs : seq costs) (w : weights) :
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) ->     
    (forall a : A, 0 < w a) -> 
    0 < \sum_(a : A) (weights_of cs w) a.
  Proof.
    by move=> H0 H; apply: sum_gt0; apply: weights_of_gt0.
  Qed.   
 
  Lemma sum_weights_of_not0 (cs : seq costs) :
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) ->     
    \sum_(a : A) (weights_of cs init_weights) a != 0.    
  Proof.
    move=> H; move: sum_weights_of_gt0.
    move/(_ cs init_weights H init_weights_gt0)=> H0.
    by apply/eqP=> H1; rewrite H1 in H0.
  Qed.    

  Lemma weight1_sum_ler (a : A) (w : weights) :
    (forall a : A, 0 <= w a) ->
    w a <= \sum_(a0 : A) w a0.
  Proof.
    move=> H.
    suff: ((\sum_(a1 : A) if a1 == a then w a1 else 0) <= \sum_a1 w a1).
    { move=> H2.
      have H3: w a <= \sum_a1 (if a1 == a then w a1 else 0).
      { have H4: \sum_a1 (if a1 == a then w a1 else 0) = \sum_(a1 | a1 == a) w a1.
        { by rewrite -big_mkcond.
        }
        by rewrite H4 big_pred1_eq.
      }
      by apply: (ler_trans H3 H2).
    }
    apply: ler_sum.
    by move=> i _; case: (i == a).
  Qed.

  Definition gamma (w : weights) : rat :=
    \sum_(a : A) (w a).

  Lemma gamma_normalizes (w : weights) :
    \sum_(a : A) w a != 0 -> 
    \sum_(a : A) w a / gamma w == 1.
  Proof. by move=> H; rewrite /gamma -mulr_suml mulrC mulVf. Qed.

  Lemma gamma_ge0 (w : weights) :
    (forall a : A, 0 <= w a) -> 
    0 <= gamma w.
  Proof.
    by move=> H; apply: sumr_ge0.
  Qed.
    
  Definition p_aux (cs : seq costs) (w : weights) : weights :=
    let w' := weights_of cs w in
    finfun (fun a : A => w' a / gamma w').

  (** The following definition of [p_aux] uses fold-left [weights_of']: *)
  Definition p_aux_left (cs : seq costs) (w : weights) : weights :=
    let w' := weights_of_left cs w in
    finfun (fun a : A => w' a / gamma w').

  Lemma p_aux_aux_left cs w : p_aux (rev cs) w = p_aux_left cs w.
  Proof.
    rewrite /p_aux /p_aux_left; apply/ffunP => a; rewrite 2!ffunE.
    by rewrite weights_of_rightleft.
  Qed.      

  Lemma div1rr (r : rat) : r != 0 -> 1 / r * r == 1.
  Proof. by move=> H; rewrite div1r mulVf. Qed.

  Lemma div1rn (n : nat) (r : rat) : r != 0 -> r == n%:R -> 1 / r *+ n == 1.
  Proof.
    move=> H H2; move: (eqP H2)=> H3.
    rewrite H3 -mulrnAl mulfV=> //.
      by rewrite -H3.
  Qed.

  Lemma Acard_gt0 : (0 < #|A|)%N.
  Proof. by apply/card_gt0P; exists a0. Qed.

  Lemma rat_to_R_Acard_gt0 : Rlt 0 (rat_to_R #|A|%:R).
  Proof.
    move: Acard_gt0; rewrite -rat_to_R0 -(@ltr_nat rat_numDomainType).
    by apply: rat_to_R_lt.
  Qed.

  Lemma rat_to_R_Acard_ge1 : Rle 1 (rat_to_R #|A|%:R).
  Proof.
    move: Acard_gt0; rewrite -rat_to_R1 -(@ler_nat rat_numDomainType).
    by apply: rat_to_R_le.
  Qed.
  
  Lemma p_aux_ind
        (cs : seq costs)
        (w : weights)
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)
        (WEIGHTS : forall a : A, 0 < w a)        
        (P : seq costs -> weights -> Prop) :
    P [::] [ffun a => w a / gamma w] ->
    (forall (w' : weights) c cs',
        let: w'' := update_weights w' c in
        (forall a : A, `|c a| <= 1) ->
        (forall a : A, 0 < w' a) -> 
        P cs' [ffun a => w' a / gamma w'] ->
        P [:: c & cs'] [ffun a => w'' a / gamma w'']) -> 
    P cs (p_aux cs w).
  Proof.
    move=> H IH; elim: cs CMAX=> //.
    move=> c cs'; rewrite /p_aux /=.
    set w' := weights_of cs' w.
    move=> H0 H1; apply: (IH w' c cs').
    by apply: H1; rewrite /in_mem /=; apply/orP; left.
    apply: weights_of_gt0=> // cx Hin a; apply: H1.
    by rewrite /in_mem /=; apply/orP; right.
    by apply: H0=> c0 H2 a; apply: H1; rewrite /in_mem /=; apply/orP; right.
  Qed.    

  Lemma p_aux_dist_axiom (cs : seq costs) (w : weights) :
    (forall a : A, 0 < w a) -> 
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) -> 
    dist_axiom (p_aux cs w).
  Proof.
    move => Hx H0; rewrite /p_aux /dist_axiom; apply/andP; split.
    { have H:
        \sum_(t : A)
         [ffun a => (weights_of cs w) a /
                    gamma (weights_of cs w)] t
      = \sum_(t : A)
         (weights_of cs w) t /
         gamma (weights_of cs w).
      { by apply/congr_big=> // i _; rewrite ffunE. }
      rewrite H; move {H}.
      rewrite gamma_normalizes=> //.
      have H1: 0 < \sum_a (weights_of cs w) a.
      { apply: sum_weights_of_gt0 => //. }
      by apply/eqP => H2; rewrite H2 in H1.
    }
    change [forall t, 0 <= p_aux cs w t].
    apply (p_aux_ind H0 Hx).
    { apply/forallP=> x; rewrite ffunE.
      apply: mulr_ge0; first by apply: ltrW; apply: Hx.
      rewrite invr_ge0 /gamma /init_weights; apply/sumr_ge0=> i _.
      by apply: ltrW; apply: Hx. }
    move=> w' c cs' H1 H2 H3; apply/forallP=> x; rewrite ffunE.
    have H4: forall a : A, 0 < update_weights w' c a.
    { move=> a; apply: update_weights_gt0=> //. }
    apply: divr_ge0; first by apply/ltrW; apply: (H4 x).
    by apply: gamma_ge0=> a; apply/ltrW.
  Qed.

  Lemma p_aux_left_dist_axiom (cs : seq costs) (w : weights) :
    (forall a : A, 0 < w a) -> 
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) -> 
    dist_axiom (p_aux_left cs w).
  Proof.
    move => H H2; rewrite /p_aux_left.
    rewrite -weights_of_rightleft; apply: p_aux_dist_axiom => //.
    move => c H3 a; apply: H2.
    by rewrite mem_rev in H3.
  Qed.
  
  Definition p_aux_dist
             (w : weights)
             (WPOS : forall a : A, 0 < w a)
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)             
    : dist A [numDomainType of rat] :=
    mkDist (p_aux_dist_axiom WPOS CMAX).

  Definition p_aux_left_dist
             (w : weights)
             (WPOS : forall a : A, 0 < w a)
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)             
    : dist A [numDomainType of rat] :=
    mkDist (p_aux_left_dist_axiom WPOS CMAX).
  
  Definition p (cs : seq costs) : {ffun A -> rat} :=
    p_aux cs init_weights.

  Lemma p_dist_axiom (cs : seq costs) :
    (forall c, c \in cs -> forall a : A, `|c a| <= 1) -> 
    dist_axiom (p cs).
  Proof.
    move => H; apply: p_aux_dist_axiom => //.
    apply: init_weights_gt0.
  Qed.    

  Delimit Scope R_scope with R.
  
  Lemma rat_to_R_prod' (cs : seq costs) a :
    rat_to_R (\prod_(c <- cs) (1 - eps * c a)) =  
    big_product cs (fun c => (rat_to_R 1 - rat_to_R eps * rat_to_R (c a)))%R.
  Proof.
    rewrite rat_to_R_prod; apply: big_product_ext=> // x.
    by rewrite rat_to_R_plus rat_to_R_opp rat_to_R1 /Rminus rat_to_R_mul.
  Qed.    

  Lemma exprDr_seq (r : rat) (cs : seq costs) (a : A) :
    0 < r -> 
    Rpower (rat_to_R r) (rat_to_R (\sum_(c <- cs) c a)) =
    big_product cs (fun c => Rpower (rat_to_R r) (rat_to_R (c a))).
  Proof.
    move=> H; elim: cs=> //=.
    { rewrite big_nil rat_to_R0 Rpower_O=> //.
      have H2: (0 = rat_to_R 0)%R.
      { by rewrite /rat_to_R /Qreals.Q2R /= Rmult_0_l. }
      rewrite H2.
      by apply: rat_to_R_lt.
    }
    move=> a1 l IH; rewrite !big_cons.
    rewrite -IH.
    rewrite rat_to_R_plus.
    by rewrite Rpower_plus.
  Qed.

  Lemma neps_gt0 : 0 < 1 - eps.
  Proof.
    rewrite subr_gt0.
    have H3: (1/2%:R : rat) < 1.
    { by rewrite ltr_pdivr_mulr. }
    have H4: eps <= 1 / 2%:R.
    { by case: (andP eps_range). }
    by apply: (ler_lt_trans H4 H3).
  Qed.      

  Lemma rat_to_R_eps_gt0 : (0 < rat_to_R eps)%R.
  Proof.
    case: (andP eps_range)=> H1 H2.
    by rewrite -rat_to_R0; apply: rat_to_R_lt.
  Qed.

  Lemma rat_to_R_eps_pos : (0 <= rat_to_R eps)%R.
  Proof.
    by apply: Rlt_le; apply: rat_to_R_eps_gt0. 
  Qed.

  Lemma rat_to_R_eps_neq0 : (rat_to_R eps <> 0)%R.
  Proof.
    move=> H; move: rat_to_R_eps_gt0; rewrite H.
    apply: Rlt_irrefl.
  Qed.
  
  Lemma rat_to_R_eps_le_one_half : (rat_to_R eps <= 1/2)%R.
  Proof.
    case: (andP eps_range)=> H1 H2.
    have H3: (1 / 2 = rat_to_R (1 / 2%:R))%R.
    { rewrite /Rdiv rat_to_R_mul rat_to_R1; f_equal.
      rewrite rat_to_R_inv => //.
      by rewrite rat_to_R2. }
    by rewrite H3; apply: rat_to_R_le.
  Qed.
  
  Lemma rat_to_R_neps : rat_to_R (1 - eps) = (1 - rat_to_R eps)%R.
  Proof. by rewrite rat_to_R_plus rat_to_R_opp rat_to_R1. Qed.

  Lemma rat_to_R_neps_gt0 : (0 < rat_to_R (1 - eps))%R.
  Proof. by rewrite -rat_to_R0; apply: rat_to_R_lt; apply: neps_gt0. Qed.
    
  Lemma Rpower_pos x y : (0 < x -> 0 <= y -> 0 < Rpower x y)%R.
  Proof.
    rewrite /Rpower.
    case: (Req_dec y 0%R).
    { move=> ->; rewrite Rmult_0_l exp_0.
      by move=> _ _; lra. }
    move=> H H2 H3.
    apply: exp_pos.
  Qed.   

  Lemma one_minus_pos x : (x <= 1 -> 0 <= 1 - x)%R.
  Proof. move=> H; fourier. Qed.
  
  Definition pdist
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)             
    : dist A [numDomainType of rat] :=
    mkDist (p_dist_axiom CMAX).

  (** The expected cost of the MW algorithm after [length cs] timesteps *)
  Definition expCost
             (cT : costs)
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)
    : rat :=
    expectedValue (pdist CMAX) cT.
  
  (** The best fixed action wrt. cost functions [cs] *)
  Definition best_action (cs : seq costs) : A :=
    arg_min xpredT (fun a : A => \sum_(c <- cs) c a) a0.


  (** Some general lemmas about logarithms 
       -- should be moved elsewhere *)
  Lemma ln_le (x y : R) : (0 < x -> x <= y -> ln x <= ln y)%R.
  Proof.
    move=> H0; case=> H.
    left; apply: ln_increasing=> //.
    by right; subst x.
  Qed.

  (* The construction of the derivability proof is needed to apply
     the compositional rules in the next two proofs *)
  Definition aux_const x : derivable_pt (fun x => (exp x - (1%R +x))%R) x :=
    derivable_pt_minus exp (Rplus 1%R) x (derivable_pt_exp x)
      (derivable_pt_plus (fun _ : R => 1%R) id x (derivable_pt_const 1 x)
      (derivable_pt_id x)).

  Lemma aux_neg y (H :(y < 0)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y < 0)%R.
  Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rlt_minus.
    rewrite -exp_0 Rplus_0_l.
    apply exp_increasing => //.
  Qed.

  Lemma aux_pos y (H :(0 <= y)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y >= 0)%R.
  Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rge_minus.
    rewrite -exp_0 Rplus_0_l.
    apply Rle_ge.
    case: H => H;
    first by left; apply exp_increasing => //.
    right. f_equal => //.
  Qed.

  Lemma ln_Taylor_upper' x : ((1 + x) <= exp x)%R.
  Proof.
    clear A a0 eps eps_range.
    apply Rge_le.
    apply Rminus_ge.
    set f := fun x => (exp x - (1 + x))%R.
    have H0 : (f x = exp x - (1 + x))%R => //.
    rewrite -H0; clear H0.
    have H0 : (f 0 = 0)%R by
      rewrite /f exp_0 Rplus_0_r;
      apply Rminus_diag_eq => //.
    rewrite -H0.
    case: (Rtotal_order x 0) => H.
    {
      left.
      apply (MVT_cor1 f x 0 aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_l in H1.
      rewrite H0.
      have H3 :  (x < 0)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans x c 0) => //.
      apply Ropp_eq_compat in H1.
      rewrite Ropp_involutive in H1.
      rewrite H1.
      apply Rlt_gt.
      rewrite Ropp_mult_distr_l.
      apply Rmult_lt_0_compat.
      apply Ropp_0_gt_lt_contravar.
      apply Rlt_gt.
      apply aux_neg.
      case: H2 => //.
      fourier.
    }
    {
      case: H => H;
      first by subst; rewrite /f Rplus_0_r exp_0; right => //.
      apply (MVT_cor1 f 0 x aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_r in H1.
      rewrite H0.
      have H3 :  (0 < x)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans 0 c x) => //.
      rewrite H1.
      apply Rle_ge.
      rewrite -(Rmult_0_l x).
      apply Rmult_le_compat.
      right => //.
      left => //.
      apply Rge_le.
      apply aux_pos.
      left. case: H2 => //.
      right => //.
    }
  Qed.

  Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
  Proof.
    intros h.
    rewrite /ln.
    case_eq (Rlt_dec 0 (1-x)); move => h1 h2;
    last by apply False_rec; apply h1; fourier.
    rewrite /Rln => /=.
    destruct (ln_exists (1 - x) h1) as [x0 e0].
    apply Rplus_le_reg_l with (r := 1%R).
    rewrite /Rminus in e0.
    rewrite e0.
    apply ln_Taylor_upper'.
  Qed.

  Lemma deriv_aux_lower :
    derivable (fun x : R => ((1 - x) * exp (x + x ^ 2))%R).
  Proof.
    rewrite /derivable => x.
    apply derivable_pt_mult.
    apply derivable_pt_minus.
    apply derivable_pt_const.
    apply derivable_pt_id.
    set f1 := fun x => (x + x ^2)%R.
    set f2 := fun x => exp x.
    have H : (fun x0 : R => exp (x0 + x0 ^ 2))
              = Ranalysis1.comp f2 f1 => //.
    rewrite H.
    apply derivable_pt_comp.
    rewrite /f1.
    apply derivable_pt_plus.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_const.
    apply derivable_pt_exp.
  Defined.

  Lemma ln_Taylor_lower_aux_lt_0 x (H : (x < 0)%R) :
    (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
      x (deriv_aux_lower x) < 0)%R.
  Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H0 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H0.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_lt_compat_l.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_lt_gt_compat_neg_l => //.
    fourier.
  Qed.

  Lemma ln_Taylor_lower_aux_gt_0
    x (H0 : (0 < x)%R) (H1 : (x  <= 1/2)%R) :
    (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
      x (deriv_aux_lower x) >= 0)%R.
  Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H2 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H2.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_ge_compat_l.
    left.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_ge_compat_l => //. fourier.
    case: H1 => H1. fourier. subst. fourier.
  Qed.

  Lemma ln_Taylor_lower x : (x <= 1/2 -> -x - x^2 <= ln (1 - x))%R.
  Proof. 
    intros H.
    rewrite -[(-x - x^2)%R] ln_exp.
    apply ln_le; first by apply exp_pos.
    have h : ((- x - x ^2) = - (x + x^2))%R by field.
      rewrite h. clear h.
    apply (Rmult_le_reg_r (/exp (- (x + x ^ 2))));
      first by apply Rinv_0_lt_compat; apply exp_pos.
    rewrite Rinv_r;
      last by move: (exp_pos (- (x + x ^ 2))%R) => H0 H1; fourier.
    rewrite exp_Ropp Rinv_involutive;
      last by move: (exp_pos (x + x^2)%R) => H0 H1; fourier.
    set F := fun x => ((1 - x) * exp (x + x^2))%R.
    have H0 : (F x = (1 - x) * exp (x + x ^ 2))%R => //.
    rewrite -H0; clear H0.
    have H1 : (F 0 = 1)%R. rewrite /F.
    have H0 : (0 + 0^2 = 0)%R by ring.
      rewrite H0; ring_simplify; apply exp_0; clear H0.
    rewrite -H1.
    apply Rminus_le.
    case: (Rtotal_order 0 x) => H2; last case: H2 => H2.
    {
      move: (MVT_cor1 F 0 x deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      have h : (F 0 - F x = - (F x - F 0))%R. ring.
      rewrite h H3. apply Rge_le. clear h.
      rewrite Rminus_0_r.
      apply Ropp_0_le_ge_contravar.
      apply Rmult_le_pos; last by fourier.
      apply Rge_le.
      apply ln_Taylor_lower_aux_gt_0 => //.
      fourier.
    }
    {
      right. subst. ring.
    }
    {
      move: (MVT_cor1 F x 0 deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      rewrite H3.
      rewrite Rminus_0_l.
      rewrite -(Rmult_0_r (derive_pt F c (deriv_aux_lower c))%R).
      apply Rmult_le_compat_neg_l; last by fourier.
      left.
      apply ln_Taylor_lower_aux_lt_0 => //.
    }
  Qed.

  Lemma exp_Taylor_lower x : (x <= 1/2 -> exp(-x - x^2) <= 1 - x)%R.
  Proof.
    move => H.
    move: (ln_Taylor_lower H); case.
    { move => H2; left.
      rewrite -[(1 - _)%R]exp_ln.
      { apply: exp_increasing.
        apply: H2. }
      fourier. }
    move => ->; rewrite exp_ln; fourier.
  Qed.    

  Lemma gamma0_sizeA : gamma init_weights = #|A|%:R.
  Proof.
    rewrite /gamma /init_weights sum_ffunE'.
    have H: \sum_(t : A) (1%:R : rat) = (\sum_(t : A) 1%N)%:R.
    { by rewrite natr_sum. }
    by rewrite H sum1_card.
  Qed.

  (** All nonempty subsequences of "cs" *)
  Fixpoint subSeqs_of A (cs : seq A) : seq (seq A) :=
    if cs is [:: c & cs'] then [:: cs & subSeqs_of cs']
    else [::].

  Lemma in_subSeqs_of (cs : seq costs) :
    cs != [::] -> cs \in subSeqs_of cs.
  Proof.
    case: cs; first by [].
    by move=> // a l H /=; rewrite in_cons; apply/orP; left.
  Qed.  
  
  Lemma subSeqs_of_CMAX (cs : seq costs)
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1) :
    forall cs', cs' \in subSeqs_of cs ->
    forall c, c \in cs' -> forall a : A, `|c a| <= 1.
  Proof.
    elim: cs CMAX=> /=.
    { by move=> H cs'; rewrite in_nil. }
    move=> a l IH H cs'; rewrite in_cons; case/orP.
    { move/eqP=> -> c; rewrite in_cons; case/orP.
      { by move/eqP=> -> a1; apply: H; apply/orP; left. }
      by move=> H2; apply: H; apply/orP; right. }
    move=> H2 c H3.
    have H4: forall c, c \in l -> forall a, `|c a| <= 1.
    { by move=> c0 H4; apply: H; apply/orP; right. }
    by apply: (IH H4 cs' H2).
  Qed.    

  Lemma CMAX_nil :
    forall c : costs, c \in [::] -> forall a : A, `|c a| <= 1.
  Proof. by move=> c; rewrite in_nil. Qed.

  Definition CMAXb (cs : seq costs) :=
    all [pred c : costs | [forall a : A, `|c a| <= 1]] cs.

  Lemma CMAXb_behead (cs : seq costs) :
    CMAXb cs -> CMAXb (behead cs).
  Proof. by move/allP=> H; apply/allP=> y/mem_behead H2; apply: H. Qed.
  
  Lemma CMAXP (cs : seq costs) :
    reflect (forall c, c \in cs -> forall a : A, `|c a| <= 1) (CMAXb cs).
  Proof.
    case H: (CMAXb cs).
    { apply: ReflectT=> c H2 a; rewrite /CMAXb in H; move: (allP H).
      by move/(_ c)/(_ H2)=> /= => /forallP/(_ a). }
    apply: ReflectF=> H2; rewrite /CMAXb in H; move: (negbT H).
    move/allPn; case=> c H3; move/negP=> /=; apply; apply/forallP=> x.
    by apply: H2.
  Qed.    

  Lemma CMAXb_CMAX cs :
    CMAXb cs ->
    forall c, c \in cs -> forall a, `|c a| <= 1.
  Proof. by apply/CMAXP. Qed.
  
  Definition CMAX_costs_seq := {cs : seq costs | CMAXb cs}.
  
  Definition CMAX_seq (cs' : seq (seq costs)) := all CMAXb cs'.
  
  Program Fixpoint subSeqs_aux (cs' : seq (seq weights)) (CMAX : CMAX_seq cs')
    : seq CMAX_costs_seq
    := (match cs' as cs'' return _ = cs'' -> seq CMAX_costs_seq with
        | [::] => fun _ => [::]
        | [:: cs'' & cs'_rest] => fun pf : cs' = cs'' :: cs'_rest  => [:: exist _ cs'' _ & @subSeqs_aux cs'_rest _]
        end) erefl.
  Next Obligation. by case: (andP CMAX). Qed.
  Next Obligation. by case: (andP CMAX). Qed.
  
  Lemma CMAX_seq_subSeqs_of (cs : seq weights)
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)
    : CMAX_seq (subSeqs_of cs).
  Proof.
    elim: cs CMAX=> //= a l IH H; apply/andP; split.
    apply/andP; split.
    { by apply/forallP; apply: H; rewrite in_cons; apply/orP; left. }
    have H2: forall c, c \in l -> forall a, `|c a| <= 1.
    { by move=> c H2 a1; apply: H; rewrite in_cons; apply/orP; right. }
    case H0: (l == [::]).
    { move: (eqP H0)=> -> //. }
    { by apply: (allP (IH H2)); apply: in_subSeqs_of; rewrite H0. }
    by apply: IH=> c H2 a1; apply: H; rewrite in_cons; apply/orP; right.
  Qed.      
    
  Definition subSeqs (cs : seq weights)
             (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1)
    : seq CMAX_costs_seq
    := @subSeqs_aux (subSeqs_of cs) (CMAX_seq_subSeqs_of CMAX). 

  Lemma Rle_contra_tech x y z : (-x <= y + -z ->  z <= y + x)%R.
  Proof.
    have ->: (y + -z = -(-y + z))%R.
    { by rewrite Ropp_plus_distr Ropp_involutive. }
    move/Ropp_le_cancel/(Rplus_le_compat_r y).
    have ->: (-y + z + y = z)%R.
    { by rewrite Rplus_comm -Rplus_assoc Rplus_opp_r Rplus_0_l. }
    by rewrite Rplus_comm.
  Qed.    

  Lemma pow_le1 x : (-1 <= x <= 1 -> x^2 <= 1)%R.
  Proof.
    case => H1 H2.
    have ->: (1 = 1^2)%R by rewrite pow1.
    case H3: (Rlt_dec x 0) => [pf|pf].
    { clear H2 H3.
      rewrite /pow Rmult_1_r Rmult_1_l.
      have H2: (x * x <= x * -1)%R.
      { apply: Rmult_le_compat_neg_l; try fourier. }
      apply: Rle_trans; first by apply: H2.
      fourier. }
    apply pow_incr.
    split => //.
      by apply: Rnot_lt_le.
  Qed.
  
  Section R173_175_176_aux.
    Variable cT : costs.    
    Variable cs : seq costs.
    Notation cs' := ([:: cT & cs]).
    Variable CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1.
      
    Notation astar := (best_action cs).
    Notation OPT := (\sum_(c <- cs) c astar).
    Notation wT := (weights_of cs init_weights). 
    Notation gammaT := (gamma wT).
    Notation pT := (pdist CMAX).
    (** In expCostT, CMAX defines the distributed pT computed at time t. 
        cT is the cost function returned by the adversary, after pT has 
        been calculated. *)
    Notation expCostT := (expCost cT CMAX).
    
    Lemma gammaT_ge_wT_astar : wT astar <= gammaT.
    Proof.
      rewrite /gamma.
      apply: weight1_sum_ler=> a.
      apply/ltrW; apply: weights_of_gt0=> //.
      apply: init_weights_gt0.
    Qed.

    Lemma wT_astar_eq :
      rat_to_R (wT astar) =
      big_product cs (fun c => (rat_to_R 1 - rat_to_R eps * rat_to_R (c astar)))%R. 
    Proof. by rewrite weights_of_eq ffunE rat_to_R_prod'. Qed.

    Lemma rat_to_R_cost_pos a c : c \in cs -> (0 <= rat_to_R `|c a|)%R.
    Proof.
      rewrite -rat_to_R0=> H.
      apply: rat_to_R_le.
      by move: (normr_ge0 (c a)).
    Qed.

    Lemma rat_to_R_sumcost_pos a : (0 <= rat_to_R (\sum_(c <- cs) `|c a|))%R.
    Proof.
      move: rat_to_R_cost_pos; elim: cs.
      { move=> _; rewrite big_nil rat_to_R0; apply: Rle_refl. }
      move=> c' l IH H; rewrite big_cons rat_to_R_plus.
      apply: Rplus_le_le_0_compat.
      by apply: H; apply/orP; left.
      by apply: IH=> a1 c H2; apply: H; apply/orP; right.
    Qed.        

    Lemma rat_to_R_cost_le1 a c : c \in cs -> (rat_to_R `|c a| <= 1)%R.
    Proof.
      rewrite -rat_to_R1=> H; move: (CMAX H a)=> H2.
      by apply: rat_to_R_le.
    Qed.

    Lemma expCostT_eq :
      expCostT = \sum_(a : A) (wT a / gammaT) * cT a.
    Proof.
      rewrite /expCost /expectedValue /expectedCondValue /pT /p /= /p_aux.
      by apply: congr_big=> // i _; rewrite ffunE.
    Qed.
    
    (** R17.3: Gamma^{T+1} = gamma^T * (1 - eps * expCostT) *)    
    Lemma gammaT_Tprod1 :
      gamma (weights_of cs' init_weights) = gammaT * (1 - eps * expCostT).
    Proof.
      rewrite expCostT_eq.
      rewrite /weights_of -/weights_of /update_weights.
      rewrite /gamma sum_ffunE'.
      have H: \sum_t wT t * (1 - eps * cT t) =
              \sum_t (wT t - wT t * eps * cT t).
      { apply: congr_big=> // x _; rewrite mulrDr.
        by rewrite mulr1 -mulrA mulrN. }
      rewrite H sumrB.
      have H2: \sum_i wT i * eps * cT i =
               eps * \sum_i wT i * cT i.
      { have H3: \sum_i wT i * eps * cT i = \sum_i eps * (wT i * cT i).
        { by apply: congr_big=> // i _; rewrite mulrA [wT i * _]mulrC. }
        by rewrite H3 mulr_sumr. }
      rewrite H2.
      have H3: \sum_i wT i - eps * (\sum_i wT i * cT i) =
               gammaT * (1 - eps * (\sum_i wT i * cT i) / gammaT).
      { rewrite mulrDr mulr1 [(eps * _) / _]mulrC mulrN mulrA mulfV.
        { by rewrite mul1r. }
        by apply sum_weights_of_not0. }
      rewrite H3.
      rewrite /gammaT.
      f_equal.
      f_equal.
      f_equal.
      rewrite -mulrA; f_equal.
      rewrite mulr_suml; apply: congr_big=> // i _.
      by rewrite -mulrA [cT i / _]mulrC mulrA.
    Qed.    

    Lemma gammaT_exp_neps :
      (rat_to_R (gamma (weights_of cs' init_weights)) <=
       rat_to_R (gammaT) * exp (- rat_to_R eps * rat_to_R expCostT))%R.
    Proof.
      rewrite gammaT_Tprod1 rat_to_R_mul.
      apply: Rmult_le_compat_l.
      { rewrite -rat_to_R0; apply: rat_to_R_le.
        apply: gamma_ge0; move => a; apply/ltrW.
        apply: weights_of_gt0 => // a1; apply: init_weights_gt0. }
      rewrite rat_to_R_plus rat_to_R1 rat_to_R_opp rat_to_R_mul.
      rewrite Ropp_mult_distr_l.
      apply: ln_Taylor_upper'.
    Qed.

    Lemma R175 :
      (big_product cs
         (fun c : costs => 1 - rat_to_R eps * (rat_to_R (c astar))) <=
       rat_to_R gammaT)%R.
    Proof.          
      have H: (Rle (big_product
                     cs
                     (fun c : costs => 1 - rat_to_R eps * (rat_to_R (c astar))))
                   (rat_to_R (wT astar)))%R.
      { rewrite wT_astar_eq rat_to_R1.
        apply: Rle_refl. }
      apply: Rle_trans; first by apply: H.
      apply: rat_to_R_le.
      apply: gammaT_ge_wT_astar => //.
    Qed.

    Lemma ler_contra (R : realFieldType) (x y : R) : ~~(x <= y) -> y < x.
    Proof.
      rewrite ler_eqVlt; move/negP.
      case H: (x < y); first by rewrite orbC.
      case H2: (x == y) => // _.
      case H3: (y < x) => //.
      have H4: x != y.
      { by apply/negP => H5; rewrite H5 in H2. }
      by move: (ltr_total H4); rewrite H H3.
    Qed.      
    
    Lemma eps_mult_cost_le12 a c (H : c \in cs) :
      (rat_to_R eps * rat_to_R (c a) <= 1/2)%R.
    Proof.
      have ->: (1/2 = 1/2*1)%R by field.
      case H2: (c a < 0).
      { have H3: (rat_to_R eps * rat_to_R (c a) <= 0)%R.
        { move: rat_to_R_eps_le_one_half => H3.
          have H4: (rat_to_R (c a) < 0)%R.
          { clear - H2.
            rewrite -rat_to_R0.
            by apply: rat_to_R_lt. }
          move: rat_to_R_eps_gt0 => H5.
          clear - H4 H5; move: H4 H5.
          move: (rat_to_R eps) => x; move: (rat_to_R (c a)) => y H1 H2.
          have H3: (x * y <= y * 0)%R.
          { rewrite Rmult_comm.
            by left; apply Rmult_lt_gt_compat_neg_l. }
          apply: Rle_trans; first by apply: H3.
          rewrite Rmult_0_r; apply: Rle_refl. }
        apply: Rle_trans; first by apply: H3.
        fourier. }
      apply: Rmult_le_compat.
      { apply: rat_to_R_eps_pos. }
      { rewrite -rat_to_R0; apply: rat_to_R_le.
        have H3: 0 <= c a.
        { clear - H2; rewrite ltr_def in H2.
          move: H2; rewrite andb_false_iff; case.
          { rewrite /negb; case H: (0 == c a) => //.
            by move: (eqP H) => <-. }
          by move => H; apply: ltrW; apply: ler_contra; rewrite H. }
        by []. }
      { apply: Rle_trans; first by apply: rat_to_R_eps_le_one_half.
        fourier. }
      rewrite -rat_to_R1.
      apply: rat_to_R_le.
      have H3: (c a <= 1).
      { move: (CMAX H a) => H3.
        move: (ler_norm (c a)) => H4.
        apply: ler_trans; first by apply: H4.
        by []. }
      by [].
    Qed.
    
    Lemma one_nepscost_ge0 a c (H : c \in cs) :     
      (0 <= 1 - rat_to_R eps * rat_to_R (c a))%R.
    Proof.
      apply: one_minus_pos.
      apply: Rle_trans; first by apply: eps_mult_cost_le12.
      fourier.
    Qed.
      
    Lemma R176_aux :
      (big_product cs
         (fun c : costs => exp (-rat_to_R eps * rat_to_R (c astar) +
                                -((rat_to_R eps)^2 * (rat_to_R (c astar))^2))) <=
       rat_to_R gammaT)%R.
    Proof.
      apply: Rle_trans; last by apply: R175.
      apply: big_product_le.
      { move => c H; left; apply: exp_pos. }
      { by move => c H; apply: one_nepscost_ge0. }
      move => c H.
      have H2: (rat_to_R eps * rat_to_R (c astar) <= 1/2)%R.
      { by apply: eps_mult_cost_le12. }
      move: H2.
      move: (rat_to_R eps) => x.
      move: (rat_to_R (c astar)) => y.
      have ->: (x^2*y^2 = (x*y)^2)%R by rewrite Rpow_mult_distr.
      rewrite -Ropp_mult_distr_l.
      move: (x * y)%R => z H2.
      by apply: exp_Taylor_lower.
    Qed.
  End R173_175_176_aux.        

  Lemma gamma_prod_aux (cs : seq costs) c_bogus
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1) :
    gamma (weights_of cs init_weights) =
    #|A|%:R * 
    \prod_(cs' <- @subSeqs cs CMAX)
     (1 - eps * @expCost (head c_bogus (projT1 cs'))
                         (behead (projT1 cs'))
                         (CMAXb_CMAX (CMAXb_behead (projT2 cs')))).
  Proof.
    elim: cs CMAX.
    { by move=> CMAX; rewrite /= big_nil mulr1 gamma0_sizeA. }
    move=> a l H CMAX; rewrite big_cons /=.
    rewrite gammaT_Tprod1.
    { by move=> c0 H2 a1; apply: CMAX; rewrite in_cons; apply/orP; right. }
    move=> pf0.
    rewrite H.
    rewrite -mulrA; f_equal.
    rewrite mulrC.
    move: (ssrfun.svalP _)=> pf1.
    move: (subSeqs_aux_obligation_2 _ _)=> pf2.
    move: (CMAXb_CMAX _)=> pf3.
    f_equal.
    rewrite /subSeqs.
    move: (CMAX_seq_subSeqs_of _)=> pf4.
    apply: congr_big=> //.
    f_equal. move => Hl pfEq.
    rewrite /subSeqs_aux. congruence.
    apply: proof_irrelevance.
  Qed.

  Section R174.
  Lemma gamma_prod (cs : seq costs) c_bogus
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1) :
    (rat_to_R (gamma (weights_of cs init_weights)) <=
     rat_to_R #|A|%:R * 
     big_product
       (@subSeqs cs CMAX)
       (fun cs' => 
          (exp (-rat_to_R eps *
                 rat_to_R (@expCost (head c_bogus (projT1 cs'))
                                    (behead (projT1 cs'))
                                    (CMAXb_CMAX (CMAXb_behead (projT2 cs'))))))))%R.
  Proof.
    elim: cs CMAX.
    { by move => CMAX; rewrite /= Rmult_1_r gamma0_sizeA; apply: Rle_refl. }
    move => a l H CMAX /=.
    apply: Rle_trans; [apply: gammaT_exp_neps|].
    { by move=> c0 H2 a1; apply: CMAX; rewrite in_cons; apply/orP; right. }
    rewrite [(exp _ * _)%R]Rmult_comm -Rmult_assoc.
    apply: Rmult_le_compat; last by apply: Rle_refl.
    { rewrite -rat_to_R0; apply: rat_to_R_le.
      apply: gamma_ge0.
      move => a1; apply/ltrW; apply: weights_of_gt0.
      { by move => c H2; apply: CMAX; rewrite in_cons; apply/orP; right. }
      move => a2; apply: init_weights_gt0. }
    { rewrite /Rle; left; apply: exp_pos. }
    apply: Rle_trans; [apply: H|].
    { by move=> c0 H2 a1; apply: CMAX; rewrite in_cons; apply/orP; right. }
    apply: Rmult_le_compat_l.
    { left; apply: rat_to_R_Acard_gt0. }
    have H2: forall x y, (x = y -> x <= y)%R.
    { move => x y ->; apply: Rle_refl. }
    apply: H2.
    apply: big_product_ext => //.
    rewrite /subSeqs; f_equal.
    apply: proof_irrelevance.
  Qed.
  
  Lemma R174 (cs : seq costs) c_bogus
        (CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1) :
    (rat_to_R (gamma (weights_of cs init_weights)) <=
    (rat_to_R #|A|%:R * 
     (exp
        (-rat_to_R eps *
          big_sum
            (@subSeqs cs CMAX)
            (fun cs' => 
               rat_to_R (@expCost (head c_bogus (projT1 cs'))
                                  (behead (projT1 cs'))
                                  (CMAXb_CMAX (CMAXb_behead (projT2 cs')))))))))%R.
  Proof.
    apply: Rle_trans; first by apply: gamma_prod.
    rewrite big_product_exp_sum; apply: Rmult_le_compat_l.
    { left; apply: rat_to_R_Acard_gt0. }
    rewrite big_sum_scalar; apply: Rle_refl.
  Qed.    
  End R174.
  
  Lemma exp_increasing' x y : (x <= y -> exp x <= exp y)%R.
  Proof.
    case; first by move => H; left; apply: exp_increasing.
    move => ->; apply: Rle_refl.
  Qed.    
  
  Section R176.
    Variable cT : costs.
    Variable cs : seq costs.
    Variable CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1.
    Variable cT_range : forall a, `|cT a| <= 1. 

    Notation astar := (best_action cs).
    Notation OPT := (\sum_(c <- cs) c astar).
    Notation wT := (weights_of cs init_weights). 
    Notation gammaT := (gamma wT).
    Notation OPTR := (rat_to_R OPT).
    Notation cs_subSeqs := (@subSeqs cs CMAX).
    Notation epsR := (rat_to_R eps).
    Notation size_A := (rat_to_R #|A|%:R).

    Notation T := (INR (size cs)).
    Hypothesis T_ge1 : (1 <= T)%R.
    
    Lemma R176_aux2 :
      (big_product cs
         (fun c : costs => exp (-rat_to_R eps * rat_to_R (c astar) +
                                -((rat_to_R eps)^2))) <=
       rat_to_R gammaT)%R.
    Proof.
      apply: Rle_trans; last by apply: R176_aux.
      apply: big_product_le.
      { move => c H; left; apply: exp_pos. }
      { move => c H; left; apply: exp_pos. }
      move => c H.
      set (x := (-_ * _ + -_)%R).
      set (y := (-_ * _ + -_)%R).
      apply: exp_increasing'; rewrite /x /y.
      apply: Rplus_le_compat_l.
      apply: Ropp_le_contravar.
      have ->: (epsR^2 = epsR^2*1)%R.
      { by rewrite Rmult_1_r. }
      apply: Rmult_le_compat; try fourier.
      { rewrite Rmult_1_r.
        apply: pow_le.
        left; apply: rat_to_R_eps_gt0. }
      by apply: pow2_ge_0.
      have H3: (-1 <= rat_to_R (c astar) <= 1)%R.
      { split.
        { clear x y.
          move: (CMAX H astar) => H2.
          rewrite ler_norml in H2; case: (andP H2) => H3 _.
          rewrite -rat_to_R1n; apply: rat_to_R_le => //. }
        clear x y.
        move: (CMAX H astar) => H2.
        rewrite ler_norml in H2.
        case: (andP H2) => _ H4.
        by rewrite -rat_to_R1; apply: rat_to_R_le. }
      apply: Rle_trans; first by apply: pow_le1.
      fourier.
    Qed.

    Lemma R176 : (exp (-epsR*OPTR - epsR^2*T) <= rat_to_R gammaT)%R.
    Proof.
      apply: Rle_trans; last by apply: R176_aux2.
      rewrite big_product_exp_sum.
      apply: exp_increasing'.
      rewrite big_sum_plus.
      rewrite big_sum_scalar.
      rewrite big_sum_constant.
      rewrite rat_to_R_sum.
      rewrite /Rminus.
      rewrite Ropp_mult_distr_l.
      rewrite [(-epsR^2 * _)%R]Rmult_comm.
      apply: Rle_refl.
    Qed.        
  End R176.      
  
  Section R177.
    Variable cT : costs.
    Variable cs : seq costs.
    Variable CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1.
    Variable cT_range : forall a, `|cT a| <= 1. 

    Notation astar := (best_action cs).
    Notation OPT := (\sum_(c <- cs) c astar).
    Notation OPTR := (rat_to_R OPT).
    Notation cs_subSeqs := (@subSeqs cs CMAX).
    Notation epsR := (rat_to_R eps).
    Notation size_A := (rat_to_R #|A|%:R).
    Notation expCostR cs :=
      (rat_to_R (expCost (head cT (projT1 cs))
                         (CMAXb_CMAX (CMAXb_behead (projT2 cs))))).
    Notation T := (INR (size cs)).
    Hypothesis T_ge1 : (1 <= T)%R.
    
    Lemma epsR_lt1 : (epsR < 1)%R.
    Proof.
      apply: Rle_lt_trans; first by apply: rat_to_R_eps_le_one_half.
      fourier.
    Qed.

    Lemma R174_176 :
      (exp (-epsR*OPTR - epsR^2*T) <=
       size_A * exp (-epsR * big_sum cs_subSeqs (fun c => expCostR c)))%R.
    Proof.
      apply: Rle_trans; first by apply: R176.
      by apply: R174.
    Qed.

    Lemma R177 :
      (big_sum cs_subSeqs (fun cs => expCostR cs) <=
       OPTR + epsR * INR (length cs) + ln size_A / epsR)%R.
    Proof.
      move: R174_176 => H; move: (ln_le (exp_pos _) H).
      rewrite ln_exp rat_to_R_sum ln_mult; last by apply: exp_pos. Focus 2.
      apply: rat_to_R_Acard_gt0.
      rewrite ln_exp.
      move: (big_sum _ _) => OPT.
      move: (ln _) => SIZE.
      move: (big_sum _ _) => EXPECTED => H2.
      have H3: ((/-epsR) * (-epsR*OPT - epsR^2*T) >= (/-epsR) * (SIZE + - epsR*EXPECTED))%R.
      { apply: Rle_ge.
        apply: Rmult_le_compat_neg_l.
        { rewrite -Ropp_inv_permute; last by apply: rat_to_R_eps_neq0.
          rewrite -Ropp_0; apply: Ropp_ge_le_contravar.
          apply: Rle_ge.
          have ->: (/epsR = 1*/epsR)%R by rewrite Rmult_1_l.
          apply: Rle_mult_inv_pos; try fourier.
          apply: rat_to_R_eps_gt0. }
        apply: H2. }
      clear H2.
      have epsR_neq : (epsR <> 0)%R.
      { move => H4.
        move: rat_to_R_eps_gt0; rewrite H4.
        apply: Rlt_irrefl. }
      have nepsR_neq : (-epsR <> 0)%R.
      { by apply: Ropp_neq_0_compat. }
      have H4: (OPT + epsR*T >= EXPECTED - SIZE/epsR)%R.
      { move: H3.
        have ->: (/-epsR * (-epsR*OPT - epsR^2*T) = OPT + epsR*T)%R.
        { rewrite Rmult_plus_distr_l -Rmult_assoc.
          rewrite -Rinv_l_sym => //.
          rewrite Rmult_1_l.
          rewrite -Ropp_mult_distr_r -Rmult_assoc.
          rewrite /pow Rmult_1_r -Ropp_inv_permute // -Rmult_assoc.
          rewrite -Ropp_mult_distr_l -Rinv_l_sym => //.
          by rewrite -2!Ropp_mult_distr_l Ropp_involutive Rmult_1_l. }
        have ->: (/-epsR * (SIZE + -epsR*EXPECTED) = EXPECTED - SIZE/epsR)%R.
        { rewrite Rmult_plus_distr_l -Rmult_assoc -Rinv_l_sym => //.
          rewrite Rmult_1_l Rmult_comm -Ropp_inv_permute // -Ropp_mult_distr_r //.
          rewrite Rplus_comm //. }
        by []. }
      clear - H4 epsR_neq.
      move: (Rge_le _ _ H4) => H5; clear H4.
      have H6: (SIZE/epsR + (EXPECTED - SIZE/epsR) <= SIZE/epsR + (OPT + epsR*T))%R.
      { by apply: Rplus_le_compat_l. }
      clear - H6 epsR_neq; move: H6.
      have ->: (SIZE/epsR + (EXPECTED - SIZE/epsR) = EXPECTED)%R.
      { by rewrite -Rplus_assoc [(SIZE/epsR + _)%R]Rplus_comm Rplus_assoc; field. }
      rewrite Rplus_assoc Rplus_comm Rplus_assoc.
      have ->: INR (length cs) = T by [].      
      by [].
    Qed.
  End R177.
End weights.

Section weights_noregret.
  Local Open Scope ring_scope.

  Variable A : finType.   (** The strategy space *)
  Variable a0 a1 : A.     (** ... has size at least 2. *)
  Variable a01_distinct : a0 != a1.

  Lemma cardA_ge2 : (2 <= #|A|)%N.
  Proof.
    have H: (#|pred2 a0 a1| <= #|A|)%N.
    { by apply: subset_leq_card; apply/subsetP. }
    have H2: (1 < #|pred2 a0 a1|)%N by rewrite card2 a01_distinct.
    by apply: leq_trans; first by apply: H2.
  Qed.    
  
  Variable cs : seq (costs A).
  Variable CMAX : forall c, c \in cs -> forall a : A, `|c a| <= 1.
  Variable cs_size_gt0 : (0 < size cs)%N.

  (** [costs_default] remains unused assuming [size cs > 0]. *)
  Definition costs_default : costs A := finfun (fun _ => 1).
  Lemma costs_default_in_range : forall a : A, `|costs_default a| <= 1.
  Proof. by move=> a; rewrite /costs_default ffunE. Qed.
  
  Variable eps : rat.
  Variable eps_range : 0 < eps <= 1/2%:R.
  
  Notation astar := (best_action a0 cs).
  Notation OPT := (\sum_(c <- cs) c astar).
  Notation OPTR := (rat_to_R OPT).
  Notation cs_subSeqs := (@subSeqs _ cs CMAX).
  Notation epsR := (rat_to_R eps).
  Notation size_A := (rat_to_R #|A|%:R).
  Notation T := (INR (size cs)).

  Delimit Scope R_scope with R.

  Lemma T_gt0 : (0 < T)%R.
  Proof. by apply: lt_0_INR; move: cs_size_gt0; apply/ltP. Qed.

  Lemma Tinv_gt0 : (0 < / T)%R.
  Proof. by apply: Rinv_0_lt_compat; apply: T_gt0. Qed.

  Lemma size_A_ge0 : (0 <= ln (rat_to_R #|A|%:R))%R.
  Proof.
    rewrite -ln_1; apply: ln_le.
    lra.
    apply: (rat_to_R_Acard_ge1 a0).
  Qed.

  Lemma size_A_gt0 : (0 < ln (rat_to_R #|A|%:R))%R.
  Proof.
    case H: size_A_ge0 => // [x].
    rewrite -ln_1.
    apply: ln_increasing.
    { apply: Rlt_0_1. }
    rewrite -rat_to_R1.
    apply: rat_to_R_lt.
    move: cardA_ge2.
    by rewrite -(@ltr_nat rat_numDomainType).
  Qed.

  Lemma T_neq0 : (T <> 0)%R.
  Proof.
    move => H; move: T_gt0; rewrite H.
    lra.
  Qed.

  Lemma Tinv_ge0 : (0 <= / T)%R.
  Proof. apply: Rlt_le; apply: Tinv_gt0. Qed.

  Lemma T_ge0 : (0 <= T)%R.
  Proof. apply: Rlt_le; apply: T_gt0. Qed.

  Lemma T_ge1 : (1 <= T)%R.
  Proof.
    have ->: (1 = INR 1)%R by [].
    apply: le_INR.
    move: (ltP cs_size_gt0) => H2.
    omega.
  Qed.    
  
  (** The expected cost at time [T = size cs]. That is, the expected
      cost of [head cs] given the weights table computed from [behead cs]. *)
  Definition expCostR (cs : CMAX_costs_seq A) : R :=
    rat_to_R
      (expCost a0 eps_range
               (head costs_default (projT1 cs))
               (CMAXb_CMAX (CMAXb_behead (projT2 cs)))).
  
  (** Assuming [cs = [c_T; c_(T-1); ...; c_1]], 
      [expsCostsR] is the sum of 
        [expCostR [c_1] + expCostR [c_2; c_1] + ...
         expCostR [cT; ...; c2; c_1]]. *)
  Definition expCostsR : R :=
    (big_sum cs_subSeqs (fun cs0 => expCostR cs0))%R.
  
  Lemma weights_noregret :
    (expCostsR <= OPTR + epsR * T + (ln size_A / epsR))%R.
  Proof. apply: R177. Qed.
  
  Lemma perstep_weights_noregret :
    ((expCostsR - OPTR) / T <= epsR + ln size_A / (epsR * T))%R.
  Proof.      
    have H0: (expCostsR - OPTR <= epsR * T + (ln size_A / epsR))%R.
    { have H1: (expCostsR - OPTR <= OPTR + epsR * T + (ln size_A / epsR) - OPTR)%R.
      { by rewrite /Rminus; apply: Rplus_le_compat_r; apply: weights_noregret. }
      apply: Rle_trans; first by apply: H1.
      rewrite /Rminus Rplus_comm Rplus_assoc -Rplus_assoc. 
      by rewrite [(- _ + _)%R]Rplus_comm Rplus_opp_r Rplus_0_l; apply: Rle_refl. }
    have H1: ((expCostsR - OPTR) / T <= (epsR * T + (ln size_A / epsR)) / T)%R.
    { rewrite /Rdiv; apply: Rmult_le_compat_r=> //.
      by apply: Rlt_le; apply: Tinv_gt0. }
    clear H0; apply: Rle_trans; first by apply: H1. clear H1.
    have H: ((epsR * T + ln size_A / epsR) / T = epsR + ln size_A / (epsR * T))%R.
    { rewrite Rdiv_plus_distr /Rdiv Rmult_assoc -Rinv_r_sym.
      rewrite Rmult_1_r Rmult_assoc Rinv_mult_distr=> //.
      by apply: rat_to_R_eps_neq0.
      by move: T_gt0=> H H2; rewrite H2 in H; apply Rlt_irrefl in H.
      by move: T_gt0=> H H2; rewrite H2 in H; apply Rlt_irrefl in H. }
    by rewrite H; clear H; apply: Rle_refl.
  Qed.

  Variable r : R. (* the error term *)
  Variable r_ok : (r <> -1)%R. (* => (1+r) <> 0 *)
  Notation vR := (rat_to_R eps).
  Variable vR_ok : (vR = (1 + r) * sqrt (ln size_A / T))%R.

  Lemma r1_neq0 : (1 + r <> 0)%R.
  Proof.
    rewrite -(Rplus_opp_l r); move/Rplus_eq_reg_r => H.
    move: r_ok; rewrite -(Ropp_involutive r) -H //.
  Qed.    

  Lemma sqrt_Rinv (a : R) (Hlt : (0 < a)%R) : (sqrt (/a) = /sqrt a)%R.
  Proof.
    have ->: (/a = 1 / a)%R by rewrite /Rdiv Rmult_1_l.
    have ->: (/sqrt a = 1 / sqrt a)%R by rewrite /Rdiv Rmult_1_l.
    by rewrite sqrt_div_alt // sqrt_1.
  Qed.
  
  Lemma sqrt_Rinv_mult (a : R) (Hlt : (0 < a)%R) : (sqrt (/a) * a = sqrt a)%R.
  Proof.                                                     
    have ->: (sqrt (/a) * a = sqrt (/a) * (sqrt a * sqrt a))%R.
    { rewrite sqrt_sqrt //.
      apply: Rlt_le => //. }
    have Hle: (0 <= a)%R.
    { by apply: Rlt_le. }
    rewrite -Rmult_assoc -sqrt_mult //.
    { rewrite -Rinv_l_sym.
      { rewrite sqrt_1 Rmult_1_l //. }
      suff: (0 <> a)%R.
      { by move => H H2; rewrite H2 in H; apply: H. } 
      by apply: Rlt_not_eq. }
    apply: Rlt_le; apply: Rinv_0_lt_compat => //. 
  Qed.

  Lemma sqrt_mult_Rinv (a : R) (Hlt : (0 < a)%R) : (sqrt a * (/a) = sqrt (/a))%R.
  Proof.                                                     
    have ->: (sqrt a * (/a) = sqrt a * (sqrt (/a) * sqrt (/a)))%R.
    { rewrite sqrt_sqrt //.
      apply: Rlt_le => //.
      by apply: Rinv_0_lt_compat. }
    have Hle: (0 <= a)%R.
    { by apply: Rlt_le. }
    have Hle_inv: (0 <= /a)%R.
    { by apply: Rlt_le; apply: Rinv_0_lt_compat. }
    rewrite -Rmult_assoc -sqrt_mult // -Rinv_r_sym.
    { rewrite sqrt_1 Rmult_1_l //. }
    by move => H; rewrite H in Hlt; apply Rlt_irrefl in Hlt.
  Qed.
  
  Lemma weights_noregret' :
    (expCostsR <=
     OPTR + (1+r) * sqrt (T*ln size_A) + sqrt (T*ln size_A) / (1+r))%R.
  Proof.
    apply: Rle_trans; first by apply: weights_noregret.
    rewrite /epsR.
    set (OPTR' := rat_to_R (\sum_(c <- cs) c astar)).
    suff:
      (vR * T + (ln size_A) / vR <=
       (1+r) * sqrt (T*ln size_A) + sqrt (T*ln size_A) / (1+r)
       )%R.
    { set (size_A' := rat_to_R #|A|%:R).
      rewrite Rplus_assoc.
      move => H; rewrite Rplus_assoc; apply: Rplus_le_compat.
      by apply: Rle_refl.
      apply: Rle_trans; last by apply: H.
      by apply: Rle_refl. }
    rewrite vR_ok.    
    set (size_A' := rat_to_R #|A|%:R).
    set (a := (1+r)%R).
    have size_A'_ge0 : (0 <= ln size_A')%R.
    { apply: size_A_ge0. }
    move: T_ge0 => T_ge0.
    rewrite /Rdiv !sqrt_mult_alt //.
    have ->:
      (a * (sqrt (ln size_A') * sqrt (/ T)) * T =
       a * (sqrt T * sqrt (ln size_A')))%R.
    { rewrite Rmult_assoc; f_equal.
      rewrite Rmult_assoc.
      have ->: (sqrt (/T) * T = sqrt T)%R.
      { apply: sqrt_Rinv_mult.
        apply: T_gt0. }
      by rewrite Rmult_comm. }
    have ->:
      (ln size_A' * / (a * (sqrt (ln size_A') * sqrt (/ T))) =
       sqrt T * sqrt (ln size_A') * / a)%R.
    { rewrite Rinv_mult_distr.
      { rewrite Rinv_mult_distr.
        { have ->: (/sqrt(/T) = sqrt T)%R.
          { rewrite sqrt_Rinv.
            { rewrite Rinv_involutive //.
              rewrite -sqrt_0 => H; apply sqrt_inj in H => //.
              { by apply: T_neq0. }
              apply: Rle_refl. }
            apply: T_gt0. }
          rewrite Rmult_comm.
          rewrite Rmult_assoc.
          have ->:
           (/sqrt (ln size_A') * sqrt T * ln size_A' =
            sqrt T * sqrt (ln size_A'))%R.
          { rewrite Rmult_comm -Rmult_assoc -sqrt_Rinv.
            { rewrite [(ln _ * _)%R]Rmult_comm sqrt_Rinv_mult.
              { rewrite Rmult_comm //. }
              apply: size_A_gt0. }
            apply: size_A_gt0. }
          by rewrite Rmult_comm. }
        { rewrite -sqrt_0 => H; apply sqrt_inj in H => //.
          { by move: size_A_gt0; move/Rlt_not_eq; rewrite H. }
          by apply: Rle_refl. }
        rewrite -sqrt_0 => H; apply sqrt_inj in H.
        { move: Tinv_gt0; rewrite H; apply/Rlt_irrefl. }
        { apply: Tinv_ge0. }
        apply: Rle_refl. }
      { apply: r1_neq0. }
      rewrite -sqrt_mult //.
      { rewrite -sqrt_0 => H; apply sqrt_inj in H => //.
        { apply Rmult_integral in H; case: H => H.
          { by move: size_A_gt0; rewrite H; move/Rlt_irrefl. }
          by move: Tinv_gt0; rewrite H; move/Rlt_irrefl. }
        { apply: Rle_mult_inv_pos => //.
          apply: T_gt0. }
        apply: Rle_refl. }
      apply: Tinv_ge0. }
    apply: Rle_refl.
  Qed.

  Lemma Rle_minus_const (rx r1 r2 : R) : (r1 <= r2 -> r1 - rx <= r2 - rx)%R.
  Proof. by apply: Rplus_le_compat_r. Qed.

  Lemma Rle_div_const (rx r1 r2 : R) (rxinv_ge : (0 <= /rx)%R) :
    (r1 <= r2 -> r1/rx <= r2/rx)%R.
  Proof. by apply: Rmult_le_compat_r. Qed.
  
  Lemma perstep_weights_noregret' :
    ((expCostsR - OPTR) / T <=
     (1+r) * sqrt (ln size_A / T) + sqrt (ln size_A / T) / (1+r))%R.
  Proof.
    move: weights_noregret'.
    set (OPTR := rat_to_R _).
    set (lnA := ln (rat_to_R _)).
    set (x := (1 + r)%R).
    move/(Rle_minus_const OPTR).
    move/(@Rle_div_const T _ _ Tinv_ge0) => H.
    apply: Rle_trans; first by apply: H.
    rewrite Rplus_comm [(OPTR + _)%R]Rplus_comm -Rplus_assoc.
    set (y := (sqrt (T*lnA) / x + x*(sqrt (T*lnA)))%R).
    have ->: (y + OPTR - OPTR = y)%R.
    { rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r //. }
    move: T_ge0 Tinv_ge0 T_gt0 size_A_ge0 => H0 H1 H2 H3.
    rewrite /y !sqrt_mult //.
    rewrite /Rdiv Rmult_plus_distr_r.
    rewrite Rmult_comm -2![(/T * (_ * _))%R]Rmult_assoc.
    rewrite [(/T * _)%R]Rmult_comm sqrt_mult_Rinv //.
    rewrite Rplus_comm; apply: Rplus_le_compat; last first.
    { rewrite Rmult_assoc [(sqrt lnA * _)%R]Rmult_comm -Rmult_assoc Rmult_comm.
      rewrite Rmult_assoc; apply: Rle_refl. }
    rewrite [(x * _)%R]Rmult_comm Rmult_comm -2!Rmult_assoc.
    rewrite [(/T * _)%R]Rmult_comm sqrt_mult_Rinv //.
    rewrite Rmult_comm [(sqrt (/T) * _)%R]Rmult_comm; apply: Rle_refl.
  Qed.    
End weights_noregret.
