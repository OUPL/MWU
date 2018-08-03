
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : nat -> nat -> nat

val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Nat :
 sig
  val pred : nat -> nat
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val add_carry : Big.big_int -> Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big.big_int -> mask

  val sub_mask : Big.big_int -> Big.big_int -> mask

  val sub_mask_carry : Big.big_int -> Big.big_int -> mask

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val iter : ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1

  val compare_cont : comparison -> Big.big_int -> Big.big_int -> comparison

  val compare : Big.big_int -> Big.big_int -> comparison

  val eqb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1

  val to_nat : Big.big_int -> nat

  val of_succ_nat : nat -> Big.big_int

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end

module N :
 sig
  val eqb : Big.big_int -> Big.big_int -> bool
 end

module Coq_N :
 sig
  type t = Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val compare : Big.big_int -> Big.big_int -> comparison

  val ltb : Big.big_int -> Big.big_int -> bool

  val to_nat : Big.big_int -> nat

  val of_nat : nat -> Big.big_int

  val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end

module Z :
 sig
  val one : Big.big_int
 end

module Coq_Z :
 sig
  val double : Big.big_int -> Big.big_int

  val succ_double : Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  val pos_sub : Big.big_int -> Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val opp : Big.big_int -> Big.big_int

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val pow_pos : Big.big_int -> Big.big_int -> Big.big_int

  val compare : Big.big_int -> Big.big_int -> comparison

  val leb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val eqb : Big.big_int -> Big.big_int -> bool

  val max : Big.big_int -> Big.big_int -> Big.big_int

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end

val le_lt_dec : nat -> nat -> bool

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val shift_pos : Big.big_int -> Big.big_int -> Big.big_int

type q = { qnum : Big.big_int; qden : Big.big_int }

val qnum : q -> Big.big_int

val qden : q -> Big.big_int

val qcompare : q -> q -> comparison

val qle_bool : q -> q -> bool

val qmult : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val n_of_digits : bool list -> Big.big_int

val n_of_ascii : char -> Big.big_int

module type DecidableType =
 DecidableTypeOrig

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end

module type WS =
 sig
  module E :
   DecidableType

  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Raw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val coq_R_equal_correct :
    ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
    list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module type Int =
 sig
  type t

  val i2z : t -> Big.big_int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int :
 sig
  type t = Big.big_int

  val _0 : Big.big_int

  val _1 : Big.big_int

  val _2 : Big.big_int

  val _3 : Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val opp : Big.big_int -> Big.big_int

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val max : Big.big_int -> Big.big_int -> Big.big_int

  val eqb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val leb : Big.big_int -> Big.big_int -> bool

  val eq_dec : Big.big_int -> Big.big_int -> bool

  val gt_le_dec : Big.big_int -> Big.big_int -> bool

  val ge_lt_dec : Big.big_int -> Big.big_int -> bool

  val i2z : t -> Big.big_int
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> nat

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

  val elements : 'a1 tree -> (key * 'a1) list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t * 'elt) list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
         * 'elt coq_R_mem

      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

      val find : key -> 'a1 t -> 'a1 option

      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
         * 'elt coq_R_find

      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

      val remove : key -> 'a1 t -> 'a1 t

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_remove

      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of 'elt t * 'a
      | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
         * ('elt, 'a) coq_R_fold

      val coq_R_fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val coq_R_fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * X.t compare0
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons :
        key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
        (key * 'a3) list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key * 'a1) list
   end
 end

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module WFacts_fun :
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 sig
  val eqb : E.t -> E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module WFacts :
 functor (M:WS) ->
 sig
  val eqb : M.E.t -> M.E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module Facts :
 functor (M:WS) ->
 sig
  val eqb : M.E.t -> M.E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module WProperties_fun :
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 sig
  module F :
   sig
    val eqb : E.t -> E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

  val of_list : (M.key * 'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key * 'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
 end

module WProperties :
 functor (M:WS) ->
 sig
  module F :
   sig
    val eqb : M.E.t -> M.E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

  val of_list : (M.key * 'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key * 'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
 end

module Properties :
 functor (M:WS) ->
 sig
  module F :
   sig
    val eqb : M.E.t -> M.E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

  val of_list : (M.key * 'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key * 'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
 end

val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

type d = { num : Big.big_int; den : Big.big_int }

val num : d -> Big.big_int

val den : d -> Big.big_int

val d_to_Q : d -> q

val d0 : d

val d1 : d

val dadd : d -> d -> d

val dmult : d -> d -> d

val dopp : d -> d

val dsub : d -> d -> d

val dle_bool : d -> d -> bool

val dlt_bool : d -> d -> bool

type 't showable =
  't -> char list
  (* singleton inductive, whose constructor was mkShowable *)

val to_string : 'a1 showable -> 'a1 -> char list

val eprint_natchar : Big.big_int -> 'a1 -> 'a1

val eprint_ZdivPos : Big.big_int -> Big.big_int -> 'a1 -> 'a1

val eprint_ascii : char -> 'a1 -> 'a1

val eprint_string : char list -> 'a1 -> 'a1

val nl : char

val cr : char

val newline : char list

val eprint_newline : 'a1 -> 'a1

val eprint_Q : q -> 'a1 -> 'a1

val print_Qvector : 'a1 showable -> ('a1 * q) list -> 'a2 -> 'a2

val print_Dvector : 'a1 showable -> ('a1 * d) list -> 'a2 -> 'a2

val showable_nat : nat showable

val showable_N : Coq_N.t showable

module type BOUND =
 sig
  val n : nat
 end

module OrdNatDep :
 functor (B:BOUND) ->
 sig
  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  val coq_val : t' -> Coq_N.t

  type t = t'

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

type 't enumerable = 't list

val enumerable_fun : 'a1 enumerable -> 'a1 list

module type MyOrderedType =
 sig
  type t

  val t0 : t

  val enumerable : t enumerable

  val showable : t showable

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedType_of_MyOrderedType :
 functor (A:MyOrderedType) ->
 sig
  type t = A.t

  val compare : A.t -> A.t -> A.t compare0

  val eq_dec : A.t -> A.t -> bool
 end

module MyOrdNatDep :
 functor (B:BOUND) ->
 sig
  module N :
   sig
    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  val coq_val : t' -> Coq_N.t

  type t = t'

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool

  val t0 : t'

  val enumerate_rec : nat -> t list

  val lt_dec : nat -> nat -> bool

  val enumerate_t : t list

  val enumerable : t enumerable

  val showable : t showable
 end

module MyOrdNatDepProps :
 functor (B:BOUND) ->
 sig
  module M :
   sig
    module N :
     sig
      type t' = Coq_N.t
        (* singleton inductive, whose constructor was mk *)

      val coq_val : t' -> Coq_N.t

      type t = t'

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool

    val t0 : t'

    val enumerate_rec : nat -> t list

    val lt_dec : nat -> nat -> bool

    val enumerate_t : t list

    val enumerable : t enumerable

    val showable : t showable
   end

  module N :
   sig
    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  val coq_val : t' -> Coq_N.t

  type t = t'

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool

  val t0 : t'

  val enumerate_rec : nat -> t list

  val lt_dec : nat -> nat -> bool

  val enumerate_t : t list

  val enumerable : t enumerable

  val showable : t showable

  val enumerate_rec_erased : nat -> Big.big_int list

  val enumerate_rec_erased_nat : nat -> nat list

  val coq_Ordinal_of_t : t -> ordinal

  val val_of_Ordinal : ordinal -> Big.big_int
 end

type val0 = d
  (* singleton inductive, whose constructor was QVal *)

type binop =
| BPlus
| BMinus
| BMult

type 'a expr =
| EVal of val0
| EOpp of 'a expr
| EWeight of 'a
| ECost of 'a
| EEps
| EBinop of binop * 'a expr * 'a expr

type 'a com =
| CSkip
| CUpdate of ('a -> 'a expr)
| CRecv
| CSend
| CSeq of 'a com * 'a com
| CIter of Coq_N.t * 'a com

val mult_weights_body : 'a1 com

val mult_weights_init : 'a1 com

val mult_weights : Coq_N.t -> 'a1 com

type 'a clientOracle = { oracle_init_state : __; oracle_bogus_chan : 
                         __; oracle_prerecv : (__ -> __ -> bool * __);
                         oracle_recv : (__ -> __ -> ('a * d) list * __);
                         oracle_presend : (__ -> ('a * d) list -> bool);
                         oracle_send : (__ -> ('a * d) list -> __ * __) }

type 'a t1 = __

val oracle_init_state : 'a1 clientOracle -> 'a1 t1

type 'a oracle_chanty = __

val oracle_bogus_chan : 'a1 clientOracle -> 'a1 oracle_chanty

val oracle_prerecv :
  'a1 clientOracle -> 'a1 t1 -> 'a1 oracle_chanty -> bool * 'a1 t1

val oracle_recv :
  'a1 clientOracle -> 'a1 t1 -> 'a1 oracle_chanty -> ('a1 * d) list * 'a1 t1

val oracle_presend : 'a1 clientOracle -> 'a1 t1 -> ('a1 * d) list -> bool

val oracle_send :
  'a1 clientOracle -> 'a1 t1 -> ('a1 * d) list -> 'a1 oracle_chanty * 'a1 t1

module MWUPre :
 functor (A:MyOrderedType) ->
 sig
  module A' :
   sig
    type t = A.t

    val compare : A.t -> A.t -> A.t compare0

    val eq_dec : A.t -> A.t -> bool
   end

  module M :
   sig
    module E :
     sig
      type t = A.t

      val compare : A.t -> A.t -> A.t compare0

      val eq_dec : A.t -> A.t -> bool
     end

    module Raw :
     sig
      type key = A.t

      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Z_as_Int.t

      val cardinal : 'a1 tree -> nat

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : A.t -> 'a1 tree -> bool

      val find : A.t -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : A.t -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : A.t -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> A.t -> 'a1 -> ('a1 enumeration -> bool) ->
        'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = A.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : A.t -> A.t -> bool

          val lt_dec : A.t -> A.t -> bool

          val eqb : A.t -> A.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = A.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : A.t -> A.t -> bool

            val lt_dec : A.t -> A.t -> bool

            val eqb : A.t -> A.t -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = A.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : A.t -> A.t -> bool

            val lt_dec : A.t -> A.t -> bool

            val eqb : A.t -> A.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = A.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : A.t -> A.t -> bool

              val lt_dec : A.t -> A.t -> bool

              val eqb : A.t -> A.t -> bool
             end
           end

          type key = A.t

          type 'elt t = (A.t * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_mem_2 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_mem_3 of 'elt t * A.t * 'elt * (A.t * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_find_2 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_find_3 of 'elt t * A.t * 'elt * (A.t * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_add_2 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_add_3 of 'elt t * A.t * 'elt * (A.t * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_remove_2 of 'elt t * A.t * 'elt * (A.t * 'elt) list
          | R_remove_3 of 'elt t * A.t * 'elt * (A.t * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            A.t -> 'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * A.t * 'elt * (A.t * 'elt) list * 
             'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * A.t * 'elt * (A.t * 'elt) list
             * A.t * 'elt * (A.t * 'elt) list * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * A.t * 'elt * (A.t * 'elt) list
             * A.t * 'elt * (A.t * 'elt) list * A.t compare0
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> A.t -> 'a1 -> (A.t * 'a1) list -> __ ->
            A.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
            __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
            coq_R_equal -> 'a2

          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A.t -> 'a1 ->
            (A.t * 'a1) list -> __ -> A.t -> 'a1 -> (A.t * 'a1) list -> __ ->
            A.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
            __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
            coq_R_equal -> 'a2

          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1
            t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t -> 'a1
            -> (A.t * 'a1) list -> __ -> A.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t ->
            'a1 -> (A.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1
            t -> 'a1 t -> A.t -> 'a1 -> (A.t * 'a1) list -> __ -> A.t -> 'a1
            -> (A.t * 'a1) list -> __ -> A.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        val coq_R_mem_rec :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
           * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        val coq_R_split_rec :
          A.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        type ('elt, 'x) coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
           * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = A.t

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> nat

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  module MFacts :
   sig
    val eqb : A.t -> A.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  module MProps :
   sig
    module F :
     sig
      val eqb : A.t -> A.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

    val of_list : (M.key * 'a1) list -> 'a1 M.t

    val to_list : 'a1 M.t -> (M.key * 'a1) list

    val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3

    val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4

    val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

    val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

    val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

    val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

    val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

    val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

    val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

    val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
   end

  val cGamma : d M.t -> q

  type cstate = { coq_SCosts : d M.t; coq_SPrevCosts : d M.t list;
                  coq_SWeights : d M.t; coq_SEpsilon : d;
                  coq_SOutputs : (A.t -> q) list;
                  coq_SChan : A.t oracle_chanty; coq_SOracleSt : A.t t1 }

  val coq_SCosts : A.t clientOracle -> cstate -> d M.t

  val coq_SPrevCosts : A.t clientOracle -> cstate -> d M.t list

  val coq_SWeights : A.t clientOracle -> cstate -> d M.t

  val coq_SEpsilon : A.t clientOracle -> cstate -> d

  val coq_SOutputs : A.t clientOracle -> cstate -> (A.t -> q) list

  val coq_SChan : A.t clientOracle -> cstate -> A.t oracle_chanty

  val coq_SOracleSt : A.t clientOracle -> cstate -> A.t t1

  val mwu_send :
    A.t clientOracle -> d M.t -> A.t t1 -> A.t oracle_chanty * A.t t1

  val mwu_recv :
    A.t showable -> A.t clientOracle -> A.t oracle_chanty -> A.t t1 -> d
    M.t * A.t t1

  val eval_binopc : binop -> d -> d -> d

  val evalc : A.t clientOracle -> A.t expr -> cstate -> d option

  val update_weights :
    A.t clientOracle -> (A.t -> A.t expr) -> cstate -> d M.t option

  val weights_distr : d M.t -> A.t -> q

  val interp :
    A.t showable -> A.t clientOracle -> A.t com -> cstate -> cstate option

  val init_map : A.t enumerable -> d M.t

  val init_cstate : A.t clientOracle -> A.t enumerable -> d -> cstate

  val mwu :
    A.t showable -> A.t enumerable -> A.t clientOracle -> d -> Coq_N.t ->
    cstate option
 end

module MWU :
 functor (A__1:MyOrderedType) ->
 sig
  module A :
   sig
    type t = A__1.t

    val t0 : t

    val enumerable : t enumerable

    val showable : t showable

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module MWUPre :
   sig
    module A' :
     sig
      type t = A__1.t

      val compare : A__1.t -> A__1.t -> A__1.t compare0

      val eq_dec : A__1.t -> A__1.t -> bool
     end

    module M :
     sig
      module E :
       sig
        type t = A__1.t

        val compare : A__1.t -> A__1.t -> A__1.t compare0

        val eq_dec : A__1.t -> A__1.t -> bool
       end

      module Raw :
       sig
        type key = A__1.t

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : A__1.t -> 'a1 tree -> bool

        val find : A__1.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : A__1.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : A__1.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> A__1.t -> 'a1 -> ('a1 enumeration -> bool)
          -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = A__1.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : A__1.t -> A__1.t -> bool

            val lt_dec : A__1.t -> A__1.t -> bool

            val eqb : A__1.t -> A__1.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = A__1.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : A__1.t -> A__1.t -> bool

              val lt_dec : A__1.t -> A__1.t -> bool

              val eqb : A__1.t -> A__1.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = A__1.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : A__1.t -> A__1.t -> bool

              val lt_dec : A__1.t -> A__1.t -> bool

              val eqb : A__1.t -> A__1.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = A__1.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : A__1.t -> A__1.t -> bool

                val lt_dec : A__1.t -> A__1.t -> bool

                val eqb : A__1.t -> A__1.t -> bool
               end
             end

            type key = A__1.t

            type 'elt t = (A__1.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_mem_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_mem_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list * 
               bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
              -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
              -> 'a1 coq_R_mem -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_find_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_find_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
               * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t
              -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t
              -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_add_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_add_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
               * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1
              -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              t -> 'a1 coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1
              -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              t -> 'a1 coq_R_add -> 'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1
              -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1
              -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_remove_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
            | R_remove_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
               * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
              'a1 t -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
              'a1 t -> 'a1 coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * A__1.t * 'elt * (A__1.t * 'elt) list
               * 'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
              'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 ->
              'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
              'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 ->
              'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
              'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
              'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * A__1.t * 'elt
               * (A__1.t * 'elt) list * A__1.t * 'elt * (A__1.t * 'elt) list
               * bool * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * A__1.t * 'elt
               * (A__1.t * 'elt) list * A__1.t * 'elt * (A__1.t * 'elt) list
               * A__1.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __
              -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> A__1.t compare0 -> __ -> __ ->
              'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
              'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __
              -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> A__1.t compare0 -> __ -> __ ->
              'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
              'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __
              -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 -> (A__1.t * 'a1)
              list -> __ -> A__1.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __
              -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A__1.t -> 'a1 ->
              (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 -> (A__1.t * 'a1)
              list -> __ -> A__1.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
            -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
            -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option
            -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option
            -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple
            -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
            -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
            -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
            -> 'a2

          val coq_R_split_rec :
            A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple
            -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
            -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
            -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
            -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = A__1.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module MFacts :
     sig
      val eqb : A__1.t -> A__1.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    module MProps :
     sig
      module F :
       sig
        val eqb : A__1.t -> A__1.t -> bool

        val coq_In_dec : 'a1 M.t -> M.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (M.key * 'a1) list -> 'a1 M.t

      val to_list : 'a1 M.t -> (M.key * 'a1) list

      val fold_rec :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
        'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __
        -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
        -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
        -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 ->
        __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ ->
        'a3 -> 'a3) -> 'a1 M.t -> 'a3

      val fold_rel :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4
        -> 'a4) -> 'a4

      val map_induction :
        ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1
        -> __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

      val map_induction_bis :
        ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 ->
        'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

      val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

      val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

      val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

      val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

      val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

      val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

      val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

      val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

      val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

      val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

      val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

      val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

      val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

      val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
     end

    val cGamma : d M.t -> q

    type cstate = { coq_SCosts : d M.t; coq_SPrevCosts : d M.t list;
                    coq_SWeights : d M.t; coq_SEpsilon : d;
                    coq_SOutputs : (A__1.t -> q) list;
                    coq_SChan : A__1.t oracle_chanty;
                    coq_SOracleSt : A__1.t t1 }

    val coq_SCosts : A__1.t clientOracle -> cstate -> d M.t

    val coq_SPrevCosts : A__1.t clientOracle -> cstate -> d M.t list

    val coq_SWeights : A__1.t clientOracle -> cstate -> d M.t

    val coq_SEpsilon : A__1.t clientOracle -> cstate -> d

    val coq_SOutputs : A__1.t clientOracle -> cstate -> (A__1.t -> q) list

    val coq_SChan : A__1.t clientOracle -> cstate -> A__1.t oracle_chanty

    val coq_SOracleSt : A__1.t clientOracle -> cstate -> A__1.t t1

    val mwu_send :
      A__1.t clientOracle -> d M.t -> A__1.t t1 -> A__1.t
      oracle_chanty * A__1.t t1

    val mwu_recv :
      A__1.t showable -> A__1.t clientOracle -> A__1.t oracle_chanty ->
      A__1.t t1 -> d M.t * A__1.t t1

    val eval_binopc : binop -> d -> d -> d

    val evalc : A__1.t clientOracle -> A__1.t expr -> cstate -> d option

    val update_weights :
      A__1.t clientOracle -> (A__1.t -> A__1.t expr) -> cstate -> d M.t option

    val weights_distr : d M.t -> A__1.t -> q

    val interp :
      A__1.t showable -> A__1.t clientOracle -> A__1.t com -> cstate ->
      cstate option

    val init_map : A__1.t enumerable -> d M.t

    val init_cstate : A__1.t clientOracle -> A__1.t enumerable -> d -> cstate

    val mwu :
      A__1.t showable -> A__1.t enumerable -> A__1.t clientOracle -> d ->
      Coq_N.t -> cstate option
   end

  module A' :
   sig
    type t = A__1.t

    val compare : A__1.t -> A__1.t -> A__1.t compare0

    val eq_dec : A__1.t -> A__1.t -> bool
   end

  module M :
   sig
    module E :
     sig
      type t = A__1.t

      val compare : A__1.t -> A__1.t -> A__1.t compare0

      val eq_dec : A__1.t -> A__1.t -> bool
     end

    module Raw :
     sig
      type key = A__1.t

      type 'elt tree = 'elt MWUPre.M.Raw.tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Z_as_Int.t

      val cardinal : 'a1 tree -> nat

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : A__1.t -> 'a1 tree -> bool

      val find : A__1.t -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : A__1.t -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = 'elt MWUPre.M.Raw.triple = { t_left : 'elt tree;
                                                      t_opt : 'elt option;
                                                      t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : A__1.t -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration = 'elt MWUPre.M.Raw.enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> A__1.t -> 'a1 -> ('a1 enumeration -> bool) ->
        'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = A__1.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : A__1.t -> A__1.t -> bool

          val lt_dec : A__1.t -> A__1.t -> bool

          val eqb : A__1.t -> A__1.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = A__1.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : A__1.t -> A__1.t -> bool

            val lt_dec : A__1.t -> A__1.t -> bool

            val eqb : A__1.t -> A__1.t -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = A__1.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : A__1.t -> A__1.t -> bool

            val lt_dec : A__1.t -> A__1.t -> bool

            val eqb : A__1.t -> A__1.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = A__1.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : A__1.t -> A__1.t -> bool

              val lt_dec : A__1.t -> A__1.t -> bool

              val eqb : A__1.t -> A__1.t -> bool
             end
           end

          type key = A__1.t

          type 'elt t = (A__1.t * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem = 'elt MWUPre.M.Raw.Proofs.L.coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_mem_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_mem_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list * 
             bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> bool
            -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
            -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> bool
            -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
            -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find = 'elt MWUPre.M.Raw.Proofs.L.coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_find_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_find_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
             * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option ->
            'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option ->
            'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add = 'elt MWUPre.M.Raw.Proofs.L.coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_add_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_add_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list * 
             'elt t * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove = 'elt MWUPre.M.Raw.Proofs.L.coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_remove_2 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
          | R_remove_3 of 'elt t * A__1.t * 'elt * (A__1.t * 'elt) list
             * 'elt t * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> A__1.t
            -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
            -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold = ('elt, 'a) MWUPre.M.Raw.Proofs.L.coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * A__1.t * 'elt * (A__1.t * 'elt) list
             * 'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> 'a2 ->
            ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
            ('a1, 'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> 'a2 ->
            ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
            ('a1, 'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> 'a3 ->
            'a3) -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> 'a3 ->
            'a3) -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          type 'elt coq_R_equal = 'elt MWUPre.M.Raw.Proofs.L.coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * A__1.t * 'elt
             * (A__1.t * 'elt) list * A__1.t * 'elt * (A__1.t * 'elt) list
             * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * A__1.t * 'elt
             * (A__1.t * 'elt) list * A__1.t * 'elt * (A__1.t * 'elt) list
             * A__1.t compare0
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
            A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A__1.t ->
            'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> A__1.t compare0 -> __ -> __ -> 'a2)
            -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
            A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> A__1.t ->
            'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t -> 'a1 ->
            (A__1.t * 'a1) list -> __ -> A__1.t compare0 -> __ -> __ -> 'a2)
            -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
            A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list
            -> __ -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t
            compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ ->
            'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ ->
            A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> A__1.t -> 'a1 -> (A__1.t * 'a1) list
            -> __ -> A__1.t -> 'a1 -> (A__1.t * 'a1) list -> __ -> A__1.t
            compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ ->
            'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem = 'elt MWUPre.M.Raw.Proofs.coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        val coq_R_mem_rec :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        type 'elt coq_R_find = 'elt MWUPre.M.Raw.Proofs.coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal = 'elt MWUPre.M.Raw.Proofs.coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add = 'elt MWUPre.M.Raw.Proofs.coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min = 'elt MWUPre.M.Raw.Proofs.coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
           * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge = 'elt MWUPre.M.Raw.Proofs.coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        type 'elt coq_R_remove = 'elt MWUPre.M.Raw.Proofs.coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat = 'elt MWUPre.M.Raw.Proofs.coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split = 'elt MWUPre.M.Raw.Proofs.coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        val coq_R_split_rec :
          A__1.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        type ('elt, 'x) coq_R_map_option = ('elt, 'x) MWUPre.M.Raw.Proofs.coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
           * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) MWUPre.M.Raw.Proofs.coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = A__1.t

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> nat

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  module MFacts :
   sig
    val eqb : A__1.t -> A__1.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  module MProps :
   sig
    module F :
     sig
      val eqb : A__1.t -> A__1.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

    val of_list : (M.key * 'a1) list -> 'a1 M.t

    val to_list : 'a1 M.t -> (M.key * 'a1) list

    val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3

    val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4

    val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

    val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

    val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

    val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

    val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

    val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

    val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

    val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
   end

  val cGamma : d M.t -> q

  type cstate = MWUPre.cstate = { coq_SCosts : d M.t;
                                  coq_SPrevCosts : d M.t list;
                                  coq_SWeights : d M.t; coq_SEpsilon : 
                                  d; coq_SOutputs : (A__1.t -> q) list;
                                  coq_SChan : A__1.t oracle_chanty;
                                  coq_SOracleSt : A__1.t t1 }

  val coq_SCosts : A__1.t clientOracle -> cstate -> d M.t

  val coq_SPrevCosts : A__1.t clientOracle -> cstate -> d M.t list

  val coq_SWeights : A__1.t clientOracle -> cstate -> d M.t

  val coq_SEpsilon : A__1.t clientOracle -> cstate -> d

  val coq_SOutputs : A__1.t clientOracle -> cstate -> (A__1.t -> q) list

  val coq_SChan : A__1.t clientOracle -> cstate -> A__1.t oracle_chanty

  val coq_SOracleSt : A__1.t clientOracle -> cstate -> A__1.t t1

  val mwu_send :
    A__1.t clientOracle -> d M.t -> A__1.t t1 -> A__1.t
    oracle_chanty * A__1.t t1

  val mwu_recv :
    A__1.t showable -> A__1.t clientOracle -> A__1.t oracle_chanty -> A__1.t
    t1 -> d M.t * A__1.t t1

  val eval_binopc : binop -> d -> d -> d

  val evalc : A__1.t clientOracle -> A__1.t expr -> cstate -> d option

  val update_weights :
    A__1.t clientOracle -> (A__1.t -> A__1.t expr) -> cstate -> d M.t option

  val weights_distr : d M.t -> A__1.t -> q

  val interp :
    A__1.t showable -> A__1.t clientOracle -> A__1.t com -> cstate -> cstate
    option

  val init_map : A__1.t enumerable -> d M.t

  val init_cstate : A__1.t clientOracle -> A__1.t enumerable -> d -> cstate

  val mwu :
    A__1.t showable -> A__1.t enumerable -> A__1.t clientOracle -> d ->
    Coq_N.t -> cstate option
 end

val r_InA_bool : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val r_NoDupA_bool : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

val inRel_bool : ('a1 -> 'a2 -> bool) -> 'a1 -> 'a2 list -> bool

val inRel_list_bool : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val inRel_list_complete_bool :
  ('a1 -> 'a2 -> bool) -> 'a1 enumerable -> 'a2 list -> bool

val num_strategies : nat

val eta : d

val num_rounds : Coq_N.t

val inputChanName : char list

val outputChanName : char list

module Coq_strategies_bound :
 BOUND

module MProps :
 sig
  module M :
   sig
    module N :
     sig
      type t' = Coq_N.t
        (* singleton inductive, whose constructor was mk *)

      val coq_val : t' -> Coq_N.t

      type t = t'

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool

    val t0 : t'

    val enumerate_rec : nat -> t list

    val lt_dec : nat -> nat -> bool

    val enumerate_t : t list

    val enumerable : t enumerable

    val showable : t showable
   end

  module N :
   sig
    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  val coq_val : t' -> Coq_N.t

  type t = t'

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool

  val t0 : t'

  val enumerate_rec : nat -> t list

  val lt_dec : nat -> nat -> bool

  val enumerate_t : t list

  val enumerable : t enumerable

  val showable : t showable

  val enumerate_rec_erased : nat -> Big.big_int list

  val enumerate_rec_erased_nat : nat -> nat list

  val coq_Ordinal_of_t : t -> ordinal

  val val_of_Ordinal : ordinal -> Big.big_int
 end

module M :
 sig
  module N :
   sig
    type t' = Coq_N.t
      (* singleton inductive, whose constructor was mk *)

    val coq_val : t' -> Coq_N.t

    type t = t'

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  type t' = Coq_N.t
    (* singleton inductive, whose constructor was mk *)

  val coq_val : t' -> Coq_N.t

  type t = t'

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool

  val t0 : t'

  val enumerate_rec : nat -> t list

  val lt_dec : nat -> nat -> bool

  val enumerate_t : t list

  val enumerable : t enumerable

  val showable : t showable
 end
module Coq__2 : module type of struct include M end

type oracleState = (M.t * d) list * unit

val bogus_result : oracleState

type inChan = in_channel

type outChan = out_channel

val open_in : char list -> inChan

val open_out : char list -> outChan

val inChan_recv : inChan -> (M.t * d) list

val outChan_send : outChan -> (M.t * d) list -> unit

type chan = inChan * outChan

val openChan : char list -> char list -> chan

val defaultChan : chan

val prerecv_recv : chan -> oracleState

val send : oracleState -> (M.t * d) list -> chan * oracleState

val mt_eqb : M.t -> M.t -> bool

val uniqR_bool : (M.t * d) -> (M.t * d) -> bool

val prerecv_chk_nodup : (M.t * d) list -> bool

val in_range_bool : M.t -> (M.t * d) -> bool

val prerecv_chk_complete_in_range_bool : (M.t * d) list -> bool

val prerecv : oracleState -> chan -> bool * oracleState

val recv : oracleState -> chan -> (M.t * d) list * oracleState

val presend : oracleState -> (M.t * d) list -> bool

val myOracle : M.t clientOracle

module MWUextract :
 sig
  module A :
   sig
    type t = M.t

    val t0 : t

    val enumerable : t enumerable

    val showable : t showable

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module MWUPre :
   sig
    module A' :
     sig
      type t = M.t

      val compare : M.t -> M.t -> M.t compare0

      val eq_dec : M.t -> M.t -> bool
     end

    module M :
     sig
      module E :
       sig
        type t = M.t

        val compare : M.t -> M.t -> M.t compare0

        val eq_dec : M.t -> M.t -> bool
       end

      module Raw :
       sig
        type key = M.t

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : M.t -> 'a1 tree -> bool

        val find : M.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : M.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : M.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> M.t -> 'a1 -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = M.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : M.t -> M.t -> bool

            val lt_dec : M.t -> M.t -> bool

            val eqb : M.t -> M.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = M.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : M.t -> M.t -> bool

              val lt_dec : M.t -> M.t -> bool

              val eqb : M.t -> M.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = M.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : M.t -> M.t -> bool

              val lt_dec : M.t -> M.t -> bool

              val eqb : M.t -> M.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = M.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : M.t -> M.t -> bool

                val lt_dec : M.t -> M.t -> bool

                val eqb : M.t -> M.t -> bool
               end
             end

            type key = M.t

            type 'elt t = (M.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_mem_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_mem_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * bool
               * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
              'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
              'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_find_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_find_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list
               * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_add_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_add_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * 'elt t
               * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_remove_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
            | R_remove_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * 
               'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
              'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * M.t * 'elt * (M.t * 'elt) list * 
               'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a3 ->
              'a3) -> 'a1 t -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a3 ->
              'a3) -> 'a1 t -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * M.t * 'elt * (M.t * 'elt) list
               * M.t * 'elt * (M.t * 'elt) list * bool * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * M.t * 'elt * (M.t * 'elt) list
               * M.t * 'elt * (M.t * 'elt) list * M.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> M.t -> 'a1 -> (M.t * 'a1) list -> __
              -> M.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
              -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool ->
              'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> M.t -> 'a1 ->
              (M.t * 'a1) list -> __ -> M.t -> 'a1 -> (M.t * 'a1) list -> __
              -> M.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
              -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool ->
              'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> M.t compare0 -> __ -> __ ->
              'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
              'a2) -> 'a1 t -> 'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t
              -> 'a1 -> (M.t * 'a1) list -> __ -> M.t compare0 -> __ -> __ ->
              'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
              'a2) -> 'a1 t -> 'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
            -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
            -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key
            -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
            'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
            -> 'a2

          val coq_R_split_rec :
            M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
            'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
            -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = M.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module MFacts :
     sig
      val eqb : Coq__2.t -> Coq__2.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    module MProps :
     sig
      module F :
       sig
        val eqb : Coq__2.t -> Coq__2.t -> bool

        val coq_In_dec : 'a1 M.t -> M.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (M.key * 'a1) list -> 'a1 M.t

      val to_list : 'a1 M.t -> (M.key * 'a1) list

      val fold_rec :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
        'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __
        -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
        -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
        -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 ->
        __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ ->
        'a3 -> 'a3) -> 'a1 M.t -> 'a3

      val fold_rel :
        (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4
        -> 'a4) -> 'a4

      val map_induction :
        ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1
        -> __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

      val map_induction_bis :
        ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 ->
        'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

      val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

      val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

      val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

      val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

      val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

      val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

      val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

      val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

      val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

      val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

      val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

      val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

      val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

      val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

      val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
     end

    val cGamma : d M.t -> q

    type cstate = { coq_SCosts : d M.t; coq_SPrevCosts : d M.t list;
                    coq_SWeights : d M.t; coq_SEpsilon : d;
                    coq_SOutputs : (Coq__2.t -> q) list;
                    coq_SChan : Coq__2.t oracle_chanty;
                    coq_SOracleSt : Coq__2.t t1 }

    val coq_SCosts : Coq__2.t clientOracle -> cstate -> d M.t

    val coq_SPrevCosts : Coq__2.t clientOracle -> cstate -> d M.t list

    val coq_SWeights : Coq__2.t clientOracle -> cstate -> d M.t

    val coq_SEpsilon : Coq__2.t clientOracle -> cstate -> d

    val coq_SOutputs : Coq__2.t clientOracle -> cstate -> (Coq__2.t -> q) list

    val coq_SChan : Coq__2.t clientOracle -> cstate -> Coq__2.t oracle_chanty

    val coq_SOracleSt : Coq__2.t clientOracle -> cstate -> Coq__2.t t1

    val mwu_send :
      Coq__2.t clientOracle -> d M.t -> Coq__2.t t1 -> Coq__2.t
      oracle_chanty * Coq__2.t t1

    val mwu_recv :
      Coq__2.t showable -> Coq__2.t clientOracle -> Coq__2.t oracle_chanty ->
      Coq__2.t t1 -> d M.t * Coq__2.t t1

    val eval_binopc : binop -> d -> d -> d

    val evalc : Coq__2.t clientOracle -> Coq__2.t expr -> cstate -> d option

    val update_weights :
      Coq__2.t clientOracle -> (Coq__2.t -> Coq__2.t expr) -> cstate -> d M.t
      option

    val weights_distr : d M.t -> Coq__2.t -> q

    val interp :
      Coq__2.t showable -> Coq__2.t clientOracle -> Coq__2.t com -> cstate ->
      cstate option

    val init_map : Coq__2.t enumerable -> d M.t

    val init_cstate :
      Coq__2.t clientOracle -> Coq__2.t enumerable -> d -> cstate

    val mwu :
      Coq__2.t showable -> Coq__2.t enumerable -> Coq__2.t clientOracle -> d
      -> Coq_N.t -> cstate option
   end

  module A' :
   sig
    type t = M.t

    val compare : M.t -> M.t -> M.t compare0

    val eq_dec : M.t -> M.t -> bool
   end

  module M :
   sig
    module E :
     sig
      type t = M.t

      val compare : M.t -> M.t -> M.t compare0

      val eq_dec : M.t -> M.t -> bool
     end

    module Raw :
     sig
      type key = M.t

      type 'elt tree = 'elt MWUPre.M.Raw.tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Z_as_Int.t

      val cardinal : 'a1 tree -> nat

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : M.t -> 'a1 tree -> bool

      val find : M.t -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : M.t -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = 'elt MWUPre.M.Raw.triple = { t_left : 'elt tree;
                                                      t_opt : 'elt option;
                                                      t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : M.t -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration = 'elt MWUPre.M.Raw.enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> M.t -> 'a1 -> ('a1 enumeration -> bool) ->
        'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = M.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : M.t -> M.t -> bool

          val lt_dec : M.t -> M.t -> bool

          val eqb : M.t -> M.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = M.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : M.t -> M.t -> bool

            val lt_dec : M.t -> M.t -> bool

            val eqb : M.t -> M.t -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = M.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : M.t -> M.t -> bool

            val lt_dec : M.t -> M.t -> bool

            val eqb : M.t -> M.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = M.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : M.t -> M.t -> bool

              val lt_dec : M.t -> M.t -> bool

              val eqb : M.t -> M.t -> bool
             end
           end

          type key = M.t

          type 'elt t = (M.t * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem = 'elt MWUPre.M.Raw.Proofs.L.coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_mem_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_mem_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find = 'elt MWUPre.M.Raw.Proofs.L.coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_find_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_find_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add = 'elt MWUPre.M.Raw.Proofs.L.coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_add_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_add_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove = 'elt MWUPre.M.Raw.Proofs.L.coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_remove_2 of 'elt t * M.t * 'elt * (M.t * 'elt) list
          | R_remove_3 of 'elt t * M.t * 'elt * (M.t * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            M.t -> 'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold = ('elt, 'a) MWUPre.M.Raw.Proofs.L.coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * M.t * 'elt * (M.t * 'elt) list * 
             'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          type 'elt coq_R_equal = 'elt MWUPre.M.Raw.Proofs.L.coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * M.t * 'elt * (M.t * 'elt) list
             * M.t * 'elt * (M.t * 'elt) list * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * M.t * 'elt * (M.t * 'elt) list
             * M.t * 'elt * (M.t * 'elt) list * M.t compare0
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> M.t -> 'a1 -> (M.t * 'a1) list -> __ ->
            M.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
            __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
            coq_R_equal -> 'a2

          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> M.t -> 'a1 ->
            (M.t * 'a1) list -> __ -> M.t -> 'a1 -> (M.t * 'a1) list -> __ ->
            M.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
            __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
            coq_R_equal -> 'a2

          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1
            t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t -> 'a1
            -> (M.t * 'a1) list -> __ -> M.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t ->
            'a1 -> (M.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1
            t -> 'a1 t -> M.t -> 'a1 -> (M.t * 'a1) list -> __ -> M.t -> 'a1
            -> (M.t * 'a1) list -> __ -> M.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem = 'elt MWUPre.M.Raw.Proofs.coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        val coq_R_mem_rec :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
          coq_R_mem -> 'a2

        type 'elt coq_R_find = 'elt MWUPre.M.Raw.Proofs.coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal = 'elt MWUPre.M.Raw.Proofs.coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add = 'elt MWUPre.M.Raw.Proofs.coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min = 'elt MWUPre.M.Raw.Proofs.coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
           * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge = 'elt MWUPre.M.Raw.Proofs.coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        type 'elt coq_R_remove = 'elt MWUPre.M.Raw.Proofs.coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat = 'elt MWUPre.M.Raw.Proofs.coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split = 'elt MWUPre.M.Raw.Proofs.coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        val coq_R_split_rec :
          M.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2

        type ('elt, 'x) coq_R_map_option = ('elt, 'x) MWUPre.M.Raw.Proofs.coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
           * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) MWUPre.M.Raw.Proofs.coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = M.t

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> nat

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  module MFacts :
   sig
    val eqb : Coq__2.t -> Coq__2.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  module MProps :
   sig
    module F :
     sig
      val eqb : Coq__2.t -> Coq__2.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

    val of_list : (M.key * 'a1) list -> 'a1 M.t

    val to_list : 'a1 M.t -> (M.key * 'a1) list

    val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3

    val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4

    val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

    val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

    val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key * 'a1)

    val cardinal_inv_2b : 'a1 M.t -> (M.key * 'a1)

    val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

    val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

    val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

    val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t

    val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t * 'a1 M.t
   end

  val cGamma : d M.t -> q

  type cstate = MWUPre.cstate = { coq_SCosts : d M.t;
                                  coq_SPrevCosts : d M.t list;
                                  coq_SWeights : d M.t; coq_SEpsilon : 
                                  d; coq_SOutputs : (Coq__2.t -> q) list;
                                  coq_SChan : Coq__2.t oracle_chanty;
                                  coq_SOracleSt : Coq__2.t t1 }

  val coq_SCosts : Coq__2.t clientOracle -> cstate -> d M.t

  val coq_SPrevCosts : Coq__2.t clientOracle -> cstate -> d M.t list

  val coq_SWeights : Coq__2.t clientOracle -> cstate -> d M.t

  val coq_SEpsilon : Coq__2.t clientOracle -> cstate -> d

  val coq_SOutputs : Coq__2.t clientOracle -> cstate -> (Coq__2.t -> q) list

  val coq_SChan : Coq__2.t clientOracle -> cstate -> Coq__2.t oracle_chanty

  val coq_SOracleSt : Coq__2.t clientOracle -> cstate -> Coq__2.t t1

  val mwu_send :
    Coq__2.t clientOracle -> d M.t -> Coq__2.t t1 -> Coq__2.t
    oracle_chanty * Coq__2.t t1

  val mwu_recv :
    Coq__2.t showable -> Coq__2.t clientOracle -> Coq__2.t oracle_chanty ->
    Coq__2.t t1 -> d M.t * Coq__2.t t1

  val eval_binopc : binop -> d -> d -> d

  val evalc : Coq__2.t clientOracle -> Coq__2.t expr -> cstate -> d option

  val update_weights :
    Coq__2.t clientOracle -> (Coq__2.t -> Coq__2.t expr) -> cstate -> d M.t
    option

  val weights_distr : d M.t -> Coq__2.t -> q

  val interp :
    Coq__2.t showable -> Coq__2.t clientOracle -> Coq__2.t com -> cstate ->
    cstate option

  val init_map : Coq__2.t enumerable -> d M.t

  val init_cstate :
    Coq__2.t clientOracle -> Coq__2.t enumerable -> d -> cstate

  val mwu :
    Coq__2.t showable -> Coq__2.t enumerable -> Coq__2.t clientOracle -> d ->
    Coq_N.t -> cstate option
 end

val extractedMW : MWUextract.cstate option
